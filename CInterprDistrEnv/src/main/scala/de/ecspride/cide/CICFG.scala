package de.ecspride.cide

import de.fosd.typechef.conditional.{Conditional, Opt}
import de.fosd.typechef.crewrite.{ASTNavigation, ASTEnv, ConditionalControlFlow}
import de.fosd.typechef.featureexpr.FeatureModel
import de.fosd.typechef.parser.c._
import de.fosd.typechef.parser.c.FunctionCall
import de.fosd.typechef.parser.c.FunctionDef
import de.fosd.typechef.parser.c.PostfixExpr
import de.fosd.typechef.typesystem.CDeclUse
import scala.collection.JavaConversions._
import scala.collection.immutable.TreeSet
import heros.InterproceduralCFG

class CICFG(val tUnit: AST, val env: ASTEnv, val fm: FeatureModel) extends ConditionalControlFlow with InterproceduralCFG[AST,FunctionDef] with ASTNavigation with CDeclUse {
              /* (tUnit: AST, env: ASTEnv, fm: FeatureModel) */
 /* var tUnit: AST = null
  var env: ASTEnv = null
  var fm: FeatureModel = null

  CICFG(tu: AST, en: ASTEnv, fmodel: FeatureModel){
    this.tUnit = tu
    this.env = en
    this.fm = fmodel
  }
   */

  /**
   * Get the Method containing the Node
   * @param p1  current Node
   * @return    FunctionDef of Method containing n1
   */
  def getMethodOf(p1: AST) : FunctionDef = {

    // /*
    System.out.println("Get method of: " + printId(p1))
    // */

    val p = pred(p1, fm, env)
    p match{
      case Some(x: FunctionDef) => x
      case Some(y: AST) => getMethodOf(y)
      case _ => null
    }
  }


  /**
   * Returns all callees of a call
   * @param p1  current node
   * @return    Set of FunctionDef called by n1
   *
   *
   */
  def getCalleesOfCallAt(p1: AST) : Set[FunctionDef] =   {

    // /*
    System.out.println("Get Callee of: " + printId(p1))

    // */

    if (isCallStmt(p1)) {

      var c = getCallTarget(p1.asInstanceOf[FunctionCall])
      // /*
      for(fd <- c){
        System.out.println("Callee: " + printId(fd.asInstanceOf[AST]))
      }
      // */


      var callee = Set.empty[FunctionDef]
      callee.++(c)
      callee
    } else {
      // /*
      System.out.println("No Callee found")
      // */
      Set.empty[FunctionDef]
    }
  }

  /**
   * Returns all caller statements/nodes of a given method.
   * @param p1 called Method (FunctionDef)
   * @return    Set of nodes calling f1
   */
  def getCallersOf(p1: FunctionDef) = {
    // /*
    System.out.println("Get Callers of: " + printId(p1))
    // */


    val callers = pred(p1, fm , env)
    var callingNodes = Set.empty[AST]

    callingNodes ++ callers

    // /*
    for (c <- callingNodes){
      System.out.println("Caller: " + printId(c))
    }
    // */

    setAsJavaSet(callingNodes)
  }

  /**
   * Return all call sites from within a method
   * @param p1 current method
   * @return   call sites within f1
   */
  def getCallsFromWithin(p1: FunctionDef) = {
    var todo = succ(p1, fm, env)
    var done = Set.empty[AST]
    var calls = Set.empty[AST]

    // /*
    System.out.println("Calls from within: " + printId(p1))
    // */
    // BFS
    for(current <- todo){
      // process only if it's not done
      if(!done.contains(Some(current))){
        current match{
          // Dont follow Returns
          case Some(z: ReturnStatement) => done+(z)
            // Dont follow Calls, but collect them
          case Some(x: FunctionCall) => {
            calls+(x)
            done+(x)
          }
          // Follow Statements
          case Some(y: AST) => {
            todo.++(succ(y, fm, env))
            done+(y)
          }
          case _ =>
        }
      }
      // remove current node from workinglist (usage of --Operator is deprecated)
      todo = todo.filterNot(_ == current);
    }

    // /*
    for (c <- calls){
      System.out.println("Calls: " + printId(c))
    }
    // */

    setAsJavaSet(calls)
  }


  /**
   *  Returns all statements to which a call could return.
   * In the RHS paper, for every call there is just one return site.
   * We, however, use as return site the successor statements, of which
   * there can be many in case of exceptional flow.
   * @param p1  calling(?) node
   * @return    List of return sites of the calling node
   */
  def getReturnSitesOfCallAt(p1: AST) = {
    val successors = succ(p1, fm, env)

    // /*
    System.out.println("Return Sites of Call: " + printId(p1))
    // */


    var rsoc = List.empty[AST]

    for(s <- successors){
      s match{
        case Some(x: AST) => {
          if (x.isInstanceOf[ReturnStatement]) {
            rsoc ++ (succ(x, fm, env))
          }
          else {
            rsoc ++ (getReturnSitesOfCallAt(x))
          }
        }
        case _ =>
      }

    }

    rsoc.distinct

    // /*
    for (c <- rsoc){
      System.out.println("Return sites: " + printId(c))
    }
    // */

    // remove all duplicates and return the list of returnsites
    seqAsJavaList(rsoc)
  }

  /**
   * Returns the set of all nodes that are neither call nor start nodes.
   *
   * Traverse all Elements of the AST and collect all Statements (exclude {isCallStmt || isStartPoint})
   * @return  Set of nodes
   */
  def allNonCallStartNodes() = {
    val callStartNodes = Set.empty[AST]
    val nonCallStartNodes = Set.empty[AST]

        // filter recursively for FunctionCalls and FunctionDefs
    callStartNodes++ filterAllASTElems[FunctionCall] (tUnit)  // Call
    callStartNodes++ filterAllASTElems[FunctionDef](tUnit)   // Start
    nonCallStartNodes++ filterAllASTElems[AST](tUnit) // getAllNodes

    nonCallStartNodes.--(callStartNodes) // remove CallStartNodes

    // /*
     System.out.println("Non Call/Start Nodes: ")
    for (ncsn <- nonCallStartNodes){
      System.out.println(printId(ncsn))
    }
    // */

    setAsJavaSet(nonCallStartNodes)
  }

  def getSuccsOf(stmt: AST) = {
    val succs = succ(stmt, fm, env)
    val results = List.empty[AST]

    for(succ <- succs){
        succ match{
          case Some(x: AST) => results ::: List(x) // why not <List> :: x ?  This would decrease complexity from O(n) to O(1)!
          case _ =>
        }
    }
    seqAsJavaList(results)
  }


  /**
   * Return the Startpoints of a Definition of a Function. (Successor of Functiondefinition Node)
   *
   * @param func
   * @return
   */
  def getStartPointsOf(func: FunctionDef): Set[AST] = {
    val succs = succ(func, fm, env)
    var startPoints = Set.empty[AST]
    startPoints ++ succs

    // /*
         System.out.println("Start points of: " + printId(func))
         for(sp <- startPoints){
           System.out.println(" " + printId(sp))
         }
    // */
    startPoints
  }

  def isCallStmt(stmt: AST) =
    stmt match {
      case PostfixExpr(_, FunctionCall(_)) => true
      case _ => false
    }


  def isExitStmt(stmt: AST) =
    stmt match {
      case _: ReturnStatement => true
      case _ => false
    }



  def isStartPoint(stmt: AST) =
    pred(stmt, fm, env) match {
      case _: FunctionDef => true
      case _ => false
    }


  def isFallThroughSuccessor(stmt: AST, suc: AST) =
    succ(stmt, fm, env).size == 1 && succ(stmt, fm, env).head == suc

  def isBranchTarget(stmt: AST, suc: AST) = succ(stmt, fm, env).exists(x => x == suc)



  def getCallTarget(stmt: FunctionCall): Option[List[FunctionDef]] =   {

    // /*
    System.out.println("Get Call Target of: " + printId(stmt))
    // */

    // if(!stmt.isInstanceOf[FunctionCall]) return null

    val getDefIds = getUseDeclMap.get(stmt.asInstanceOf[PostfixExpr].p)

    var fDefs = List.empty[FunctionDef]

    for(id <- getDefIds){
      fDefs.::(findPriorASTElem(id, env)[FunctionDef])
    }

    if (!fDefs.isEmpty) Option(fDefs)
    else None
  }

  def printId(stmt: AST): String = PrettyPrinter.print(stmt)


 /*

  def printId(stmt: AST): String = {
    def getListString(l: List[Opt[AST]], s: String): String = {
      var res = ""

      for (a <- l){
        res = res + s + " " + printId(a.entry)
      }
      res
    }

    def getListString(l: List[Opt[Expr]], s: String): String = {
      var res = ""

      for (a <- l){
        res = res + s + " " + printId(a.entry)
      }
      res
    }

    def commaSep(l: List[Opt[AST]]) = getListString(l, ",")
    def spaceSep(l: List[Opt[AST]]) = getListString(l, " ")
    def opt(o: Option[AST]): String = if (o.isDefined) printId(o.get) else " "
    def optCond(o: Option[Conditional[AST]]): String = if (o.isDefined) printId(o.get) else " "


    stmt match {
      case TranslationUnit(ext) => "TranslationUnit"
      case Id(name) => name
      case Constant(v) => v
      case SimplePostfixSuffix(t) => t
      case PointerPostfixSuffix(kind, id) => kind + " " + id
      case FunctionCall(params) => stmt.asInstanceOf[PostfixExpr].p +  "(" + params + ")"
      case ArrayAccess(e) => "[" + e + "]"
      case PostfixExpr(p, s) => p + printId(s)
      case UnaryExpr(p, s) => p + s
      case SizeOfExprT(typeName) => "sizeof(" + typeName + ")"
      case SizeOfExprU(e) => "sizeof(" + e + ")"
      case CastExpr(typeName, expr) => "((" + typeName + ") " + expr + ")"

      case PointerDerefExpr(castExpr) => "(* " + castExpr + ")"
      case PointerCreationExpr(castExpr) => "(& " + castExpr + ")"

      case UnaryOpExpr(kind, castExpr) => "(" + kind + " " + castExpr ")"
      case NAryExpr(e, others) => "(" + e + others + ")"
      case NArySubExpr(op: String, e: Expr) => op + " " + e
      case ConditionalExpr(condition: Expr, thenExpr, elseExpr: Expr) => "(" + condition + " ? " + opt(thenExpr) + " : " + elseExpr + ")"
      case AssignExpr(target: Expr, operation: String, source: Expr) => "(" + target + " " + operation  + " " +  source + ")"
      case ExprList(exprs) => getListString(exprs, ",")

      case CompoundStatement(innerStatements) =>
        "{ " + getListString(innerStatements, "; ")
      case EmptyStatement() => ";"
      case ExprStatement(expr: Expr) => expr + ";"
      case WhileStatement(expr: Expr, s) =>  "while (" + expr + ")" + s
      case DoStatement(expr: Expr, s) => "do" + s + "\n while (" + expr + ")"
      case ForStatement(expr1, expr2, expr3, s) =>
        "for (" + opt(expr1) + ";\n" + opt(expr2) + ";\n" + opt(expr3) + ")\n" + s
      case GotoStatement(target) => "goto\n" + target + ";"
      case ContinueStatement() => "continue;"
      case BreakStatement() => "break;"
      case ReturnStatement(None) => "return;"
      case ReturnStatement(Some(e)) => "\n" + e + ";"
      case LabelStatement(id: Id, _) => id + ":"
      case CaseStatement(c: Expr) => "case \n" + c + ":"
      case DefaultStatement() => "default:"
      case IfStatement(condition, thenBranch, elifs, elseBranch) =>
        "if (" + condition + ") \n" + thenBranch + getListString(elifs, ",") + getListString(elseBranch.get, "\n,")
      case ElifStatement(condition, thenBranch) => "\n else if (" + condition + ")\n" + thenBranch
      case SwitchStatement(expr, s) => "switch (" + expr + ")\n" + s
      case DeclarationStatement(decl: Declaration) => decl
      case NestedFunctionDef(isAuto, specifiers, declarator, parameters, stmt) =>
        (if (isAuto) "auto\n" + "" else "") + getListString(specifiers, "\n;") + "\n" + declarator + "\n" + getListString(parameters, "\n;") + "\n;" + stmt
      case LocalLabelDeclaration(ids) => "__label__\n" + getListString(ids, ",\n") + ";"
      case OtherPrimitiveTypeSpecifier(typeName: String) => typeName
      case VoidSpecifier() => "void"
      case ShortSpecifier() => "short"
      case IntSpecifier() => "int"
      case FloatSpecifier() => "float"
      case LongSpecifier() => "long"
      case CharSpecifier() => "char"
      case DoubleSpecifier() => "double"

      case TypedefSpecifier() => "typedef"
      case TypeDefTypeSpecifier(name: Id) => name
      case SignedSpecifier() => "signed"
      case UnsignedSpecifier() => "unsigned"

      case InlineSpecifier() => "inline"
      case AutoSpecifier() => "auto"
      case RegisterSpecifier() => "register"
      case VolatileSpecifier() => "volatile"
      case ExternSpecifier() => "extern"
      case ConstSpecifier() => "const"
      case RestrictSpecifier() => "restrict"
      case StaticSpecifier() => "static"

      case AtomicAttribute(n: String) => n
      case AttributeSequence(attributes) => getListString(attributes, "\n")
      case CompoundAttribute(inner) => "(" + getListString(inner, ",\n") + ")"

      case Declaration(declSpecs, init) =>
        getListString(declSpecs, "\n") + "\n" + commaSep(init) + ";"

      case InitDeclaratorI(declarator, _, Some(i)) => declarator + "\n = \n" + i
      case InitDeclaratorI(declarator, _, None) => declarator.getId.name
      case InitDeclaratorE(declarator, _, e: Expr) => declarator + ":\n" + e

      case AtomicNamedDeclarator(pointers, id, extensions) =>
        getListString(pointers, ",") + id + getListString(extensions, ",")
      case NestedNamedDeclarator(pointers, nestedDecl, extensions) =>
        getListString(pointers, ",") + "(" + nestedDecl + ")" + getListString(extensions, ",")
      case AtomicAbstractDeclarator(pointers, extensions) =>
        getListString(pointers, ",") + getListString(extensions, ",")
      case NestedAbstractDeclarator(pointers, nestedDecl, extensions) =>
        getListString(pointers, ",") + "(" + nestedDecl + ")" + getListString(extensions, ",")

      case DeclIdentifierList(idList) => "(" + commaSep(idList) + ")"
      case DeclParameterDeclList(parameterDecls) =>  "(" + commaSep(parameterDecls) + ")"
      case DeclArrayAccess(expr) => "[" + opt(expr) + "]"
      case Initializer(initializerElementLabel, expr: Expr) => opt(initializerElementLabel) + "\n" + expr
      case Pointer(specifier) => "*" + spaceSep(specifier)
      case PlainParameterDeclaration(specifiers) => spaceSep(specifiers)
      case ParameterDeclarationD(specifiers, decl) => spaceSep(specifiers) +" "+ decl
      case ParameterDeclarationAD(specifiers, decl) => spaceSep(specifiers) +" " + decl
      case VarArgs() => "..."
      case EnumSpecifier(id, Some(enums)) => "enum\n" + opt(id) +"\n{"+ getListString(enums, ",") +  "}"
      case EnumSpecifier(Some(id), None) => "enum\n" + id
      case Enumerator(id, Some(init)) => id + "\n=\n" + init
      case Enumerator(id, None) => id
      case StructOrUnionSpecifier(isUnion, id, enumerators) =>
        (if (isUnion) "union" else "struct") + "\n" + opt(id) + "\n" +  (if (enumerators.isDefined) "{" + getListString(enumerators.get, ",") else "")
      case StructDeclaration(qualifierList, declaratorList) => spaceSep(qualifierList) + "\n" +  commaSep(declaratorList) + ";"
      case StructDeclarator(decl, initializer, _) => decl + optExt(initializer, ":\n" )
      case StructInitializer(expr, _) => ":" + "\n" +  expr
      case AsmExpr(isVolatile, expr) => "asm" + "\n" +  (if (isVolatile) "volatile " else "") + "{" + expr + "}" + ";"
      case FunctionDef(specifiers, declarator, oldStyleParameters, stmt) =>
        spaceSep(specifiers) + "\n" +  declarator + "\n" + spaceSep(oldStyleParameters) + "\n" +  stmt
      case EmptyExternalDef() => ";"
      case TypelessDeclaration(declList) => commaSep(declList) + ";"
      case TypeName(specifiers, decl) => spaceSep(specifiers) + "\n" +  opt(decl)

      case GnuAttributeSpecifier(attributeList) => "__attribute__((" + commaSep(attributeList) + "))"
      case AsmAttributeSpecifier(stringConst) => getListString(stringConst.name, ",")
      case LcurlyInitializer(inits) => "{" + commaSep(inits) + "}"
      case AlignOfExprT(typeName: TypeName) => "__alignof__(" + typeName + ")"
      case AlignOfExprU(expr: Expr) => "__alignof__" + "\n" +  expr
      case GnuAsmExpr(isVolatile: Boolean, isAuto, expr: StringLit, stuff: Any) => "asm"
      case RangeExpr(from: Expr, to: Expr) => from + "\n" +  "..." + "\n" +  to
      case TypeOfSpecifierT(typeName: TypeName) => "typeof(" + typeName + ")"
      case TypeOfSpecifierU(e: Expr) => "typeof(" + e + ")"
      case InitializerArrayDesignator(expr: Expr) => "[" + expr + "]"
      case InitializerDesignatorD(id: Id) => "." + id
      case InitializerDesignatorC(id: Id) => id + ":"
      case InitializerAssigment(desgs) => spaceSep(desgs) + "\n" +  "="
      case BuiltinOffsetof(typeName: TypeName, offsetofMemberDesignator) => "__builtin_offsetof(" + typeName + "," + "\n" +  spaceSep(offsetofMemberDesignator) + ")"
      case OffsetofMemberDesignatorID(id: Id) => "." + id
      case OffsetofMemberDesignatorExpr(expr: Expr) => "[" + expr + "]"
      case BuiltinTypesCompatible(typeName1: TypeName, typeName2: TypeName) => "__builtin_types_compatible_p(" + typeName1 + "," + "\n" +  typeName2 + ")"
      case BuiltinVaArgs(expr: Expr, typeName: TypeName) => "__builtin_va_arg(" + expr + "," + "\n" +  typeName + ")"
      case CompoundStatementExpr(compoundStatement: CompoundStatement) => "(" + compoundStatement + ")"
      case Pragma(command: StringLit) => "_Pragma(" + command + ")"

      case e => assert(false, "match not exhaustive: " + e); ""
    }
  }

  */

}
