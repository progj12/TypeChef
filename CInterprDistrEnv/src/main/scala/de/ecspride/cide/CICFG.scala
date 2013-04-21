package de.ecspride.cide

import de.fosd.typechef.conditional.{Conditional, Opt}
import de.fosd.typechef.crewrite.{ASTNavigation, ASTEnv, InterCFG}
import de.fosd.typechef.featureexpr.FeatureModel
import de.fosd.typechef.parser.c._
import de.fosd.typechef.parser.c.FunctionCall
import de.fosd.typechef.parser.c.FunctionDef
import de.fosd.typechef.parser.c.PostfixExpr
import de.fosd.typechef.typesystem.CDeclUse
import scala.collection.JavaConversions._
import scala.collection.immutable.TreeSet
import heros.InterproceduralCFG

/* CDeclUse not necessary, when InterCFG is used */
class CICFG(val tUnit: AST, val env: ASTEnv, val fm: FeatureModel) extends InterCFG with InterproceduralCFG[AST,FunctionDef] with ASTNavigation /*with CDeclUse*/ {
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
    System.out.println("Get method of: " + PrettyPrinter.print(p1))
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
    System.out.println("Get Callee of: " + PrettyPrinter.print(p1))

    // */

    if (isCallStmt(p1)) {

      var c = getCallTarget(p1.asInstanceOf[FunctionCall])
      // /*
      for(fd <- c){
        System.out.println("Callee: " + PrettyPrinter.print(fd.asInstanceOf[AST]))
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
    System.out.println("Get Callers of: " + PrettyPrinter.print(p1))
    // */


    val callers = pred(p1, fm , env)
    var callingNodes = Set.empty[AST]

    callingNodes ++ callers

    // /*
    for (c <- callingNodes){
      System.out.println("Caller: " + PrettyPrinter.print(c))
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
    System.out.println("Calls from within: " + PrettyPrinter.print(p1))
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
      System.out.println("Calls: " + PrettyPrinter.print(c))
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
    System.out.println("Return Sites of Call: " + PrettyPrinter.print(p1))
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
      System.out.println("Return sites: " + PrettyPrinter.print(c))
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
      System.out.println(PrettyPrinter.print(ncsn))
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
         System.out.println("Start points of: " + PrettyPrinter.print(func))
         for(sp <- startPoints){
           System.out.println(" " + PrettyPrinter.print(sp))
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
    System.out.println("Get Call Target of: " + PrettyPrinter.print(stmt))
    // */

    var fDefs = List.empty[FunctionDef]

    val target = getSuccsOf(stmt)

    // only FunctionDefs are relevant
    for(id <- target){
      fDefs.::(findPriorASTElem(id, env)[FunctionDef])
    }

    if (!fDefs.isEmpty) Option(fDefs)
    else None


  }

  // provide a lookup mechanism for function defs (from the type system or selfimplemented)
  def lookupFunctionDef(name: String): Conditional[Option[ExternalDef]] = null
}
