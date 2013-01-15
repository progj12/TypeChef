import de.fosd.typechef.crewrite.{ASTNavigation, ASTEnv, ConditionalControlFlow}
import de.fosd.typechef.featureexpr.FeatureModel
import de.fosd.typechef.parser.c._
import de.fosd.typechef.parser.c.FunctionCall
import de.fosd.typechef.parser.c.FunctionDef
import de.fosd.typechef.parser.c.PostfixExpr
import scala.collection.JavaConversions._
import scala.collection.immutable.TreeSet
import heros.InterproceduralCFG

class CICFG(tUnit: AST, env: ASTEnv, fm: FeatureModel) extends ConditionalControlFlow with InterproceduralCFG[AST,FunctionDef] with ASTNavigation {




  /**
   * Method containing the a Node
   * @param p1  current Node
   * @return    FunctionDef of Method containing n1
   *
   * question: possible to have more than one pred?
   */
  def getMethodOf(p1: AST) : FunctionDef = {
    val p = pred(p1, fm, env);
    p match{
      case Some(x: FunctionDef) => x;
      case Some(y: AST) => getMethodOf(y);
      case _ => null; // question:   possible? (root node?)
    }
  }
  /**
   * Returns all callees of a call
   * @param p1  current node
   * @return    Set of FunctionDef called by n1
   *
   *            question: more than one Callee if virtual call or function pointer - tbd! (Points-to-?)
   *
   */
  def getCalleesOfCallAt(p1: AST) : Set[FunctionDef] =   {
    if (isCallStmt(p1)) {
      return getCalleeOfP1(p1)     // question more efficient way?
    } else {
      return Set.empty[FunctionDef]
    }
  }

  /**
   * returns all Succs of the AST-Element for {succ(p) | für alle i: succ(p)_i = FunctionDef}
   * @param p1
   * @return
   */
  def getCalleeOfP1(p1: AST) : Set[FunctionDef] =  {
    val succs = succ(p1, fm, env)
    var callee = Set.empty[FunctionDef]
    for(succ <- succs){
      succ match{
        case Some(x: FunctionDef) => callee.+(x)
        case _ =>
      }
    }
    callee

  }
  /**
   * Returns all caller statements/nodes of a given method.
   * @param p1 called Method (FunctionDef)
   * @return    Set of nodes calling f1
   */
  def getCallersOf(p1: FunctionDef): Set[AST] = {
    val callers = pred(p1, fm , env)  // question pred ok?
    var callingNodes = Set.empty[AST]

    callingNodes ++ callers

    callingNodes
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

    var rsoc = List.empty[AST]

    for(s <- successors){
      s match{
        case Some(x: AST) => {
          if (x.isInstanceOf[ReturnStatement])
            rsoc++(succ(x, fm, env)) // if s is a return node -> ALL successors of s are return sites of s and p1
          else
            rsoc++(getReturnSitesOfCallAt(x))
        }
        case _ =>
      }

    }
    // remove all duplicates and return the list of returnsites
    seqAsJavaList(rsoc.distinct)
  }

  /**
   * Returns the set of all nodes that are neither call nor start nodes.
   *
   * Traverse all Elements of the AST and collect all Statements (exclude {isCallStmt || isStartPoint})
   * @return  Set of nodes
   */
  def allNonCallStartNodes() = {
    var callStartNodes = Set.empty[AST]
    var nonCallStartNodes = Set.empty[AST]
    var todo = Set.apply(tUnit)


    // filter recursively for FunctionCalls and FunctionDefs
    callStartNodes++ filterAllASTElems[FunctionCall] (tUnit)  // Call
    callStartNodes++ filterAllASTElems[FunctionDef](tUnit)   // Start
    nonCallStartNodes++ filterAllASTElems[AST](tUnit) // getAllNodes

    // todo correct? efficient way?

    nonCallStartNodes.--(callStartNodes) // remove CallStartNodes

    setAsJavaSet(nonCallStartNodes)
  }

  def getSuccsOf(stmt: AST) = {
    val succs = succ(stmt, fm, env);
    var results = List.empty[AST]
    for(succ <- succs){
        succ match{
          case Some(x: AST) => results ::: List(x) // question why not <List> :: x ?  This would decrease complexity from O(n) to O(1)!
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
    startPoints ++ succs     // if the assignment is done in one Statement a wrong returntype is generated
    startPoints              // if this line is missing a wrong returntype is generated (Set[Product] instead of Set[AST])
  }

  def isCallStmt(stmt: AST) =
    stmt match {
      case PostfixExpr(_, FunctionCall(_)) => true;
      case _ => false }
  ;

  def isExitStmt(stmt: AST) =
    stmt match {
      case _: ReturnStatement => true;
      case _ => false
    }
  ;


  def isStartPoint(stmt: AST) =
    pred(stmt, fm, env) match {
      case _: FunctionDef => true;
      case _ => false
    }
  ;

  def isFallThroughSuccessor(stmt: AST, suc: AST) =
    succ(stmt, fm, env).size == 1 && succ(stmt, fm, env).head == suc;

  def isBranchTarget(stmt: AST, suc: AST) = succ(stmt, fm, env).exists(x => x == suc)

  def getCallTarget(stmt: AST): Option[List[FunctionDef]] =   {

    if(!stmt.isInstanceOf[FunctionCall]){
      null // proceed only with FunctionCalls
    }

      // get called Function
      var tu = findPriorASTElem[stmt.type ](tUnit, env)
      var called = filterASTElems[FunctionDef](tu)

      Some(called)

    }
}
