import de.fosd.typechef.crewrite.{ASTNavigation, ASTEnv, ConditionalControlFlow}
import de.fosd.typechef.featureexpr.FeatureModel
import de.fosd.typechef.parser.c._
import de.fosd.typechef.parser.c.FunctionCall
import de.fosd.typechef.parser.c.FunctionDef
import de.fosd.typechef.parser.c.PostfixExpr
import soot.jimple.interproc.ifds.InterproceduralCFG
import scala.collection.JavaConversions._
import scala.collection.immutable.TreeSet

class CICFG(env: ASTEnv, fm: FeatureModel) extends ConditionalControlFlow with InterproceduralCFG[AST,FunctionDef] with ASTNavigation {

  /**
   * Method containing the a Node
   * @param p1  current Node
   * @return    FunctionDef of Method containing n1
   *
   *            todo call-node is on caller site!
   *
   * idea: traverse pred(p1) to next FunctionDef
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
  def getCallsFromWithin(p1: FunctionDef) = null
  // idea "tree" build from p1 to next "returnExpr" build with breadthFirstSearch with succ(..)

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
    rsoc.distinct
  }

  /**
   * Returns the set of all nodes that are neither call nor start nodes.
   *
   * Traverse all Elements of the AST and collect all Statements (exclude {isCallStmt || isStartPoint})
   * @return  Set of nodes
   */
  def allNonCallStartNodes() = {
    // question how to get the "root" node?

    null // todo remove
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
    results
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

}
