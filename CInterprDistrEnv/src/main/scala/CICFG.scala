import de.fosd.typechef.crewrite.{ASTNavigation, ASTEnv, ConditionalControlFlow}
import de.fosd.typechef.featureexpr.FeatureModel
import de.fosd.typechef.parser.c._
import de.fosd.typechef.parser.c.FunctionCall
import de.fosd.typechef.parser.c.FunctionDef
import de.fosd.typechef.parser.c.PostfixExpr
import soot.jimple.interproc.ifds.InterproceduralCFG
import scala.collection.JavaConversions._

class CICFG(env: ASTEnv, fm: FeatureModel) extends ConditionalControlFlow with InterproceduralCFG[AST,FunctionDef] with ASTNavigation {

  def getMethodOf(p1: AST) = null

  def getCalleesOfCallAt(p1: AST) = null

  def getCallersOf(p1: FunctionDef) = null

  def getCallsFromWithin(p1: FunctionDef) = null

  def getReturnSitesOfCallAt(p1: AST) = null

  def allNonCallStartNodes() = null

  def getSuccsOf(stmt: AST) = seqAsJavaList(succ(stmt, fm, env))

  def getStartPointsOf(func: FunctionDef) = setAsJavaSet(Set.empty[AST] ++ succ(func, fm, env))

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
    pred(stmt,env) match {
      case _: FunctionDef => true;
      case _ => false
    }
  ;

  def isFallThroughSuccessor(stmt: AST, suc: AST) =
    succ(stmt,env).size() == 1 && succ(stmt, fm, env).head == suc;

  def isBranchTarget(stmt: AST, suc: AST) = succ(stmt, fm, env).exists(x => x == suc)
}
