package de.fosd.typechef.crewrite

import de.fosd.typechef.featureexpr.{FeatureModel, FeatureExpr}
import de.fosd.typechef.conditional.Conditional
import de.fosd.typechef.parser.c._
import scala.Some

// interprocedural control flow graph (cfg) implementation based on the
// intraprocedural cfg implementation (see IntraCFG.scala)
// To do so, we resolve function calls and add edges to function definitions
// to our resulting list.
//
// ChK: search for function calls. we will never be able to be precise here, but we can detect
// standard function calls "a(...)" at least. The type system will also detect types of parameters
// and pointers, but that should not be necessary (with pointers we won't get the precise target
// anyway without expensive dataflow analysis and parameters do not matter since C has no overloading)

trait InterCFG extends IntraCFG {

  // provide a lookup mechanism for function defs (from the type system or selfimplemented)
  // return None if function cannot be found
  def lookupFunctionDef(name: String): Conditional[Option[ExternalDef]]

  override private[crewrite] def findMethodCalls(t: AST, env: ASTEnv, oldres: CFGRes, ctx: FeatureExpr, _res: CFGRes): CFGRes = {
    var res: CFGRes = _res
    val postfixExprs = filterAllASTElems[PostfixExpr](t)
    for (pf@PostfixExpr(Id(funName), FunctionCall(_)) <- postfixExprs) {
      val fexpr = env.featureExpr(pf)
      val newresctx = getNewResCtx(oldres, ctx, fexpr)
      val targetFun = lookupFunctionDef(funName)
      targetFun.mapf(fexpr, {
        case (f, Some(target)) => res = (newresctx and f, f, target) :: res
        case _ =>
      })
    }
    res
  }

  override def getExprSucc(exp: Expr, ctx: FeatureExpr, oldres: CFGRes, fm: FeatureModel, env: ASTEnv): CFGRes = {
    findMethodCalls(exp, env, oldres, ctx, oldres) ++ super.getExprSucc(exp, ctx, oldres, fm, env)
  }
}
