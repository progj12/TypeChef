package de.ecspride.cide

import heros.{FlowFunction, FlowFunctions}
import de.fosd.typechef.parser.c._
import javafx.scene.Scene
import heros.template.DefaultIFDSTabulationProblem
import java.util ._
import java.util
import heros.flowfunc.{KillAll, Kill, Identity}
import javax.lang.model.`type`.NullType

/**
 * Created with IntelliJ IDEA.
 * User: Tim
 * Date: 13.05.13
 * Time: 21:52
 * To change this template use File | Settings | File Templates.
 */
class IFDSUninitializedVariables(icfg: CICFG) extends DefaultIFDSTabulationProblem {

  def createFlowFunctionsFactory(): FlowFunctions[AST, Specifier, FunctionDef] = {
    new FlowFunctions[AST, Specifier, FunctionDef]() {

      @Override
      def getNormalFlowFunction (curr: AST, succ: AST): FlowFunction[Specifier] = {
        val m = icfg.getMethodOf(curr)
        if (Scene.v().getEntryPoints().contains(m) && icfg.isStartPoint(curr)) {     // Scene?
          return new FlowFunction[Specifier] () {

            @Override
            def computeTargets (source: Specifier): util.Set[Specifier] = {
              if (source == zeroValue()) {
                val res: LinkedHashSet[Specifier] = new LinkedHashSet[Specifier]()
                res.addAll(m.getActiveBody().getSpecifiers())                // Method methods needed
                 for (i <- 0 to m.getParameterCount()){
                  res.remove(m.getActiveBody().getParameterSpecifier(i))
                 }
                 return res.asInstanceOf[util.Set[Specifier]]
              }
              return new LinkedHashSet[Specifier].asInstanceOf[util.Set[Specifier]]
            }
          }
        }

        if (curr.isInstanceOf[Declaration]) {
          val definition = curr.asInstanceOf[Declaration]
          val leftOp: AST = definition.getLeftOp()                        // knowledge of possible node-types necessary
          if (leftOp.isInstanceOf[Specifier]) {
            val leftOpSpecifier: Specifier = leftOp.asInstanceOf[Specifier]
            return new FlowFunction[Specifier] () {

              @Override
              def computeTargets(source: Specifier): util.Set[Specifier]=
              {
                var useBoxes: List[ValueBox] = definition.getUseBoxes()      // Use-/Valueboxes or equivalent functionality needed
                for (valueBox <- useBoxes)
                {
                  if (valueBox.getValue().equivTo(source)) {
                    var res: LinkedHashSet[Specifier] = new LinkedHashSet[Specifier]()
                    res.add(source)
                    res.add(leftOpSpecifier)
                    return res.asInstanceOf[util.Set[Specifier]]
                  }
                }

                if (leftOp.equivTo(source))
                  return java.util.Collections.emptySet()

                return java.util.Collections.singleton(source)
              }

            }
          }
        }

        return Identity.v()
      }

      @Override
      def getCallFlowFunction(callStmt: AST, destinationMethod: FunctionDef): FlowFunction[Specifier]=
      {
        val stmt: Stmt = (Stmt) callStmt              // Exact type of a call statement?
        invokeExpr: InvokeExpr = stmt.getInvokeExpr()       // Invoke expression of a call statement?
        val args: List[Value]  = invokeExpr.getArgs()   // Value?

        val SpecifierArguments: List[Specifier]  = new ArrayList[Specifier]()
        for (v <- args)
        if (v.isInstanceOf[Specifier]) // unknown type: Value
          SpecifierArguments.add(v.asInstanceOf[Specifier])

        return new FlowFunction[Specifier] () {

          @Override
          def computeTargets(source: Specifier): Set [Specifier] =
            {
            for (SpecifierArgument <- SpecifierArguments)
            {
              if (source.equivTo(SpecifierArgument)) {
                return Collections.singleton[Specifier] (destinationMethod.getActiveBody().getParameterSpecifier(args.indexOf(SpecifierArgument)))
              }
            }

            if (source == zeroValue()) {
              //gen all Specifiers that are not parameter Specifiers
              var Specifiers: Chain[Specifier] = destinationMethod.getActiveBody().getSpecifiers()     // Chain?
              var uninitializedSpecifiers: LinkedHashSet[Specifier] = new LinkedHashSet[Specifier](Specifiers)
              for ( i <-  0 to  destinationMethod.getParameterCount())
              {
                uninitializedSpecifiers.remove(destinationMethod.getActiveBody().getParameterSpecifier(i))
              }
              return uninitializedSpecifiers
            }

            return Collections.emptySet()
          }

        }
      }

      @Override
      def getReturnFlowFunction(callSite: AST, calleeMethod: FunctionDef,
      exitStmt: AST, returnSite: AST): FlowFunction[Specifier] =
        {
        if (callSite.isInstanceOf[DefinitionStmt]) {                    // Definition statement in typechef?
          val definition: DefinitionStmt = callSite.asInstanceOf[DefinitionStmt]
          if (definition.getLeftOp().isInstanceOf[Specifier]) {
            val leftOpSpecifier: Specifier = definition.getLeftOp().asInstanceOf[Specifier]
            if (exitStmt.isInstanceOf[ReturnStmt]) {
              val returnStmt: ReturnStmt = exitStmt.asInstanceOf[ReturnStmt]
              return new FlowFunction[Specifier] () {

                @Override
                def computeTargets(source: Specifier): Set[Specifier] =  {
                  if (returnStmt.getOp().equivTo(source))
                    return Collections.singleton(leftOpSpecifier)
                  return Collections.emptySet()
                }

              }
            } else if (exitStmt.isInstanceOf[ThrowStmt]) {          // Throw Statement in typechef?
              //if we throw an exception, LHS of call is undefined
              return new FlowFunction[Specifier] () {

                @Override
                def computeTargets(source: Specifier): util.Set[Specifier] =
                {
                  if (source == zeroValue())
                    return Collections.singleton(leftOpSpecifier)
                  else
                    return Collections.emptySet()
                }

              }
            }
          }
        }

        return KillAll.v()
      }

      @Override
      def getCallToReturnFlowFunction (callSite: AST, returnSite: AST): FlowFunction[Specifier] = {
        if (callSite.isInstanceOf[DefinitionStmt]) {
          var definition: DefinitionStmt = callSite.asInstanceOf[DefinitionStmt]
          if (definition.getLeftOp().isInstanceOf[Specifier]) {
            val leftOpSpecifier: Specifier = definition.getLeftOp().asInstanceOf[Specifier]
            return new Kill[Specifier] (leftOpSpecifier)
          }
        }
        return Identity.v()
      }
    }
  }

  @Override
  def initialSeeds(): Set[AST] = {
    return Collections.singleton(Scene.v().getMainMethod().getActiveBody().getUnits().getFirst())
  }

  @Override
  def createZeroValue() = {
    return new JimpleSpecifier("<<zero>>", NullType.v())         // Null ?!
  }

}

}
