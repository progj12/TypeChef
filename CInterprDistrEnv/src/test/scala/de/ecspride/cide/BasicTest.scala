package de.ecspride.cide

import org.junit.Test
import de.fosd.typechef.parser.c._
import de.fosd.typechef.crewrite._
import de.fosd.typechef.featureexpr._
import java.io.{FileNotFoundException, InputStream}



/**
 * Created with IntelliJ IDEA.
 * User: Tim
 * Date: 22.03.13
 * Time: 20:27
 * To change this template use File | Settings | File Templates.
 */
class BasicTest extends TestHelper with EnforceTreeHelper with ConditionalControlFlow with ConditionalNavigation {
  val folder = "testfiles/"

  var transalationUnit: AST = null
  var astEnvironment: ASTEnv = null




  def checkCICFGMethods(file: String) {

    var f : FeatureModel = FeatureExprFactory.default.featureModelFactory.empty

    checkCfg(folder+file, f)

    val cicfg = new CICFG(transalationUnit, astEnvironment, f)


     var ancsn = cicfg.allNonCallStartNodes()

      for(a <- ancsn){
        System.out.println(PrettyPrinter.print(a))
      }


    false
  }


  private def checkCfg(filename: String, fm: FeatureModel = FeatureExprFactory.default.featureModelFactory.empty) = {
    var errorOccured = false
    var tfam: Long = 0
    var tbase: Long = 0
    var tfullcoverage: Long = 0

    println("analysis " + filename)
    val inputStream: InputStream = getClass.getResourceAsStream("/" + folder + filename)

    if (inputStream == null)
      throw new FileNotFoundException("Input file not fould: " + filename)

    val ast = parseFile(inputStream, filename, folder)
    println("checking family-based")
    val family_ast = rewriteInfiniteForLoops[TranslationUnit](prepareAST(ast))
    val family_env = CASTEnv.createASTEnv(family_ast)

    val family_function_defs = filterAllASTElems[FunctionDef](family_ast)

    // ######################################### \\
    transalationUnit = family_ast
    astEnvironment = family_env
    // ######################################### \\

    val tfams = System.currentTimeMillis()
    errorOccured |= family_function_defs.map(intraCfgFunctionDef(_, family_env)).exists(_ == true)
    val tfame = System.currentTimeMillis()

    tfam = tfame - tfams

    println("family-based: " + tfam + "ms")
    println("base variant: " + tbase + "ms")
    println("full coverage: " + tfullcoverage + "ms")
    errorOccured
  }

  private def intraCfgFunctionDef(f: FunctionDef, env: ASTEnv) = {
    val s = getAllSucc(f, FeatureExprFactory.empty, env)
    val p = getAllPred(f, FeatureExprFactory.empty, env)

    //println("succ: " + DotGraph.map2file(s, env, List(), List()))
    //println("pred: " + DotGraph.map2file(p, env, List(), List()))

    val errors = compareSuccWithPred(s, p, env)
    CCFGErrorOutput.printCCFGErrors(s, p, errors, env)

    errors.size > 0
  }


  @Test def testSimpleMethod(){assert(checkCICFGMethods("simpleMethod.c") == true)}

}
