package de.fosd.typechef.crewrite

import de.fosd.typechef.conditional._
import de.fosd.typechef.parser.c._
import org.kiama._
import org.kiama.attribution._
import org.kiama.attribution.Attribution._
import de.fosd.typechef.featureexpr.FeatureExpr

trait CAnalysis extends ConditionalNavigation with ASTNavigation {

  // according to paper listed below; computation of cyclomatic complexity already contains
  // conditional inclusion directives of preprocessor
  // cf. http://www.verifysoft.com/de_cmtpp_mscoder.pdf
  val cc: Attributable ==> Int = attr { case a: Attributable => eCC(a) + 1}

  private def eCC(a: Attributable): Int = {
    a match {
      case e: IfStatement => 1 + childrenCC(e);
      case e: ElifStatement => 1 + childrenCC(e);
      case e: Conditional[_] => 1 + childrenCC(e);
      case e: Opt[Attributable] => {
        if (featureExpr(e.entry).isDead()) childrenCC(e) // necessary as parser generates dead AST nodes; cf. http://goo.gl/7Rr1a
        else if (featureExpr(e.entry).equivalentTo(FeatureExpr.base)) childrenCC(e)
        else if (featureExpr(e.entry).equivalentTo(featureExpr(parentAST(e.entry)))) childrenCC(e)
        else 1 + childrenCC(e)
      }
      case e: SwitchStatement => 1 + childrenCC(e);
      case e: CaseStatement => 1 + childrenCC(e);
      case e: DefaultStatement => 1 + childrenCC(e);
      case e: ForStatement => 1 + childrenCC(e);
      case e: WhileStatement => 1 + childrenCC(e);
      case w@List(_) => w.asInstanceOf[List[Attributable]].map(eCC(_)).foldLeft(0)(_ + _)
      case _ => childrenCC(a);
    };
  }

  private def childrenCC(a: Attributable): Int = {
    a.children.map(eCC).foldLeft(0)(_ + _)
  }
}