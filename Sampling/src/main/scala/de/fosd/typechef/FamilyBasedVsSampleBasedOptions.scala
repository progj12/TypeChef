package de.fosd.typechef

import java.util
import lexer.options.Options
import lexer.options.Options.OptionGroup
import gnu.getopt.{Getopt, LongOpt}
import java.lang.String

class FamilyBasedVsSampleBasedOptions extends FrontendOptionsWithConfigFiles {
  private[typechef] var fileconfig: Boolean = false
  private[typechef] var codecoverage: Boolean = false
  private[typechef] var codecoverageNH: Boolean = false
  private[typechef] var pairwise: Boolean = false
  private var rootfolder: String = ""

  private final val F_FILECONFIG: Char = Options.genOptionId
  private final val F_CODECOVERAGE: Char = Options.genOptionId
  private final val F_CODECOVERAGENH: Char = Options.genOptionId
  private final val F_PAIRWISE: Char = Options.genOptionId
  private final val F_ROOTFOLDER: Char = Options.genOptionId

  protected override def getOptionGroups() = {
    val groups = new util.ArrayList[OptionGroup](super.getOptionGroups())

    groups.add(new Options.OptionGroup("Sampling options", 1, new Options.Option("rootfolder", LongOpt.REQUIRED_ARGUMENT, F_ROOTFOLDER, "rootfolder", "parent folder of case study"), new Options.Option("fileconfig", LongOpt.NO_ARGUMENT, F_FILECONFIG, null, "enable fileconfig sampling; default is disabled"), new Options.Option("codecoverage", LongOpt.NO_ARGUMENT, F_CODECOVERAGE, null, "enable codecoverage sampling; default is disabled"), new Options.Option("codecoveragenh", LongOpt.NO_ARGUMENT, F_CODECOVERAGENH, null, "enable codecoverage (without header files) sampling; default is disabled"), new Options.Option("pairwise", LongOpt.NO_ARGUMENT, F_PAIRWISE, null, "enable pairwise sampling; default is disabled")))

    groups
  }

  protected override def interpretOption(c: Int, g: Getopt): Boolean = {
    if (c == F_FILECONFIG) fileconfig = true
    else if (c == F_CODECOVERAGE) codecoverage = true
    else if (c == F_PAIRWISE) pairwise = true
    else if (c == F_ROOTFOLDER) {
      checkDirectoryExists(g.getOptarg)
      rootfolder = g.getOptarg
    }
    else {
      return super.interpretOption(c, g)
    }

    true
  }

  def getRootFolder: String = { rootfolder }

}
