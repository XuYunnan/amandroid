package org.sireum.amandroid.run.report

import org.sireum.jawa.MessageCenter
import org.sireum.jawa.MessageCenter._
import org.sireum.amandroid.security.AmandroidSocket
import org.sireum.util.FileUtil
import org.sireum.amandroid.appInfo.AppInfoCollector
import org.sireum.amandroid.util.AndroidLibraryAPISummary
import org.sireum.util.FileResourceUri
import org.sireum.amandroid.security.AmandroidSocketListener
import org.sireum.amandroid.AppCenter
import org.sireum.amandroid.security.report.ReportGen
import org.sireum.jawa.JawaProcedure
import org.sireum.amandroid.util.AndroidUrlCollector

/**
 * @author <a href="mailto:fgwei@k-state.edu">Fengguo Wei</a>
 */
object ApkReport_run {
  private final val TITLE = "ApkReport_run"
  
  private class ApkReportListener(source_apk : FileResourceUri, outputPath : String) extends AmandroidSocketListener {
    def onPreAnalysis: Unit = {
      
    }

    def entryPointFilter(eps: Set[JawaProcedure]): Set[JawaProcedure] = {
      eps
    }

    def onTimeout : Unit = {}

    def onAnalysisSuccess : Unit = {
      AppCenter.getInterproceduralReachingFactsAnalysisResults.foreach{
        res =>
          val idfg = res._2
      }
    }

    def onPostAnalysis: Unit = {
    }
    
    def onException(e : Exception) : Unit = {
    }
  }
  
  def main(args: Array[String]): Unit = {
    if(args.size != 2){
      System.err.print("Usage: source_path dest_path")
      return
    }
    MessageCenter.msglevel = MessageCenter.MSG_LEVEL.CRITICAL
    try{
      
      val socket = new AmandroidSocket
      socket.preProcess
      
      val sourcePath = args(0)
      val outputPath = args(1)
      
      
      val files = FileUtil.listFiles(FileUtil.toUri(sourcePath), ".apk", true).toSet
      
      files.foreach{
        file =>
          try{
            msg_critical(TITLE, "####" + file + "#####")
            
            val reportGen = new ReportGen(FileUtil.filename(file))
            
            val lac = new LibraryAPICollector
            socket.loadApk(file, outputPath, lac)
            val man = AppInfoCollector.analyzeManifest(file)
            
            reportGen.permissions ++= man.getPermissions
            val comps = man.getComponentInfos
            comps.foreach{
              comp =>
                val comp_report = reportGen.genComp(comp.name, comp.typ, comp.exported, comp.permission)
                
                val intentfilters = man.getIntentDB.getIntentFilters(comp.name)
                intentfilters foreach{
                  inf =>
                    comp_report.addIntentFilter(inf.getActions(), inf.getCategorys(), inf.getData())
                }
                reportGen.comps += comp_report
            }
            reportGen.libLoaded ++= lac.usedLib
            val urls = AndroidUrlCollector.collectUrls(file)
            reportGen.urls ++= urls
//            socket.plugListener(new ApkReportListener(file, outputPath))
//            socket.runWithoutDDA(false, true)
            println(reportGen.toString())
          } catch {
            case e : Throwable =>
              e.printStackTrace()
          } finally {
            socket.cleanEnv
          }
      }
    } catch {
      case e : Throwable =>
        e.printStackTrace()
    }
  }
}