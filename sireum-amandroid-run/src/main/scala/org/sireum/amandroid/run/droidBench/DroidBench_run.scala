package org.sireum.amandroid.run.droidBench

import org.sireum.jawa.MessageCenter._
import org.sireum.amandroid.security._
import org.sireum.amandroid.AppCenter
import org.sireum.amandroid.alir.dataRecorder.DataCollector
import org.sireum.amandroid.alir.dataRecorder.MetricRepo
import org.sireum.amandroid.alir.reachingFactsAnalysis.AndroidReachingFactsAnalysisConfig
import org.sireum.jawa.util.Timer
import org.sireum.util.FileUtil
import org.sireum.amandroid.appInfo.AppInfoCollector
import org.sireum.amandroid.alir.taintAnalysis.DefaultAndroidSourceAndSinkManager
import org.sireum.amandroid.AndroidGlobalConfig
import org.sireum.amandroid.util.AndroidLibraryAPISummary
import org.sireum.jawa.alir.LibSideEffectProvider
import org.sireum.util.FileResourceUri
import org.sireum.jawa.util.IgnoreException

/**
 * @author <a href="mailto:fgwei@k-state.edu">Fengguo Wei</a>
 */
object DroidBench_run {
  private final val TITLE = "DroidBench_run"
  
  object DroidBenchCounter {
    var total = 0
    var haveresult = 0
    var taintPathFound = 0
    var taintPathFoundList = Set[String]()
    override def toString : String = "total: " + total + ", haveResult: " + haveresult + ", taintPathFound: " + taintPathFound
  }
  
  private class DroidBenchListener(source_apk : FileResourceUri) extends AmandroidSocketListener {
    def onPreAnalysis: Unit = {
      DroidBenchCounter.total += 1
    }

    def entryPointFilter(eps: Set[org.sireum.jawa.JawaProcedure]): Set[org.sireum.jawa.JawaProcedure] = {
      eps
    }

    def onTimeout : Unit = {}

    def onAnalysisSuccess : Unit = {
      if(AppCenter.getTaintAnalysisResults.exists(!_._2.getTaintedPaths.isEmpty)){
	      DroidBenchCounter.taintPathFound += 1
	      DroidBenchCounter.taintPathFoundList += source_apk
	    }
    	val appData = DataCollector.collect
    	MetricRepo.collect(appData)
//		    	val apkName = title.substring(0, title.lastIndexOf("."))
//		    	val appDataDirFile = new File(outputDir + "/" + apkName)
//		    	if(!appDataDirFile.exists()) appDataDirFile.mkdirs()
//		    	val out = new PrintWriter(appDataDirFile + "/AppData.txt")
//			    out.print(appData.toString)
//			    out.close()
//			    val mr = new PrintWriter(outputDir + "/MetricInfo.txt")
//				  mr.print(MetricRepo.toString)
//				  mr.close()
		  DroidBenchCounter.haveresult += 1
    }

    def onPostAnalysis: Unit = {
      msg_critical(TITLE, DroidBenchCounter.toString)
    }
    
    def onException(e : Exception) : Unit = {
      e match{
        case ie : IgnoreException => System.err.println("Ignored!")
        case a => 
          e.printStackTrace()
      }
    }
  }
  
  def main(args: Array[String]): Unit = {
    if(args.size != 2){
      System.err.print("Usage: source_path output_path")
      return
    }
    
    AndroidReachingFactsAnalysisConfig.k_context = 1
    AndroidReachingFactsAnalysisConfig.resolve_icc = false
    AndroidReachingFactsAnalysisConfig.resolve_static_init = false
    AndroidReachingFactsAnalysisConfig.timerOpt = Some(new Timer(5))
    
    val socket = new AmandroidSocket
    socket.preProcess
    
    val sourcePath = args(0)
    val outputPath = args(1)
    
    val files = FileUtil.listFiles(FileUtil.toUri(sourcePath), ".apk", true).toSet
    
    files.foreach{
      file =>
        msg_critical(TITLE, "####" + file + "#####")
        val app_info = new AppInfoCollector(file)
        socket.loadApk(file, outputPath, AndroidLibraryAPISummary, app_info)
        val ssm = new DefaultAndroidSourceAndSinkManager(app_info.getPackageName, app_info.getLayoutControls, app_info.getCallbackMethods, AndroidGlobalConfig.SourceAndSinkFilePath)
        socket.plugListener(new DroidBenchListener(file))
        socket.runWithDDA(ssm, false, true)
    }
  }
}