package org.sireum.amandroid.run.test

import org.sireum.util._
import org.sireum.jawa.MessageCenter._
import java.io.File
import java.net.URI
import org.sireum.jawa.util.APKFileResolver
import org.sireum.amandroid.decompile.Dex2PilarConverter
import org.sireum.jawa.JawaCodeSource
import org.sireum.jawa.GlobalConfig
import org.sireum.jawa.DefaultLibraryAPISummary
import org.sireum.jawa.util.URLInString
import java.io.PrintWriter
import org.sireum.amandroid.appInfo.AppInfoCollector
import org.sireum.amandroid.parser.ResourceFileParser
import org.sireum.amandroid.parser.ARSCFileParser
import java.io.FileWriter
import org.sireum.jawa.MessageCenter

object UrlCollection_run {
  private final val TITLE = "UrlCollection_run"
  
  def main(args: Array[String]): Unit = {
    if(args.size != 1){
      System.err.print("Usage: source_path")
      return
    }
    MessageCenter.msglevel = MessageCenter.MSG_LEVEL.CRITICAL
    val outputpath = "/Volumes/ArgusGroup/Stash/outputs/url_collection"
    val outputUri = FileUtil.toUri(outputpath)
    val sourcePath = args(0)
    val files = FileUtil.listFiles(FileUtil.toUri(sourcePath), ".apk", true).toSet
//    val results : MMap[String, (Set[String], Set[String])] = mmapEmpty
    files.foreach{
      file =>
        msg_critical(TITLE, "####" + file + "#####")
        try{
          val man = AppInfoCollector.analyzeManifest(file)
          val strs = msetEmpty[String]
        	val rfp = new ResourceFileParser
        	rfp.parseResourceFile(file)
        	strs ++= rfp.getAllStrings
        	val arsc = new ARSCFileParser
        	arsc.parse(file)
        	strs ++= arsc.getGlobalStringPool.map(_._2)
          
          val srcFile = new File(new URI(file))
        	val dexFile = APKFileResolver.getDexFile(file, FileUtil.toUri(srcFile.getParentFile()))
        	
        	// convert the dex file to the "pilar" form
        	val pilarRootUri = Dex2PilarConverter.convert(dexFile)
        	val pilarFile = new File(new URI(pilarRootUri))
        	//store the app's pilar code in AmandroidCodeSource which is organized record by record.
        	JawaCodeSource.load(pilarRootUri, GlobalConfig.PILAR_FILE_EXT, DefaultLibraryAPISummary)
        	val codes = JawaCodeSource.getAppRecordsCodes
        	val code_urls : Set[String] =
          	if(!codes.isEmpty){
            	codes.map{
                case (name, code) =>
                  URLInString.extract(code)
              }.reduce(iunion[String])
          	} else isetEmpty[String]
          val res_urls : Set[String] =
            if(!strs.isEmpty){
              strs.map{
                str =>
                  URLInString.extract(str)
              }.reduce(iunion[String])
            } else isetEmpty[String]
          val summaryfile = new File(outputpath + "/summary.txt")
          val sos = new FileWriter(summaryfile, true)
          try{
            sos.write(file + ":\n")
            sos.write("package name: " + man.getPackageName + "\n")
            sos.write("resource:\n")
            res_urls.foreach{
              case rurl =>
                sos.write(rurl + "\n")
            }
            sos.write("code:\n")
            code_urls.foreach{
              case curl =>
                sos.write(curl + "\n")
            }
            sos.write("\n\n")
          } finally {
            sos.close()
            JawaCodeSource.clearAppRecordsCodes
    	    	APKFileResolver.deleteOutputs(file, outputUri)
    	    	System.gc
          }
        } catch {
          case e : Exception =>
            err_msg_critical(TITLE, e.getMessage())
        }
    }
    
  }
}