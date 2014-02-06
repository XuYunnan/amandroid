package org.sireum.amandroid.android.appInfo

import org.sireum.util._
import org.sireum.amandroid.alir.AndroidConstants
import org.sireum.pilar.symbol.ProcedureSymbolTable
import org.sireum.alir.ControlFlowGraph
import org.sireum.amandroid.android.parser.LayoutControl
import org.sireum.amandroid.android.parser.ARSCFileParser
import org.sireum.amandroid.android.parser.IntentFilterDataBase
import org.sireum.alir.ReachingDefinitionAnalysis
import org.sireum.amandroid.android.parser.ManifestParser
import org.sireum.jawa.JawaRecord
import org.sireum.jawa.Center
import org.sireum.jawa.JawaProcedure
import org.sireum.amandroid.android.parser.LayoutFileParser
import scala.util.control.Breaks._
import org.sireum.amandroid.alir.AppCenter
import org.sireum.jawa.GlobalConfig
import org.sireum.jawa.MessageCenter._
import org.sireum.amandroid.android.parser.ComponentInfo
import java.io.InputStream
import org.sireum.jawa.util.ResourceRetriever
import org.sireum.amandroid.android.pilarCodeGenerator.AndroidEnvironmentGenerator
import org.sireum.amandroid.android.pilarCodeGenerator.AndroidSubstituteRecordMap
import org.sireum.amandroid.android.pilarCodeGenerator.AndroidEntryPointConstants
import java.io.File
import java.net.URI
import org.sireum.jawa.util.IgnoreException

/**
 * adapted from Steven Arzt
 * @author <a href="mailto:fgwei@k-state.edu">Fengguo Wei</a>
 */
class AppInfoCollector(apkUri : FileResourceUri) {  
  
  protected var uses_permissions : ISet[String] = isetEmpty
	protected var callbackMethods : Map[JawaRecord, Set[JawaProcedure]] = Map()
	protected var componentInfos : Set[ComponentInfo] = Set()
	protected var layoutControls : Map[Int, LayoutControl] = Map()
	protected var appPackageName : String = null
	protected var taintWrapperFile : String = null
	protected var intentFdb : IntentFilterDataBase = null
	protected var codeLineCounter : Int = 0
	
	/**
	 * Map from record name to it's env procedure code.
	 */
	protected var envProcMap : Map[JawaRecord, JawaProcedure] = Map()
	def getAppName = new File(new URI(apkUri)).getName()
	def getPackageName = this.appPackageName
	def getUsesPermissions = this.uses_permissions
	def getLayoutControls = this.layoutControls
	def getCallbackMethodMapping = this.callbackMethods
	def getCallbackMethods = if(!this.callbackMethods.isEmpty)this.callbackMethods.map(_._2).reduce(iunion[JawaProcedure]) else isetEmpty[JawaProcedure]
	def printEnvs() =
	  envProcMap.foreach{case(k, v) => println("Environment for " + k + "\n" + v)}
	
	def printEntrypoints() = {
		if (this.componentInfos == null)
			println("Entry points not initialized")
		else {
			println("Classes containing entry points:")
			for (record <- componentInfos)
				println("\t" + record)
			println("End of Entrypoints")
		}
	}
		
	def setTaintWrapperFile(taintWrapperFile : String) = {
		this.taintWrapperFile = taintWrapperFile;
	}
	
	def getIntentDB = this.intentFdb
	def getEntryPoints = this.componentInfos.map(_.name).toSet
	
	def getComponentInfos = this.componentInfos
	def getEnvMap = this.envProcMap
	def getEnvString : String = {
	  val sb = new StringBuilder
	  this.envProcMap.foreach{
	    case (k, v) =>
	      sb.append("*********************** Environment for " + k + " ************************\n")
	      sb.append(v.retrieveCode + "\n\n")
	  }
	  sb.toString.intern()
	}
	
	def hasEnv(rec : JawaRecord) : Boolean = this.envProcMap.contains(rec)
	
	/**
	 * generates env code for a component like Activity, BroadcastReceiver, etc.
	 * @param recordName component name
	 * @param codeCtr code line number of the last generated env
	 * @return codeCtr + newly generated number of lines
	 */
	def generateEnvironment(record : JawaRecord, envName : String, codeCtr: Int) : Int = {
	  if(record == null) return 0
		//generate env main method
  	msg_normal("Generate environment for " + record)
	  val dmGen = new AndroidEnvironmentGenerator
	  dmGen.setSubstituteRecordMap(AndroidSubstituteRecordMap.getSubstituteRecordMap)
	  dmGen.setCurrentComponent(record.getName)
	  dmGen.setCodeCounter(codeCtr)
	  var callbackMethodSigs : Map[String, Set[String]] = Map()
	  this.callbackMethods.foreach{
	    case (record, procs) =>
	      procs.foreach{
	        p =>
	          callbackMethodSigs += (record.getName -> (callbackMethodSigs.getOrElse(record.getName, isetEmpty) + p.getSignature))
	      }
	  }
	  dmGen.setCallbackFunctions(callbackMethodSigs)
    val proc = dmGen.generateWithParam(List(AndroidEntryPointConstants.INTENT_NAME), envName)
    this.envProcMap += (record -> proc)
	  dmGen.getCodeCounter
	}
	
	def dynamicRegisterComponent(comRec : JawaRecord, iDB : IntentFilterDataBase, precise : Boolean) = {
	  this.synchronized{
		  if(!comRec.declaresProcedureByShortName(AndroidConstants.COMP_ENV)){
			  msg_critical("*************Dynamically Register Component**************")
			  msg_normal("Component name: " + comRec)
			  this.intentFdb.updateIntentFmap(iDB)
			  val analysisHelper = new ReachableInfoCollector(Set(comRec.getName)) 
				analysisHelper.collectCallbackMethods()
				this.callbackMethods = analysisHelper.getCallbackMethods
				analysisHelper.getCallbackMethods.foreach {
			    case(k, v) =>
		  			this.callbackMethods += (k -> (this.callbackMethods.getOrElse(k, isetEmpty) ++ v))
				}
			  msg_normal("Found " + this.callbackMethods.size + " callback methods")
		    val clCounter = generateEnvironment(comRec, AndroidConstants.COMP_ENV, this.codeLineCounter)
		    this.codeLineCounter = clCounter
		    AppCenter.addComponent(comRec)
		    AppCenter.addDynamicRegisteredComponent(comRec, precise)
		    AppCenter.updateIntentFilterDB(iDB)
		    msg_critical("~~~~~~~~~~~~~~~~~~~~~~~~~Done~~~~~~~~~~~~~~~~~~~~~~~~~~")
		  }
	  }
	}
	
	def collectInfo : Unit = {
	  val mfp = AppInfoCollector.analyzeManifest(apkUri)
	  val afp = AppInfoCollector.analyzeARSC(apkUri)
		val lfp = AppInfoCollector.analyzeLayouts(apkUri, mfp)
		val ra = AppInfoCollector.reachabilityAnalysis(mfp)
		val callbacks = AppInfoCollector.analyzeCallback(afp, lfp, ra)
		
		this.appPackageName = mfp.getPackageName
		this.componentInfos = mfp.getComponentInfos
		this.uses_permissions = mfp.getPermissions
		this.intentFdb = mfp.getIntentDB
		this.layoutControls = lfp.getUserControls
		this.callbackMethods = callbacks
		
		var components = isetEmpty[JawaRecord]
    mfp.getComponentInfos.foreach{
      f => 
        val record = Center.resolveRecord(f.name, Center.ResolveLevel.HIERARCHY)
        if(!record.isPhantom){
	        components += record
	        val clCounter = generateEnvironment(record, if(f.exported)AndroidConstants.MAINCOMP_ENV else AndroidConstants.COMP_ENV, codeLineCounter)
	        codeLineCounter = clCounter
        }
    }
		
		AppCenter.setComponents(components)
		AppCenter.updateIntentFilterDB(this.intentFdb)
		AppCenter.setAppInfo(this)
		msg_normal("Entry point calculation done.")
	}
}

object AppInfoCollector {
	def analyzeManifest(apkUri : FileResourceUri) : ManifestParser = {
	  val mfp = new ManifestParser
		mfp.loadManifestFile(apkUri)
	  msg_normal("entrypoints--->" + mfp.getComponentRecords)
	  msg_normal("packagename--->" + mfp.getPackageName)
	  msg_normal("permissions--->" + mfp.getPermissions)
	  msg_normal("intentDB------>" + mfp.getIntentDB)
	  mfp
	}
	
	def analyzeARSC(apkUri : FileResourceUri) : ARSCFileParser = {
	  // Parse the resource file
	  val afp = new ARSCFileParser()
		afp.parse(apkUri)
	  msg_detail("arscstring-->" + afp.getGlobalStringPool)
	  msg_detail("arscpackage-->" + afp.getPackages)
	  afp
	}
	
	def analyzeLayouts(apkUri : FileResourceUri, mfp : ManifestParser) : LayoutFileParser = {
	  // Find the user-defined sources in the layout XML files
	  val lfp = new LayoutFileParser
		lfp.setPackageName(mfp.getPackageName)
		lfp.parseLayoutFile(apkUri, mfp.getComponentInfos.map(_.name))
		msg_detail("layoutcallback--->" + lfp.getCallbackMethods)
	  msg_detail("layoutuser--->" + lfp.getUserControls)
	  lfp
	}
	
	def analyzeCallback(afp : ARSCFileParser, lfp : LayoutFileParser, analysisHelper : ReachableInfoCollector) : Map[JawaRecord, Set[JawaProcedure]] = {
	  var callbackMethods : Map[JawaRecord, Set[JawaProcedure]] = Map()
	  analysisHelper.collectCallbackMethods()
		callbackMethods = analysisHelper.getCallbackMethods
		msg_detail("LayoutClasses --> " + analysisHelper.getLayoutClasses)

		analysisHelper.getCallbackMethods.foreach {
	    case(k, v) =>
  			callbackMethods += (k -> (callbackMethods.getOrElse(k, isetEmpty) ++ v))
		}
	  
		// Collect the XML-based callback methods
		analysisHelper.getLayoutClasses.foreach {
		  case (k, v) =>
		    v.foreach {
		      i =>
		        val resource = afp.findResource(i)
		        if(resource.isInstanceOf[afp.StringResource]){
		          val strRes = resource.asInstanceOf[afp.StringResource]
		          if(lfp.getCallbackMethods.contains(strRes.value)){
		            lfp.getCallbackMethods(strRes.value).foreach{
		              methodName =>
		                //The callback may be declared directly in the class or in one of the superclasses
		                var callbackRecord = k
		                var callbackProcedure : Set[JawaProcedure] = Set()
		                breakable{ 
		                  while(callbackProcedure.isEmpty){
			                  if(callbackRecord.declaresProcedureByShortName(methodName))
			                  	callbackProcedure = callbackRecord.getProceduresByShortName(methodName)
			                  if(callbackRecord.hasSuperClass)
			                    callbackRecord = callbackRecord.getSuperClass
			                  else break
		                  }
		                }
		                if(callbackProcedure != null){
		                  callbackMethods += (k -> (callbackMethods.getOrElse(k, isetEmpty) ++ callbackProcedure))
		                } else {
		                  err_msg_normal("Callback method " + methodName + " not found in class " + k);
		                }
		                
		            }
		          }
		        } else {
		          err_msg_normal("Unexpected resource type for layout class")
		        }
		    }
		}
		callbackMethods
	}
	
	def reachabilityAnalysis(mfp : ManifestParser) : ReachableInfoCollector = {
	  // Collect the callback interfaces implemented in the app's source code
		val analysisHelper = new ReachableInfoCollector(mfp.getComponentInfos.map(_.name)) 
	  analysisHelper.init
//	  this.sensitiveLayoutContainers = analysisHelper.getSensitiveLayoutContainer(this.layoutControls)
		analysisHelper
	}
}