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
import org.sireum.amandroid.alir.interProcedural.taintAnalysis.SourceAndSinkCenter
import org.sireum.amandroid.android.parser.ComponentInfo
import java.io.InputStream
import org.sireum.jawa.util.ResourceRetriever
import org.sireum.amandroid.android.pilarCodeGenerator.AndroidEnvironmentGenerator
import org.sireum.amandroid.android.pilarCodeGenerator.AndroidSubstituteRecordMap
import org.sireum.amandroid.android.pilarCodeGenerator.AndroidEntryPointConstants

/**
 * adapted from Steven Arzt
 * @author <a href="mailto:fgwei@k-state.edu">Fengguo Wei</a>
 */
class AppInfoCollector(apkRet : ResourceRetriever) {  
  private var uses_permissions : ISet[String] = isetEmpty
	private var callbackMethods : Map[JawaRecord, Set[JawaProcedure]] = Map()
	private var componentInfos : Set[ComponentInfo] = null
	private var layoutControls : Map[Int, LayoutControl] = Map()
	private var appPackageName : String = ""
	private var taintWrapperFile : String = ""
	private var intentFdb : IntentFilterDataBase = null
	private var codeLineCounter : Int = 0
	/**
	 * Map from record name to it's env procedure code.
	 */
	private var envMap : Map[JawaRecord, JawaProcedure] = Map()
	def getAppName = this.apkRet.name
	def getUsesPermissions = this.uses_permissions
	
	def printEnvs() =
	  envMap.foreach{case(k, v) => println("Environment for " + k + "\n" + v)}
	
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
	def getEnvMap = this.envMap
	
	def hasEnv(rec : JawaRecord) : Boolean = this.envMap.contains(rec)
	

	/**
	 * generates env code for a component like Activity, BroadcastReceiver, etc.
	 * @param recordName component name
	 * @param codeCtr code line number of the last generated env
	 * @return codeCtr + newly generated number of lines
	 */
	def generateEnvironment(record : JawaRecord, envName : String, codeCtr: Int) : Int = {
	  if(record == null) return 0
		//generate env main method
  	msg_critical("Generate environment for " + record)
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
	  this.envMap += (record -> proc)
	  dmGen.getCodeCounter
	}
	
	def dynamicRegisterComponent(comRec : JawaRecord, iDB : IntentFilterDataBase, precise : Boolean) = {
	  msg_critical("*************Dynamic Register Component**************")
	  msg_normal("Component name: " + comRec)
	  this.intentFdb.updateIntentFmap(iDB)
	  val analysisHelper = new CallBackInfoCollector(Set(comRec.getName)) 
		analysisHelper.collectCallbackMethods()
		this.callbackMethods = analysisHelper.getCallbackMethods
		analysisHelper.getCallbackMethods.foreach {
	    case(k, v) =>
  			this.callbackMethods += (k -> (this.callbackMethods.getOrElse(k, isetEmpty) ++ v))
		}
	  msg_normal("Found " + this.callbackMethods.size + " callback methods")
    val clCounter = generateEnvironment(comRec, AndroidConstants.COMP_ENV, codeLineCounter)
    codeLineCounter = clCounter
    AppCenter.addComponent(comRec)
    AppCenter.addDynamicRegisteredComponent(comRec, precise)
    AppCenter.updateIntentFilterDB(iDB)
    msg_critical("~~~~~~~~~~~~~~~~~~~~~~~~~Done~~~~~~~~~~~~~~~~~~~~~~~~~~")
	}
	
	def collectInfo = {
	  val mfp = new ManifestParser
		mfp.loadManifestFile(apkRet)
		this.appPackageName = mfp.getPackageName
		this.componentInfos = mfp.getComponentInfos
		this.uses_permissions = mfp.getPermissions
		this.intentFdb = mfp.getIntentDB
	  msg_normal("entrypoints--->" + mfp.getComponentRecords)
	  msg_normal("packagename--->" + mfp.getPackageName)
	  msg_normal("permissions--->" + mfp.getPermissions)
	  msg_normal("intentDB------>" + mfp.getIntentDB)
		// Parse the resource file
	  val afp = new ARSCFileParser()
		afp.parse(apkRet)
	  msg_detail("arscstring-->" + afp.getGlobalStringPool)
	  msg_detail("arscpackage-->" + afp.getPackages)
		
		// Find the user-defined sources in the layout XML files
	  val lfp = new LayoutFileParser
		lfp.setPackageName(this.appPackageName)
		lfp.parseLayoutFile(apkRet, this.componentInfos.map(_.name))
		this.layoutControls = lfp.getUserControls
		msg_detail("layoutcallback--->" + lfp.getCallbackMethods)
	  msg_detail("layoutuser--->" + lfp.getUserControls)
		
		// Collect the callback interfaces implemented in the app's source code
		val analysisHelper = new CallBackInfoCollector(this.componentInfos.map(_.name)) 
		analysisHelper.collectCallbackMethods()
		this.callbackMethods = analysisHelper.getCallbackMethods
		msg_detail("LayoutClasses --> " + analysisHelper.getLayoutClasses)

		analysisHelper.getCallbackMethods.foreach {
	    case(k, v) =>
  			this.callbackMethods += (k -> (this.callbackMethods.getOrElse(k, isetEmpty) ++ v))
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
		                var callbackProcedure : JawaProcedure = null
		                breakable{ 
		                  while(callbackProcedure == null){
			                  if(callbackRecord.declaresProcedureByShortName(methodName))
			                  	callbackProcedure = callbackRecord.getProcedureByShortName(methodName)
			                  if(callbackRecord.hasSuperClass)
			                    callbackRecord = callbackRecord.getSuperClass
			                  else break
		                  }
		                }
		                if(callbackProcedure != null){
		                  this.callbackMethods += (k -> (this.callbackMethods.getOrElse(k, isetEmpty) + callbackProcedure))
		                } else {
		                  err_msg_normal("Callback method " + methodName + " not found in class " + k);
		                }
		                
		            }
		          }
		        } else {
		          err_msg_critical("Unexpected resource type for layout class")
		        }
		    }
		}
		val callbacks = if(!this.callbackMethods.isEmpty)this.callbackMethods.map(_._2).reduce(iunion[JawaProcedure]) else isetEmpty[JawaProcedure]
		msg_normal("Found " + callbacks.size + " callback methods")
		msg_detail("Which are: " + this.callbackMethods)
    var components = isetEmpty[JawaRecord]
    this.componentInfos.foreach{
      f => 
        val record = Center.resolveRecord(f.name, Center.ResolveLevel.BODIES)
        if(!record.isPhantom){
	        components += record
	        val clCounter = generateEnvironment(record, if(f.exported)AndroidConstants.MAINCOMP_ENV else AndroidConstants.COMP_ENV, codeLineCounter)
	        codeLineCounter = clCounter
        }
    }
		SourceAndSinkCenter.init(appPackageName, afp, layoutControls, callbacks)
		AppCenter.setComponents(components)
		AppCenter.updateIntentFilterDB(this.intentFdb)
		AppCenter.setAppInfo(this)
		msg_normal("Entry point calculation done.")
	}
}