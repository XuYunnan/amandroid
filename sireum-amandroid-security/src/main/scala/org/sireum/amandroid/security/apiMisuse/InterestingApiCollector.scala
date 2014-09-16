package org.sireum.amandroid.security.apiMisuse

import org.sireum.amandroid.appInfo.AppInfoCollector
import org.sireum.util._
import org.sireum.amandroid.appInfo.ReachableInfoCollector
import org.sireum.jawa.JawaRecord
import org.sireum.jawa.util.IgnoreException
import org.sireum.jawa.Center
import org.sireum.amandroid.AndroidConstants
import org.sireum.amandroid.AppCenter
import org.sireum.jawa.MessageCenter._

class InterestingApiCollector (apkUri : FileResourceUri) extends AppInfoCollector(apkUri) {
  private final val TITLE = "InterestingApiCollector"
  var ra : ReachableInfoCollector = null
  
  def getInterestingContainers(interestingAPIs : Set[String]) : Set[JawaRecord] = {
	  val interestingContainers : MSet[JawaRecord] = msetEmpty
    interestingAPIs.foreach{
		  api =>
		    interestingContainers ++= this.ra.getSensitiveAPIContainer(api)
		}
		if(interestingContainers.isEmpty) throw new IgnoreException
    interestingContainers.toSet
  }
  
	override def collectInfo : Unit = {
	  val mfp = AppInfoCollector.analyzeManifest(apkUri)
	  this.appPackageName = mfp.getPackageName
		this.componentInfos = mfp.getComponentInfos
		this.uses_permissions = mfp.getPermissions
		this.intentFdb = mfp.getIntentDB
		
	  val afp = AppInfoCollector.analyzeARSC(apkUri)
		val lfp = AppInfoCollector.analyzeLayouts(apkUri, mfp)
		this.layoutControls = lfp.getUserControls
		this.ra = AppInfoCollector.reachabilityAnalysis(mfp)
		val callbacks = AppInfoCollector.analyzeCallback(afp, lfp, ra)
		this.callbackMethods = callbacks
		var components = isetEmpty[JawaRecord]
    mfp.getComponentInfos.foreach{
      f => 
        val record = Center.resolveRecord(f.name, Center.ResolveLevel.HIERARCHY)
        if(!record.isPhantom && record.isApplicationRecord){
	        components += record
	        val clCounter = generateEnvironment(record, if(f.exported)AndroidConstants.MAINCOMP_ENV else AndroidConstants.COMP_ENV, codeLineCounter)
	        codeLineCounter = clCounter
        }
    }
		
		AppCenter.setComponents(components)
		AppCenter.updateIntentFilterDB(this.intentFdb)
		AppCenter.setAppInfo(this)
		msg_normal(TITLE, "Entry point calculation done.")
	}
	
}