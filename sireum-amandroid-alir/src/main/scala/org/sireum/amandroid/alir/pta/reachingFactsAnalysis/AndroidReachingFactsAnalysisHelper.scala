/*
Copyright (c) 2013-2014 Fengguo Wei & Sankardas Roy, Kansas State University.        
All rights reserved. This program and the accompanying materials      
are made available under the terms of the Eclipse Public License v1.0 
which accompanies this distribution, and is available at              
http://www.eclipse.org/legal/epl-v10.html                             
*/
package org.sireum.amandroid.alir.pta.reachingFactsAnalysis

import org.sireum.util._
import org.sireum.jawa.JawaProcedure
import org.sireum.jawa.alir.pta.reachingFactsAnalysis.RFAFact
import org.sireum.jawa.alir.Context
import org.sireum.jawa.JawaRecord
import org.sireum.jawa.alir.controlFlowGraph.InterproceduralControlFlowGraph
import org.sireum.jawa.alir.controlFlowGraph.ICFGNode
import org.sireum.jawa.MessageCenter._
import org.sireum.jawa.ClassLoadManager
import org.sireum.amandroid.AndroidGlobalConfig
import java.io.File
import java.io.PrintWriter
import org.sireum.amandroid.AppCenter
import org.sireum.jawa.alir.dataDependenceAnalysis.InterproceduralDataDependenceAnalysis
import org.sireum.amandroid.alir.taintAnalysis
import org.sireum.amandroid.alir.pta.reachingFactsAnalysis.model.AndroidModelCallHandler
import org.sireum.jawa.alir.pta.PTAResult
import org.sireum.jawa.util.MyTimer
import org.sireum.jawa.alir.dataFlowAnalysis.ExtraInfo
import org.sireum.jawa.alir.dataFlowAnalysis.InterProceduralDataFlowGraph
import org.sireum.jawa.Center

/**
 * @author <a href="mailto:fgwei@k-state.edu">Fengguo Wei</a>
 * @author <a href="mailto:sroy@k-state.edu">Sankardas Roy</a>
 */ 
object AndroidReachingFactsAnalysisHelper {
	private final val TITLE = "AndroidReachingFactsAnalysisHelper"
	def isModelCall(calleeProc : JawaProcedure) : Boolean = {
    AndroidModelCallHandler.isModelCall(calleeProc)
  } 
  def doModelCall(s : PTAResult, calleeProc : JawaProcedure, args : List[String], retVars : Seq[String], currentContext : Context) : (ISet[RFAFact], ISet[RFAFact]) = {
    AndroidModelCallHandler.doModelCall(s, calleeProc, args, retVars, currentContext)
  }  
  def isICCCall(calleeProc : JawaProcedure) : Boolean = {
    AndroidModelCallHandler.isICCCall(calleeProc)
  } 
  def doICCCall(s : PTAResult, calleeProc : JawaProcedure, args : List[String], retVars : Seq[String], currentContext : Context) : (ISet[RFAFact], ISet[JawaProcedure]) = {
    AndroidModelCallHandler.doICCCall(s, calleeProc, args, retVars, currentContext)
  }
  def isServiceAndHasRpcMethod(record : JawaRecord) = {
    var result = false
    val ancestors = Center.getRecordHierarchy.getAllSuperClassesOf(record)
    val sAnc = ancestors.filter { x => x.getName == AndroidEntryPointConstants.SERVICE_CLASS}
    if(!sAnc.isEmpty){
      val procs = record.getProcedures.filter { 
        proc => 
          !(proc.isConstructor || AndroidEntryPointConstants.getServiceLifecycleMethods().contains(proc.getSubSignature)) 
      }
      if(!procs.isEmpty)
        result = true
    }
    result
  } 
  def getRpcMethods(record : JawaRecord): Set[JawaProcedure] = {
    var result: MSet[JawaProcedure] = msetEmpty
    val ancestors = Center.getRecordHierarchy.getAllSuperClassesOf(record)
    val sAnc = ancestors.filter { x => x.getName == AndroidEntryPointConstants.SERVICE_CLASS}
    if(!sAnc.isEmpty){
      val procs = record.getProcedures.filter { 
        proc => 
          !(proc.isConstructor || AndroidEntryPointConstants.getServiceLifecycleMethods().contains(proc.getSubSignature)) 
      }
      result ++=procs
    }
    result.toSet
  }
  def doIrfaMerge(entryPoints:Set[JawaProcedure], parallel: Boolean, timer : Option[MyTimer]) ={    
    //initialize the appPool and worklist           
    var idfgMap : MMap[JawaProcedure, InterProceduralDataFlowGraph] = mmapEmpty
    var irfaMap : MMap[JawaProcedure, AndroidReachingFactsAnalysisExtended.Result] = mmapEmpty
    val appPool : ExtraInfo[RFAFact] = new ExtraInfo[RFAFact]
    var compPool : MMap[JawaProcedure, ExtraInfo[RFAFact]] = mmapEmpty
    var converged = false
    val worklist = mlistEmpty[JawaProcedure]
    entryPoints.map { 
      ep => 
        msg_critical(TITLE, "--------------initialize Component " + ep + "--------------")                                                
        val initialfacts = AndroidRFAConfig.getInitialFactsForMainEnvironment(ep)
        val (idfg, irfaRes) = AndroidReachingFactsAnalysisExtended(ep, null, null, initialfacts, new ClassLoadManager, timer)
        idfgMap +=(ep -> idfg)
        irfaMap +=(ep -> irfaRes)
        compPool += (ep -> irfaRes.getExtraInfo)
        //appPool.merge(compPool(ep))
        worklist += ep
    }
    val phase2=true
    if(phase2){
      while(!worklist.isEmpty){
        converged = true
        val ep = worklist.remove(0)
        msg_critical(TITLE, "--------------Current item taken out from worklist is Component:" + ep + "--------------")
        //System.out.println(" appPool.getIntentFacts = " + appPool.getIntentFacts)
        //System.out.println(" compPool.getIntentFacts before merge with appPool = " + compPool(ep).getIntentFacts)
        compPool(ep).merge(appPool)
        //System.out.println(" compPool.getIntentFacts after merge with appPool = " + compPool(ep).getIntentFacts)
        val initialfacts = AndroidRFAConfig.getInitialFactsForMainEnvironment(ep)
        val receivedIntentFacts = compPool(ep).getIntentFacts.getOrElse(ep, Set())
        //System.out.println(" receivedIntentFacts = " + receivedIntentFacts)
        val (idfg, irfaResult) = AndroidReachingFactsAnalysisExtended(ep, idfgMap(ep), irfaMap(ep), initialfacts ++ receivedIntentFacts, new ClassLoadManager, timer)
        idfgMap +=(ep->idfg)
        irfaMap +=(ep->irfaResult)
        compPool += (ep->irfaResult.getExtraInfo)
        if(appPool.hasLessStaticFactsThan(compPool(ep))){
          worklist ++= entryPoints
          appPool.mergeStaticFacts(compPool(ep))
        }
        if(appPool.hasLessIntentFactsThan(compPool(ep))){
          worklist ++= appPool.findIntentDestComp(compPool(ep))
          appPool.mergeIntentFacts(compPool(ep))
        }
        if(appPool.hasLessRpcFactsThan(compPool(ep))){
          worklist ++= entryPoints
          appPool.mergeRpcData(compPool(ep))
        }
        System.out.println("at end of convergence loop: irfaResult.getExtraInfo.getRpcData callfacts = " + 
            irfaResult.getExtraInfo.getRpcData.getCallersByCallee(irfaResult.getExtraInfo.getRpcData.getCalleeCallers.keySet.head).head.callFacts)
        System.out.println(" and retfacts = " + 
            irfaResult.getExtraInfo.getRpcData.getCallersByCallee(irfaResult.getExtraInfo.getRpcData.getCalleeCallers.keySet.head).head.retFacts)
  //      System.out.println(" compPool.getIntentFacts et end of while = " + compPool(ep).getIntentFacts)
  //      System.out.println(" appPool.getIntentFacts at end of while = " + appPool.getIntentFacts)
  //      System.out.println(" irfaResult.getExtraInfo.getStaticFacts = " + irfaResult.getExtraInfo.getStaticFacts())
      }
    }

    

//        
//      {if(parallel) entryPoints.par else entryPoints}.foreach{
//        ep =>              
//            val outputDir = AndroidGlobalConfig.amandroid_home + "/output"            
//            val dotDirFile = new File(outputDir + "/" + "toDot")
//            if(!dotDirFile.exists()) dotDirFile.mkdirs()           
//            val out = new PrintWriter(dotDirFile.getAbsolutePath + "/"+ ep.getName +"icfg.dot")
//            idfgMap(ep).icfg.toDot(out)
//            out.close()
//       
//            val irfaResDirFile = new File(outputDir + "/" + "irfaResult")
//            if(!irfaResDirFile.exists()) irfaResDirFile.mkdirs()
//            val irfaOut = new PrintWriter(irfaResDirFile.getAbsolutePath + "/"+ ep.getName + "irfaRes.txt")
//            irfaOut.print(irfaMap(ep).toString())
//            irfaOut.close()
//        
//            msg_critical(TITLE,"--------------------------icfg and irfaResult are stored in file --------------")
//            AppCenter.addIDFG(ep.getDeclaringRecord, idfgMap(ep)) 
//            msg_critical(TITLE, "processed-->" + idfgMap(ep).icfg.getProcessed.size)              
//      } 
//    }
    
    val headComp = entryPoints.head // this is only a representative component; nothing special
    val appIdfg = idfgMap(headComp)
    msg_critical(TITLE, "appIdfg icfg nodes prior num = " + appIdfg.icfg.nodes.size)   
    entryPoints.map {
      ep =>
        if(ep != headComp){            
          appIdfg.merge(idfgMap(ep))           
          msg_critical(TITLE, "appIdfg icfg nodes post-merge num = " + appIdfg.icfg.nodes.size)          
        }            
    }
    appIdfg
   }
}

object AndroidEntryPointConstants {
  final val ACTIVITY_CLASS = "android.app.Activity"
  final val SERVICE_CLASS = "android.app.Service"
  final val BROADCAST_RECEIVER_CLASS = "android.content.BroadcastReceiver"
  final val CONTENT_PROVIDER_CLASS = "android.content.ContentProvider"
  final val APPLICATION_CLASS = "[|android:app:Application|]"
  
  final val APPLICATION_ONCREATE = "onCreate:()V"
  final val APPLICATION_ONTERMINATE = "onTerminate()V"
    
  final val ACTIVITY_ONCREATE = "onCreate:(Landroid/os/Bundle;)V"
  final val ACTIVITY_ONSTART = "onStart:()V"
  final val ACTIVITY_ONRESTOREINSTANCESTATE = "onRestoreInstanceState:(Landroid/os/Bundle;)V"
  final val ACTIVITY_ONPOSTCREATE = "onPostCreate:(Landroid/os/Bundle;)V"
  final val ACTIVITY_ONRESUME = "onResume:()V"
  final val ACTIVITY_ONPOSTRESUME = "onPostResume:()V"
  final val ACTIVITY_ONCREATEDESCRIPTION = "onCreateDescription:()Ljava/lang/CharSequence;"
  final val ACTIVITY_ONSAVEINSTANCESTATE = "onSaveInstanceState:(Landroid/os/Bundle;)V"
  final val ACTIVITY_ONPAUSE = "onPause:()V"
  final val ACTIVITY_ONSTOP = "onStop:()V"
  final val ACTIVITY_ONRESTART = "onRestart:()V"
  final val ACTIVITY_ONDESTROY = "onDestroy:()V"
  
  final val SERVICE_ONCREATE = "onCreate:()V"
  final val SERVICE_ONSTART1 = "onStart:(Landroid/content/Intent;I)V"
  final val SERVICE_ONSTART2 = "onStartCommand:(Landroid/content/Intent;II)I"
  final val SERVICE_ONBIND = "onBind:(Landroid/content/Intent;)Landroid/os/IBinder;"
  final val SERVICE_ONREBIND = "onRebind:(Landroid/content/Intent;)V"
  final val SERVICE_ONUNBIND = "onUnbind:(Landroid/content/Intent;)Z"
  final val SERVICE_ONDESTROY = "onDestroy:()V"
  
  final val BROADCAST_ONRECEIVE = "onReceive:(Landroid/content/Context;Landroid/content/Intent;)V"
  
  final val CONTENTPROVIDER_ONCREATE = "onCreate:()Z"
  
  final val INTENT_NAME = "android.content.Intent"
  final val ACTIVITY_SETINTENT_SIG = "Landroid/app/Activity;.setIntent:(Landroid/content/Intent;)V"
  
  private final val applicationMethods = List(APPLICATION_ONCREATE, APPLICATION_ONTERMINATE)
  private final val activityMethods = List(ACTIVITY_ONCREATE, ACTIVITY_ONDESTROY, ACTIVITY_ONPAUSE,
    ACTIVITY_ONRESTART, ACTIVITY_ONRESUME, ACTIVITY_ONSTART, ACTIVITY_ONSTOP,
    ACTIVITY_ONSAVEINSTANCESTATE, ACTIVITY_ONRESTOREINSTANCESTATE,
    ACTIVITY_ONCREATEDESCRIPTION, ACTIVITY_ONPOSTCREATE, ACTIVITY_ONPOSTRESUME)
  private final val serviceMethods = List(SERVICE_ONCREATE, SERVICE_ONDESTROY, SERVICE_ONSTART1,
    SERVICE_ONSTART2, SERVICE_ONBIND, SERVICE_ONREBIND, SERVICE_ONUNBIND)
  private final val broadcastMethods = List(BROADCAST_ONRECEIVE)
  private final val contentproviderMethods = List(CONTENTPROVIDER_ONCREATE)
  
  def getApplicationLifecycleMethods() : List[String] = applicationMethods
  
  def getActivityLifecycleMethods() : List[String] = activityMethods
  
  def getServiceLifecycleMethods() : List[String] = serviceMethods
  
  def getBroadcastLifecycleMethods() : List[String] = broadcastMethods
  
  def getContentproviderLifecycleMethods() : List[String] = contentproviderMethods
}