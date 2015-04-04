/*
Copyright (c) 2013-2014 Fengguo Wei & Sankardas Roy, Kansas State University.        
All rights reserved. This program and the accompanying materials      
are made available under the terms of the Eclipse Public License v1.0 
which accompanies this distribution, and is available at              
http://www.eclipse.org/legal/epl-v10.html                             
*/
package org.sireum.amandroid.alir.reachingFactsAnalysis

import org.sireum.util._
import org.sireum.jawa.JawaProcedure
import org.sireum.amandroid.alir.model.AndroidModelCallHandler
import org.sireum.jawa.alir.reachingFactsAnalysis.RFAFact
import org.sireum.jawa.alir.Context
import org.sireum.jawa.alir.interProcedural.ExtraInfo
import org.sireum.jawa.JawaRecord
import org.sireum.jawa.alir.controlFlowGraph.InterproceduralControlFlowGraph
import org.sireum.jawa.alir.controlFlowGraph.CGNode
import org.sireum.jawa.MessageCenter._
import org.sireum.jawa.ClassLoadManager
import org.sireum.jawa.util.TimeOutException
import org.sireum.amandroid.AndroidGlobalConfig
import java.io.File
import java.io.PrintWriter
import org.sireum.amandroid.AppCenter
import org.sireum.jawa.alir.dataDependenceAnalysis.InterproceduralDataDependenceAnalysis
import org.sireum.amandroid.alir.taintAnalysis
/**
 * @author <a href="mailto:fgwei@k-state.edu">Fengguo Wei</a>
 * @author <a href="mailto:sroy@k-state.edu">Sankardas Roy</a>
 */ 
object AndroidReachingFactsAnalysisHelper {
	private final val TITLE = "AndroidReachingFactsAnalysisHelper"
	def isModelCall(calleeProc : JawaProcedure) : Boolean = {
    AndroidModelCallHandler.isModelCall(calleeProc)
  }
  
  def doModelCall(s : ISet[RFAFact], calleeProc : JawaProcedure, args : List[String], retVars : Seq[String], currentContext : Context) : ISet[RFAFact] = {
    AndroidModelCallHandler.doModelCall(s, calleeProc, args, retVars, currentContext)
  }
  
  def isICCCall(calleeProc : JawaProcedure) : Boolean = {
    AndroidModelCallHandler.isICCCall(calleeProc)
  }
  
  def doICCCall(s : ISet[RFAFact], calleeProc : JawaProcedure, args : List[String], retVars : Seq[String], currentContext : Context) : (ISet[RFAFact], ISet[JawaProcedure]) = {
    AndroidModelCallHandler.doICCCall(s, calleeProc, args, retVars, currentContext)
  }
  
  def doIrfaMerge(entryPoints:Set[JawaProcedure], parallel: Boolean) ={
    
    //initialize each component's sharable local facts (compPool) and the appPool           
    var icfgMap : IMap[JawaProcedure, InterproceduralControlFlowGraph[CGNode]] = Map()
    var irfaResultMap : IMap[JawaProcedure, AndroidReachingFactsAnalysisExtended.Result] = Map()
     
    entryPoints.map { 
      ep => 
        msg_critical(TITLE, "--------------Component " + ep + "--------------")                                                
        val initialfacts = AndroidRFAConfig.getInitialFactsForMainEnvironment(ep)
        val (icfg, irfaResult) = AndroidReachingFactsAnalysisExtended(ep, null, null, initialfacts, new ClassLoadManager)
        icfgMap +=(ep -> icfg)
        irfaResultMap += (ep -> irfaResult)                    
     }    
    //inter-component merging starts
    var converged = false
    var appPool : ExtraInfo[RFAFact] = new ExtraInfo[RFAFact]
    var compPool : IMap[JawaProcedure, ExtraInfo[RFAFact]] = Map()
    while(converged != true){
      converged = true
      entryPoints.map {
        ep =>
          compPool +=(ep -> irfaResultMap(ep).getExtraInfo)
          appPool.merge(compPool(ep))
      }
                
        {if(parallel) entryPoints.par else entryPoints}.foreach{
          ep =>

              msg_critical(TITLE, "--------------Component " + ep + "--------------")              
              compPool += (ep -> compPool(ep).merge(appPool))
              
              val initialfacts = AndroidRFAConfig.getInitialFactsForMainEnvironment(ep)
              val receivedIntentFacts = appPool.getIntentFacts.getOrElse(ep, Set())
              val preIcfg = icfgMap(ep)
              val preIrfaResult = irfaResultMap(ep)
              System.out.println("received intent facts = " + receivedIntentFacts)
              val (icfg, irfaResult) = AndroidReachingFactsAnalysisExtended(ep, preIcfg, preIrfaResult, initialfacts ++ receivedIntentFacts, new ClassLoadManager)              
              icfgMap +=(ep -> icfg)
              irfaResultMap += (ep -> irfaResult)
              if(!irfaResult.getExtraInfo.diffStaticFacts(preIrfaResult.getExtraInfo).isEmpty || !irfaResult.getExtraInfo.diffIntentFacts(preIrfaResult.getExtraInfo).isEmpty) {
                converged = false
                System.out.println(" irfaResult.getExtraInfo.getIntentFacts = " + irfaResult.getExtraInfo.getIntentFacts)
                System.out.println(" preirfaResult.getExtraInfo.getIntentFacts = " + preIrfaResult.getExtraInfo.getIntentFacts)
                System.out.println(" irfaResult.getExtraInfo.diffIntentFacts(preIrfaResult.getExtraInfo) = " + irfaResult.getExtraInfo.diffIntentFacts(preIrfaResult.getExtraInfo))
              }              
              System.out.println("icfg and irfaRes computed. " + " holeNodes num = " + irfaResult.getExtraInfo.getHoleNodes().size)
              System.out.println(" irfaRes extra facts = " + irfaResult.getExtraInfo.getStaticFacts().toString)
              System.out.println(" irfaRes sent intent facts = " + irfaResult.getExtraInfo.getIntentFacts.toString)
        }
        
        {if(parallel) entryPoints.par else entryPoints}.foreach{
          ep =>              
              val outputDir = AndroidGlobalConfig.amandroid_home + "/output"            
              val dotDirFile = new File(outputDir + "/" + "toDot")
              if(!dotDirFile.exists()) dotDirFile.mkdirs()           
              val out = new PrintWriter(dotDirFile.getAbsolutePath + "/"+ ep.getName +"icfg.dot")
              icfgMap(ep).toDot(out)
              out.close()
         
              val irfaResDirFile = new File(outputDir + "/" + "irfaResult")
              if(!irfaResDirFile.exists()) irfaResDirFile.mkdirs()
              val irfaOut = new PrintWriter(irfaResDirFile.getAbsolutePath + "/"+ ep.getName + "irfaRes.txt")
              irfaOut.print(irfaResultMap(ep).toString())
              irfaOut.close()
          
              msg_critical(TITLE,"--------------------------icfg and irfaResult are stored in file --------------")
              AppCenter.addInterproceduralReachingFactsAnalysisResult(ep.getDeclaringRecord, icfgMap(ep), irfaResultMap(ep))
              msg_critical(TITLE, "processed-->" + icfgMap(ep).getProcessed.size)              
            } 
        }
    
    val headComp = entryPoints.head // this is only a representative component; nothing special
    val appCg = icfgMap(headComp)
    msg_critical(TITLE, "appCg nodes prior num = " + appCg.nodes.size)
    val appIrfaResult = irfaResultMap(headComp)
    msg_critical(TITLE, "appIrfa nodes prior num = " + appIrfaResult.getEntrySetMap.keySet.size)
    entryPoints.map {
        ep =>
          if(ep != headComp){            
            appCg.merge(icfgMap(ep))
            appIrfaResult.merge(irfaResultMap(ep))
            msg_critical(TITLE, "appCg nodes merge-post num = " + appCg.nodes.size)
            msg_critical(TITLE, "appIrfa nodes merge-post num = " + appIrfaResult.getEntrySetMap.keySet.size)
          }            
    }
    (appCg, appIrfaResult)
    //val iddResult = InterproceduralDataDependenceAnalysis(appCg, appIrfaResult)
    //AppCenter.addInterproceduralDataDependenceAnalysisResult(ep.getDeclaringRecord, iddResult) 
    
   }
 
}