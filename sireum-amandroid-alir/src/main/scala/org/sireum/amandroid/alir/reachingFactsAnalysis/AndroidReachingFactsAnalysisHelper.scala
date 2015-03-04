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
              }              
              System.out.println("icfg and irfaRes computed. " + " holeNodes num = " + irfaResult.getExtraInfo.getHoleNodes().size)
              System.out.println(" irfaRes extra facts = " + irfaResult.getExtraInfo.getStaticFacts().toString)
              System.out.println(" irfaRes sent intent facts = " + irfaResult.getExtraInfo.getIntentFacts.toString)
//           
//              val outputDir = AndroidGlobalConfig.amandroid_home + "/output"            
//              val dotDirFile = new File(outputDir + "/" + "toDot")
//              if(!dotDirFile.exists()) dotDirFile.mkdirs()           
//              val out = new PrintWriter(dotDirFile.getAbsolutePath + "/"+ ep.getShortName +"icfg.dot")
//              icfg.toDot(out)
//              out.close()
//            
//              val out2 = new PrintWriter(dotDirFile.getAbsolutePath + "/" + ep.getShortName +"icfg2.dot")
//              icfg2.toDot(out2)
//              out2.close()
//            
//              val irfaResDirFile = new File(outputDir + "/" + "irfaResult")
//              if(!irfaResDirFile.exists()) irfaResDirFile.mkdirs()
//              val irfaOut = new PrintWriter(irfaResDirFile.getAbsolutePath + "/"+ ep.getShortName + "irfaRes.txt")
//              irfaOut.print(irfaResult.toString())
//              irfaOut.close()
//            
//              val irfaOut2 = new PrintWriter(irfaResDirFile.getAbsolutePath + "/"+ ep.getShortName + "irfaRes2.txt")
//              irfaOut2.print(irfaResult2.toString())
//              irfaOut2.close()
//            
//              msg_critical(TITLE,"--------------------------icfg and irfaResult are stored in file --------------")
//            
//            
//              AppCenter.addInterproceduralReachingFactsAnalysisResult(ep.getDeclaringRecord, icfg, irfaResult)
//              msg_critical(TITLE, "processed-->" + icfg.getProcessed.size)
//              val iddResult = InterproceduralDataDependenceAnalysis(icfg, irfaResult)
//              AppCenter.addInterproceduralDataDependenceAnalysisResult(ep.getDeclaringRecord, iddResult)
            } 
        }   
          
      }
  
}