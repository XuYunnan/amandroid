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
      System.out.println(" irfaResult.getExtraInfo.getIntentFacts at end of convergence loop = " + irfaResult.getExtraInfo.getIntentFacts)
//      System.out.println(" compPool.getIntentFacts et end of while = " + compPool(ep).getIntentFacts)
//      System.out.println(" appPool.getIntentFacts at end of while = " + appPool.getIntentFacts)
//      System.out.println(" irfaResult.getExtraInfo.getStaticFacts = " + irfaResult.getExtraInfo.getStaticFacts())
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