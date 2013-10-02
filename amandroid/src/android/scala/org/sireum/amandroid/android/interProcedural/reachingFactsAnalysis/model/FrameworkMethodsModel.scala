package org.sireum.amandroid.android.interProcedural.reachingFactsAnalysis.model

import org.sireum.amandroid.interProcedural.Context
import org.sireum.util._
import org.sireum.amandroid.interProcedural.reachingFactsAnalysis.RFAFact
import org.sireum.amandroid._
import org.sireum.amandroid.interProcedural.reachingFactsAnalysis.RFAInstance
import org.sireum.amandroid.interProcedural.reachingFactsAnalysis.VarSlot
import org.sireum.amandroid.interProcedural.reachingFactsAnalysis.RFAPointStringInstance
import org.sireum.amandroid.interProcedural.reachingFactsAnalysis.ReachingFactsAnalysisHelper
import org.sireum.amandroid.interProcedural.reachingFactsAnalysis.RFAConcreteStringInstance
import org.sireum.amandroid.interProcedural.reachingFactsAnalysis.RFAPointStringInstance
import org.sireum.amandroid.android.AndroidConstants
import org.sireum.amandroid.interProcedural.reachingFactsAnalysis.RFAUnknownInstance
import org.sireum.amandroid.android.AppCenter
import org.sireum.amandroid.android.parser.IntentFilterDataBase
import org.sireum.amandroid.android.parser.IntentFilter
import org.sireum.amandroid.interProcedural.reachingFactsAnalysis.FieldSlot
import org.sireum.amandroid.interProcedural.reachingFactsAnalysis.RFANullInstance

object FrameworkMethodsModel {
  val DEBUG = true
	def isFrameworkMethods(p : AmandroidProcedure) : Boolean = {
	  val contextRec = Center.resolveRecord("[|android:content:Context|]", Center.ResolveLevel.BODIES)
	  if(Center.getRecordHierarchy.isRecordRecursivelySubClassOfIncluding(p.getDeclaringRecord, contextRec))
		  p.getSubSignature match{
		    case "setContentView:(I)V" |
		    		 "registerReceiver:(Landroid/content/BroadcastReceiver;Landroid/content/IntentFilter;)Landroid/content/Intent;" |
		    		 "registerReceiver:(Landroid/content/BroadcastReceiver;Landroid/content/IntentFilter;Ljava/lang/String;Landroid/os/Handler;)Landroid/content/Intent;" |
		         "getApplication:()Landroid/app/Application;" |
		         "getSystemService:(Ljava/lang/String;)Ljava/lang/Object;" |
		         "getBaseContext:()Landroid/content/Context;" |
		         "getApplicationContext:()Landroid/content/Context;"=> true
		    case _ => false
		  }
	  else false
	}
	
	def doFrameworkMethodsModelCall(s : ISet[RFAFact], p : AmandroidProcedure, args : List[String], retVarOpt : Option[String], currentContext : Context) : ISet[RFAFact] = {
	  var newFacts = isetEmpty[RFAFact]
	  p.getSubSignature match{
	    case "setContentView:(I)V" =>
	    case "registerReceiver:(Landroid/content/BroadcastReceiver;Landroid/content/IntentFilter;)Landroid/content/Intent;" =>
	      require(retVarOpt.isDefined)
	      newFacts ++= registerReceiver(s, args, retVarOpt.get, currentContext)
	    case "registerReceiver:(Landroid/content/BroadcastReceiver;Landroid/content/IntentFilter;Ljava/lang/String;Landroid/os/Handler;)Landroid/content/Intent;" => 
	      require(retVarOpt.isDefined)
	      newFacts ++= registerReceiver(s, args, retVarOpt.get, currentContext)
	    case "getApplication:()Landroid/app/Application;" =>
	      require(retVarOpt.isDefined)
	      ReachingFactsAnalysisHelper.getReturnFact(NormalType("[|android:app:Application|]", 0), retVarOpt.get, currentContext) match{
	        case Some(f) => newFacts += f
	        case None =>
	      }
	    case "getSystemService:(Ljava/lang/String;)Ljava/lang/Object;" =>
	      require(retVarOpt.isDefined)
	      newFacts ++= getSystemService(s, args, retVarOpt.get, currentContext)
	    case "getBaseContext:()Landroid/content/Context;" =>
	      require(retVarOpt.isDefined)
	      ReachingFactsAnalysisHelper.getReturnFact(NormalType("[|android:app:ContextImpl|]", 0), retVarOpt.get, currentContext) match{
	        case Some(f) => newFacts += f
	        case None =>
	      }
	    case "getApplicationContext:()Landroid/content/Context;"=>
	      require(retVarOpt.isDefined)
	      ReachingFactsAnalysisHelper.getReturnFact(NormalType("[|android:app:Application|]", 0), retVarOpt.get, currentContext) match{
	        case Some(f) => newFacts += f
	        case None =>
	      }
	    case _ =>
	  }
	  if(newFacts.isEmpty){
	    if(retVarOpt.isDefined){
	      val slot = VarSlot(retVarOpt.get)
        val value = RFAUnknownInstance(currentContext)
        newFacts += RFAFact(slot, value)
	    }
	  }
	  s ++ newFacts
	}
	
	private def registerReceiver(s : ISet[RFAFact], args : List[String], retVar : String, currentContext : Context) : ISet[RFAFact] ={
	  var result = isetEmpty[RFAFact]
	  val factMap = ReachingFactsAnalysisHelper.getFactMap(s)
    require(args.size > 2)
    val thisSlot = VarSlot(args(0))
    val thisValue = factMap.getOrElse(thisSlot, isetEmpty)
    val receiverSlot = VarSlot(args(1))
	  val receiverValue = factMap.getOrElse(receiverSlot, isetEmpty)
	  val filterSlot = VarSlot(args(2))
	  val filterValue = factMap.getOrElse(filterSlot, isetEmpty)
	  val iDB = new IntentFilterDataBase
	  receiverValue.foreach{
	    rv =>
	      val intentF = new IntentFilter(rv.getType.name)
	      filterValue.foreach{
	        fv =>
	          val mActionsSlot = FieldSlot(fv, AndroidConstants.INTENTFILTER_ACTIONS)
	          println(factMap)
	          val mActionsValue = factMap.getOrElse(mActionsSlot, isetEmpty)
	          mActionsValue.foreach{
	            mav =>
	              mav match{
			            case cstr @ RFAConcreteStringInstance(text, c) =>
			              intentF.addAction(text)
			            case pstr @ RFAPointStringInstance(c) => 
			              if(DEBUG)
			              	System.err.println("Register IntentFilter actions use point string: " + pstr)
			            case n @ RFANullInstance(c) =>
			            case _ => throw new RuntimeException("unexpected instance type: " + mav)
			          }
	          }
	          val mCategoriesSlot = FieldSlot(fv, AndroidConstants.INTENTFILTER_CATEGORIES)
	          val mCategoriesValue = factMap.getOrElse(mCategoriesSlot, isetEmpty)
	          mCategoriesValue.foreach{
	            mav =>
	              mav match{
			            case cstr @ RFAConcreteStringInstance(text, c) =>
			              intentF.addCategory(text)
			            case pstr @ RFAPointStringInstance(c) => 
			              if(DEBUG)
			              	System.err.println("Register IntentFilter categories use point string: " + pstr)
			            case n @ RFANullInstance(c) =>
			            case _ => throw new RuntimeException("unexpected instance type: " + mav)
			          }
	          }
	      }
	      iDB.updateIntentFmap(intentF)
	  }
	  AppCenter.updateIntentFilterDB(iDB)
	  println("intentfilter database: " + AppCenter.getIntentFilterDB)
	  isetEmpty
	}
	
	private def getSystemService(s : ISet[RFAFact], args : List[String], retVar : String, currentContext : Context) : ISet[RFAFact] ={
	  var result = isetEmpty[RFAFact]
	  val factMap = ReachingFactsAnalysisHelper.getFactMap(s)
    require(args.size >1)
    val paramSlot = VarSlot(args(1))
	  val paramValue = factMap.getOrElse(paramSlot, isetEmpty)
	  paramValue.foreach{
	    str =>
	      str match{
			    case cstr @ RFAConcreteStringInstance(text, c) =>
			      text match{
			        case AndroidConstants.WINDOW_SERVICE => println("Get window service in " + currentContext)
							case AndroidConstants.LAYOUT_INFLATER_SERVICE => println("Get layout_inflater service in " + currentContext)
							case AndroidConstants.ACTIVITY_SERVICE => println("Get activity service in " + currentContext)
							case AndroidConstants.POWER_SERVICE => println("Get power service in " + currentContext)
							case AndroidConstants.ALARM_SERVICE => println("Get alarm service in " + currentContext)
							case AndroidConstants.NOTIFICATION_SERVICE => println("Get notification service in " + currentContext)
							case AndroidConstants.KEYGUARD_SERVICE => println("Get keyguard service in " + currentContext)
							case AndroidConstants.LOCATION_SERVICE => println("Get location service in " + currentContext)
							case AndroidConstants.SEARCH_SERVICE => println("Get search service")
							case AndroidConstants.VIBRATOR_SERVICE => println("Get vibrator service in " + currentContext)
							case AndroidConstants.CONNECTIVITY_SERVICE => println("Get connection service in " + currentContext)
							case AndroidConstants.WIFI_SERVICE => println("Get wifi service")
							case AndroidConstants.INPUT_METHOD_SERVICE => println("Get input_method service in " + currentContext)
							case AndroidConstants.UI_MODE_SERVICE => println("Get uimode service in " + currentContext)
							case AndroidConstants.DOWNLOAD_SERVICE => println("Get download service in " + currentContext)
							case _ => System.err.println("Given service does not exist: " + cstr)
			      }
			    case pstr @ RFAPointStringInstance(c) => System.err.println("Get system service use point string: " + pstr)
			    case _ => throw new RuntimeException("unexpected instance type: " + str)
	      }
	  }
	  result
	}
}