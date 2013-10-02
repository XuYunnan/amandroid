package org.sireum.amandroid.android.interProcedural.reachingFactsAnalysis.model

import org.sireum.amandroid._
import org.sireum.util._
import org.sireum.amandroid.interProcedural.reachingFactsAnalysis.RFAFact
import org.sireum.amandroid.interProcedural.Context
import org.sireum.amandroid.interProcedural.reachingFactsAnalysis._
import org.sireum.amandroid.android.AndroidConstants

object IntentFilterModel {
  val DEBUG = true
	def isIntentFilter(r : AmandroidRecord) : Boolean = r.getName == AndroidConstants.INTENTFILTER
	  
	def doIntentFilterCall(s : ISet[RFAFact], p : AmandroidProcedure, args : List[String], retVarOpt : Option[String], currentContext : Context) : ISet[RFAFact] = {
	  var newFacts = isetEmpty[RFAFact]
	  var delFacts = isetEmpty[RFAFact]
	  p.getSignature match{
	    case "[|Landroid/content/IntentFilter;.<clinit>:()V|]" =>  //static constructor
		  case "[|Landroid/content/IntentFilter;.<init>:()V|]" =>  //public constructor
		  case "[|Landroid/content/IntentFilter;.<init>:(Landroid/content/IntentFilter;)V|]" =>  //public constructor
		  case "[|Landroid/content/IntentFilter;.<init>:(Landroid/os/Parcel;)V|]" =>  //private constructor
		  case "[|Landroid/content/IntentFilter;.<init>:(Landroid/os/Parcel;Landroid/content/IntentFilter$1;)V|]" =>  //synthetic constructor
		  case "[|Landroid/content/IntentFilter;.<init>:(Ljava/lang/String;)V|]" =>  //public constructor
		    intentFilterInitWithAction(s, args, currentContext) match{case (n, d) => newFacts ++= n; delFacts ++= d}
		  case "[|Landroid/content/IntentFilter;.<init>:(Ljava/lang/String;Ljava/lang/String;)V|]" =>  //public constructor
		  case "[|Landroid/content/IntentFilter;.actionsIterator:()Ljava/util/Iterator;|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.addAction:(Ljava/lang/String;)V|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.addCategory:(Ljava/lang/String;)V|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.addDataAuthority:(Ljava/lang/String;Ljava/lang/String;)V|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.addDataPath:(Ljava/lang/String;I)V|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.addDataScheme:(Ljava/lang/String;)V|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.addDataType:(Ljava/lang/String;)V|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.addStringToSet:([Ljava/lang/String;Ljava/lang/String;[II)[Ljava/lang/String;|]" =>  //private static
		  case "[|Landroid/content/IntentFilter;.authoritiesIterator:()Ljava/util/Iterator;|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.categoriesIterator:()Ljava/util/Iterator;|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.countActions:()I|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.countCategories:()I|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.countDataAuthorities:()I|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.countDataPaths:()I|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.countDataSchemes:()I|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.countDataTypes:()I|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.create:(Ljava/lang/String;Ljava/lang/String;)Landroid/content/IntentFilter;|]" =>  //public static
		  case "[|Landroid/content/IntentFilter;.debugCheck:()Z|]" =>  //public
		  case "[|Landroid/content/IntentFilter;.describeContents:()I|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.dump:(Landroid/util/Printer;Ljava/lang/String;)V|]" =>  //public
		  case "[|Landroid/content/IntentFilter;.findMimeType:(Ljava/lang/String;)Z|]" =>  //private final
		  case "[|Landroid/content/IntentFilter;.findStringInSet:([Ljava/lang/String;Ljava/lang/String;[II)I|]" =>  //private static
		  case "[|Landroid/content/IntentFilter;.getAction:(I)Ljava/lang/String;|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.getCategory:(I)Ljava/lang/String;|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.getDataAuthority:(I)Landroid/content/IntentFilter$AuthorityEntry;|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.getDataPath:(I)Landroid/os/PatternMatcher;|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.getDataScheme:(I)Ljava/lang/String;|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.getDataType:(I)Ljava/lang/String;|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.getPriority:()I|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.hasAction:(Ljava/lang/String;)Z|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.hasCategory:(Ljava/lang/String;)Z|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.hasDataAuthority:(Landroid/net/Uri;)Z|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.hasDataPath:(Ljava/lang/String;)Z|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.hasDataScheme:(Ljava/lang/String;)Z|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.hasDataType:(Ljava/lang/String;)Z|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.match:(Landroid/content/ContentResolver;Landroid/content/Intent;ZLjava/lang/String;)I|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.match:(Ljava/lang/String;Ljava/lang/String;Ljava/lang/String;Landroid/net/Uri;Ljava/util/Set;Ljava/lang/String;)I|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.matchAction:(Ljava/lang/String;)Z|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.matchCategories:(Ljava/util/Set;)Ljava/lang/String;|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.matchData:(Ljava/lang/String;Ljava/lang/String;Landroid/net/Uri;)I|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.matchDataAuthority:(Landroid/net/Uri;)I|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.pathsIterator:()Ljava/util/Iterator;|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.readFromXml:(Lorg/xmlpull/v1/XmlPullParser;)V|]" =>  //public
		  case "[|Landroid/content/IntentFilter;.removeStringFromSet:([Ljava/lang/String;Ljava/lang/String;[II)[Ljava/lang/String;|]" =>  //private static
		  case "[|Landroid/content/IntentFilter;.schemesIterator:()Ljava/util/Iterator;|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.setPriority:(I)V|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.typesIterator:()Ljava/util/Iterator;|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.writeToParcel:(Landroid/os/Parcel;I)V|]" =>  //public final
		  case "[|Landroid/content/IntentFilter;.writeToXml:(Lorg/xmlpull/v1/XmlSerializer;)V|]" =>  //public
	  }
	  if(newFacts.isEmpty){
	    if(retVarOpt.isDefined){
	      val slot = VarSlot(retVarOpt.get)
        val value = RFAUnknownInstance(currentContext)
        newFacts += RFAFact(slot, value)
	    }
	  }
	  s ++ newFacts -- delFacts
	}
  
  
	/**
	 * [|Landroid/content/IntentFilter;.<init>:(Ljava/lang/String;)V|]
	 */
	private def intentFilterInitWithAction(s : ISet[RFAFact], args : List[String], currentContext : Context) : (ISet[RFAFact], ISet[RFAFact]) = {
    val factMap = ReachingFactsAnalysisHelper.getFactMap(s)
    require(args.size >1)
    val thisSlot = VarSlot(args(0))
	  val thisValue = factMap.getOrElse(thisSlot, isetEmpty)
	  val actionSlot = VarSlot(args(1))
	  val actionValue = factMap.getOrElse(actionSlot, isetEmpty)
	  var newfacts = isetEmpty[RFAFact]
    var delfacts = isetEmpty[RFAFact]
	  thisValue.foreach{
	    tv =>
	      if(thisValue.size == 1){
	        for (rdf @ RFAFact(slot, _) <- s) {
		        //if it is a strong definition, we can kill the existing definition
		        if (FieldSlot(tv, AndroidConstants.INTENTFILTER_ACTIONS) == slot) {
		          delfacts += rdf
		        }
		      }
	      }
	      actionValue.foreach{
		      acStr =>
	          acStr match{
	            case cstr @ RFAConcreteStringInstance(text, c) =>
	              newfacts += RFAFact(FieldSlot(tv, AndroidConstants.INTENTFILTER_ACTIONS), cstr)
	            case pstr @ RFAPointStringInstance(c) => 
	              if(DEBUG)
	              	System.err.println("Init IntentFilter use point string: " + pstr)
	              newfacts += RFAFact(FieldSlot(tv, AndroidConstants.INTENTFILTER_ACTIONS), pstr)
	            case _ => throw new RuntimeException("unexpected instance type: " + acStr)
	          }
		    }
	  }
    (newfacts, delfacts)
  }
	
}