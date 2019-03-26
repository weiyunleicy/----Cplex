/*********************************************
 * OPL 12.6.1.0 Model
 * Author: 01369515
 * Creation Date: 2019-1-10 at ÉÏÎç10:49:16
 *********************************************/

{string} ZzcList=...;//Distribution Centre List

tuple ZzcODAptWt {//Define the airport routes that the distribution centre OD can pick && the weight of the d-c OD 
   string Szzc;  
   string Dzzc;
   string Sapt;	
   string Dapt;
   float Wt;
   int Cc;
   int Cr;
}

tuple AirportState {  //Define the airports' state about now or update
   key string Apt;	
   int Cc;
   int Cr;	
   string State;	
}
tuple ZzcApt {//Define which airport a distribution centre can pick 
   key string Zzc;		
   key string Apt;	
}

tuple ZzcOd {//Define the distribution OD
   key string Szzc;		
   key string Dzzc;	
}

{ZzcOd} ZzcOdList=...;
{ZzcApt} ZzcAptList=...;
{ZzcODAptWt} ZzcOdAptWt=...;  
{AirportState} Airports = ...;

dvar boolean Sselect[ZzcOdAptWt]; //decide if the distribution OD will pick this airport route
dvar boolean Select[ZzcAptList];  //decide if the distribution will pick this airport
dvar boolean Apt[Airports];//decide if the airport will be pick

dvar boolean AptC[Airports];

dexpr float Swt[i in ZzcOdAptWt]=Sselect[i]*i.Wt;//the selected weight 

dexpr float SwtAm[i in ZzcOdAptWt]=Sselect[i]*i.Cc*i.Wt;//the selected nextday morning weight 
dexpr float SwtPm[i in ZzcOdAptWt]=Sselect[i]*i.Wt;//the selected nextday weight 

dexpr float TotalWt=sum(i in ZzcOdAptWt)Swt[i];

dexpr float TotalSwtpm=sum(i in Airports)Apt[i]*i.Cr*9.8;//punishment of nextday
dexpr float TotalSwtam=sum(i in Airports)Apt[i]*i.Cc*9.8;//punishment of nextday morning
/*
dexpr float TotalSwt=sum(i in Airports)Apt[i]*9.8;//punishment of openning new apt*/

maximize TotalWt-TotalSwtpm-TotalSwtam;

subject to{
	forall(z in ZzcOdList)
	  ctZzcOdPickOneRoute: //every distribution centre OD can pick less than one Airport route
		sum(i in ZzcOdAptWt:i.Szzc==z.Szzc&&i.Dzzc==z.Dzzc) Sselect[i]<=1;
	
	forall(i in ZzcList)
	  ctSzzcAptPickOne://every distribution centre can pick less than one airport
	    sum(z in ZzcAptList:z.Zzc==i)Select[z]<=1;	
	
	forall(x in ZzcAptList,i in Airports:x.Apt==i.Apt)
	  ctZzcApt://only when the airport is selected can the distribution centre pick the airport
		Select[x]<=Apt[i];
	
	forall( z in ZzcOdAptWt,i in ZzcAptList,j in ZzcAptList:i.Zzc==z.Szzc&&j.Zzc==z.Dzzc&&i.Apt==z.Sapt&&j.Apt==z.Dapt)
	  ctRelateOdAndZzcApt://define the connecttion about the ZzcAptList and the ZzcOdAptWt data
		Sselect[z]>=Select[i]+Select[j]-1;
		
	forall(z in ZzcOdAptWt,i in ZzcAptList:i.Zzc==z.Szzc&&i.Apt==z.Sapt)	//2min
	  ctSzzcApt://only when the distribution centre pick the airport to gather can the OD pick the route
		Sselect[z]<=Select[i];
		
	forall(z in ZzcOdAptWt,i in ZzcAptList:i.Zzc==z.Dzzc&&i.Apt==z.Dapt)	
	  ctDzzcApt://only when the distribution centre pick the airport to distribute can the OD pick the route
		Sselect[z]<=Select[i];
	 
	forall(z in Airports:z.State=="updata")//take 44min
	  ctAptWtLimit://the standard that an update airport can be opened is its in-out weight more than 20T
		sum(i in ZzcOdAptWt:i.Sapt==z.Apt)Swt[i]+sum(x in ZzcOdAptWt:x.Dapt==z.Apt)Swt[x]>=19.6*Apt[z];
	
	forall(z in Airports:z.State=="updata")//an update apt can be opened when its 1200 more than 10 or its 1800 more then 20 
	  ctAmAptWtLimit://the standard that an update airport can be opened is its nextday morning weight more than 4.9T
		sum(i in ZzcOdAptWt:i.Sapt==z.Apt)SwtAm[i]+sum(x in ZzcOdAptWt:x.Dapt==z.Apt)SwtAm[x]>=9.8*(AptC[z]+Apt[z]-1);
	forall(z in Airports:z.State=="updata")
	  ctPmAptWtLimit://the standard that an update airport can be opened is its nextday weight more than 9.8T
		sum(i in ZzcOdAptWt:i.Sapt==z.Apt)SwtPm[i]+sum(x in ZzcOdAptWt:x.Dapt==z.Apt)SwtPm[x]>=19.6*(1-AptC[z]+Apt[z]-1);
	
	// one-way weight more than 8.8(less than 11.2--80% of B737's capacity)
	forall(z in Airports:z.State=="updata")
	  ctAptWtLimit2:
		sum(i in ZzcOdAptWt:i.Sapt==z.Apt)Swt[i]>=8.4*Apt[z];
	forall(z in Airports:z.State=="updata")
	  ctAptWtLimit3:
		sum(i in ZzcOdAptWt:i.Dapt==z.Apt)Swt[i]>=8.4*Apt[z];
		
	forall(z in Airports:z.State=="now")
	  ctAptMustSelect://the airport must be selected if it has been already opened
	    Apt[z]==1;
	
	/*ctAptQuantity: //Airport quantity
	  sum(z in Airports) Apt[z]<=45;
	*/
 }	  
 
 //Write the result into SQLsever
   tuple Sselect_Result{
   string Szzc;  
   string Dzzc;
   string Sapt;	
   string Dapt;
   float Wt;
   int Cc;
   int Cr;
   int Sselect;
}
{Sselect_Result} Sselect_Result_List={<s.Szzc,s.Dzzc,s.Sapt,s.Dapt,s.Wt,s.Cc,s.Cr,Sselect[s]>|s in ZzcOdAptWt:Sselect[s]==1};
	  
	