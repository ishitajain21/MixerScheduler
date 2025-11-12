# Currently maximize cuisine preference

set Meet; 
set Person; 
set Cuisines; 
set Restaurants;

param Avail{Person, Meet};  
param Cusin_pref{Person, Cuisines}; 
 
param PricePM{Person}; 
 
param TimesMeetP{Person}; 
 
param RestPrice{Restaurants};
 
param RestCuisines{Restaurants, Cuisines}; 

param RestRating{Restaurants};  
var whoGO{Person, Meet} binary; 

var whereGO{Meet, Restaurants} binary; 

var meetingPairs{Person, Person, Meet} binary; 

maximize Obj:
    sum {m in Meet, r in Restaurants}
        whereGO[m, r] *
        sum {p in Person, c in Cuisines}
            whoGO[p, m] * Cusin_pref[p, c] * RestCuisines[r, c];

 
subject to Availibility{i in Person, m in Meet}:
	whoGO[i,m] <= Avail[i,m];
  
 subject to OneRestaurantPerMeet{m in Meet}:
    sum {r in Restaurants} whereGO[m, r] = 1;

 
subject to MeetingPair0{i in Person, m in Meet}:
	meetingPairs[i,i,m] = whoGO[i,m]; 

subject to MeetingPair1{i in Person, j in Person, m in Meet: i <> j}: 
	meetingPairs[i,j,m] <= whoGO[j,m];
	
subject to MeetingPair2{i in Person, j in Person, m in Meet: i <> j}:
	meetingPairs[i,j,m] <= whoGO[i,m];
	
subject to MeetingPair3{i in Person, j in Person, m in Meet: i <> j}:
	meetingPairs[i,j,m] >= whoGO[i,m] + whoGO[j,m] - 1; 
