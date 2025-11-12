set Meet; 
set Person; 
set Cuisines; 
set Restaurants;

param Avail{Person, Meet};  
param Cusin_pref{Person, Cuisines}; 
 
param PricePM{Person}; 
 
param TimesMeetP{Person}; 
set Week; 
param RestPrice{Restaurants};
 
param RestCuisines{Restaurants, Cuisines}; 

param RestRating{Restaurants};  

var whoGO{Person, Meet} binary; 
var whenGO{Meet} binary;
var whereGO{Meet, Restaurants} binary; 

var meetingPairs{Person, Person, Meet} binary;
set MinPrice{meet}; 

maximize Obj:
    sum {m in Meet, r in Restaurants}
        whereGO[m, r] * (RestRating[r] / 5) * 
        sum {p in Person, c in Cuisines}
            whoGO[p, m] * Cusin_pref[p, c] * RestCuisines[r, c];

subject to pricePerPerson{p in Person, m in Meet, r in Restaurants}: 
	whereGo[m,r] * RestPrice[r] <= MinPrice[m] + 10; 
	
subject to defMinPrice{m in Meet, p in Person}:
	MinPrice[m] >= whoGO[p,m] * PricePM; 
	
subject to TotalPrice{p in Person}: 
	TotalPrice >= sum{m in Meet} sum{r in Restaurants} whereGo[r,m]

subject to PickFriSat{w in Week}: 
	whenGO[3*w-2] + whenGO[3*w-1] + whenGO[3*w] <= 1; 


subject to eightTimesSemester: 
		sum{i in Meet} whenGO[i] <= 8; 

# what it means to choose not to go to restrant
subject to NoWhoGo{m in Meet, p in Person}: 
	whenGO[m] >= whoGO[p,m];

subject to NoWhereGo{m in Meet, p in Restaurants}:
	whenGO[m] >= whereGO[m,p];

	
 
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
