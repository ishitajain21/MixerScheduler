set Meet;
set Person;
set Cuisines;
set Restaurants; 
set Week;

param Avail{Person, Meet};
param Cusin_pref{Person, Cuisines};

# slack params: 

param SlackTotSem; 
param SlackPerMeet;
param PplInRest;
param MeetingsPerSemPerPerson;
param multiObj;

param PricePM{Person};

param PricePS{Person};  

param RestPrice{Restaurants};

param RestCuisines{Restaurants, Cuisines};

param RestRating{Restaurants};

param Allergy{Restaurants, Person};
param Friend{Person, Person};
var MinPrice{Meet} >= 0;  
var TotalPrice >= 0;

var s{Person, Person} >= 0;
var whoGO{Person, Meet} binary;
var whenGO{Meet} binary;
var whereGO{Meet, Restaurants} binary;

var meetingPairs{Person, Person, Meet} binary;
var z{Person, Meet, Restaurants} binary; # auxiliary variable for linearization

var sumMeets;
var averagePeople; 
var averagePrice; 


maximize Obj:
    -1000*sum{i in Person,j in Person} s[i,j] + sum {m in Meet, r in Restaurants, p in Person, c in Cuisines} z[p, m, r] * (Cusin_pref[p, c] -1) / 2 * (RestCuisines[r, c] )* (RestRating[r] / 5);

# def of z, z is 1 iff whoGO and whereGO are both 1
subject to z_leq_whoGO{p in Person, m in Meet, r in Restaurants}:
    z[p, m, r] <= whoGO[p, m];

subject to z_leq_whereGO{p in Person, m in Meet, r in Restaurants}:
    z[p, m, r] <= whereGO[m, r];

subject to z_geq_sum{p in Person, m in Meet, r in Restaurants}:
    z[p, m, r] >= whoGO[p, m] + whereGO[m, r] - 1;

subject to pricePerPerson{p in Person, m in Meet, r in Restaurants}: 
    whereGO[m, r] * RestPrice[r] <=  PricePM[p] + SlackPerMeet + 1000*(1- whoGO[p, m]);
 # A restaurant can only be picked if all attendees can afford it 
 
subject to PricePerPersonPerSem{p in Person}:
	PricePS[p] + SlackTotSem >= sum{m in Meet, r in Restaurants} z[p,m,r] * RestPrice[r];

subject to PickFriSat{w in Week}: 
    whenGO[3 * w - 2] + whenGO[3 * w - 1] + whenGO[3 * w] <= 1;



# number of people per meeting is up to 8
subject to eightPersonPerMeet{m in Meet}: 
   sum {p in Person} whoGO[p, m] <= PplInRest;

# number of meetings per semester is up to 5
subject to fiveMeetPerSem:
   sum {m in Meet} whenGO[m] <= MeetingsPerSemPerPerson;

# also we can go sometime only if some person goes 
subject to NoWhoGo{m in Meet, p in Person}: 
    whenGO[m] >= whoGO[p, m];
   # whenGO[m] <= 
# define whereGo (we can only go on a certain day if on that day we are giong ot a restaurant)
subject to NoWhereGo{m in Meet, r in Restaurants}: 
    whenGO[m] >= whereGO[m, r];

# allowing a restaurant to be chosen only once
subject to OneRestPerSem{r in Restaurants}: 
    sum {m in Meet} whereGO[m, r] <= 1;

# this person can never go to a restuarant that has 0
subject to AllergyConstraint{p in Person, r in Restaurants, m in Meet}:
	z[p,m,r] <= Allergy[r,p]; 

subject to Availibility{p in Person, m in Meet}: 
    whoGO[p, m] <= Avail[p, m];

# only one restaurant per meeting
subject to OneRestaurantPerMeet{m in Meet}: 
    sum {r in Restaurants} whereGO[m, r] = whenGO[m];

subject to twoPersonMin{m in Meet}: 
    sum {p in Person} whoGO[p, m] >= 2 * whenGO[m];

subject to MeetingPair0{i in Person, m in Meet}:
    # MeetingPair[i,i,m] is 1 if person i attends meet m
    meetingPairs[i, i, m] = whoGO[i, m];

subject to MeetingPair{i in Person, j in Person, m in Meet: i <> j}: 
    meetingPairs[i, j, m] <= whoGO[j, m];
subject to MeetingPair2{i in Person, j in Person, m in Meet: i <> j}:
    meetingPairs[i, j, m] <= whoGO[i, m];
subject to MeetingPair3{i in Person, j in Person, m in Meet: i <> j}:
    meetingPairs[i, j, m] >= whoGO[i, m] + whoGO[j, m] - 1;
subject to MeetingPair4{i in Person, j in Person, m in Meet: i <> j}:
    meetingPairs[i,j,m] = meetingPairs[j,i,m]; 

subject to ShouldMeet{i in Person, j in Person: i <>j}: 
    s[i,j] + sum{m in Meet} meetingPairs[i,j,m] >= 1; 
subject to slack{i in Person}: 
    s[i,i] = 0;
    
subject to settingVars:
	sumMeets = sum{m in Meet} whenGO[m]; 
subject to abs: 
	averagePeople   = (sum{i in Person, m in Meet} whoGO[i,m] ) / sumMeets; 
subject to abss: 
	averagePrice = sum{r in Restaurants, m in Meet} whereGO[m, r]*RestPrice[r] / sumMeets;
	 
	
	
