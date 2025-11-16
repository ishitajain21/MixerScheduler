set Meet;
set Person;
set Cuisines;
set Restaurants; 
set Week;

param Avail{Person, Meet};
param Cusin_pref{Person, Cuisines};

param PricePM{Person};

param PricePS{Person};  

param RestPrice{Restaurants};

param RestCuisines{Restaurants, Cuisines};

param RestRating{Restaurants};
 
var MinPrice{Meet} >= 0;  
var TotalPrice >= 0;


var whoGO{Person, Meet} binary;
var whenGO{Meet} binary;
var whereGO{Meet, Restaurants} binary;

var meetingPairs{Person, Person, Meet} binary; 

maximize Obj:
    sum {m in Meet, r in Restaurants}
        whereGO[m, r] * (RestRating[r] / 5) *
        sum {p in Person, c in Cuisines}
            whoGO[p, m] * Cusin_pref[p, c] * RestCuisines[r, c];

subject to pricePerPerson{p in Person, m in Meet, r in Restaurants}: 
    whereGO[m, r] * RestPrice[r] <= MinPrice[m] + 10;


subject to defMinPrice{m in Meet, p in Person}: 
    MinPrice[m] >= whoGO[p, m] * PricePM[p];


subject to PickFriSat{w in Week}: 
    whenGO[3 * w - 2] + whenGO[3 * w - 1] + whenGO[3 * w] <= 1;


subject to eightTimesSemester: 
    sum {m in Meet} whenGO[m] <= 8;

# what it means to choose not to go to restrant
subject to NoWhoGo{m in Meet, p in Person}: 
    whenGO[m] >= whoGO[p, m];

subject to NoWhereGo{m in Meet, r in Restaurants}: 
    whenGO[m] >= whereGO[m, r];


subject to Availibility{p in Person, m in Meet}: 
    whoGO[p, m] <= Avail[p, m];


subject to OneRestaurantPerMeet{m in Meet}: 
    sum {r in Restaurants} whereGO[m, r] = whenGO[m];


subject to MeetingPair0{i in Person, m in Meet}:
    # MeetingPair[i,i,m] is 1 if person i attends meet m
    meetingPairs[i, i, m] = whoGO[i, m];

subject to MeetingPair1{i in Person, j in Person, m in Meet: i <> j}:
    # meetingPairs[i,j,m] <= whoGO[j,m]
    meetingPairs[i, j, m] <= whoGO[j, m];

subject to MeetingPair2{i in Person, j in Person, m in Meet: i <> j}:
    # meetingPairs[i,j,m] <= whoGO[i,m]
    meetingPairs[i, j, m] <= whoGO[i, m];

subject to MeetingPair3{i in Person, j in Person, m in Meet: i <> j}:
    # meetingPairs[i,j,m] >= whoGO[i,m] + whoGO[j,m] - 1
    meetingPairs[i, j, m] >= whoGO[i, m] + whoGO[j, m] - 1;
