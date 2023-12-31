/*facts*/
/*tovar(id, name, category, price)*/
/*10tovar*/

tovar (1, "butter", "fat&oil" , 100).
tovar(2, "chicken", "vegetable", 300).
tovar(3, "biscuit", "snacks", 50).
tovar (4, "groundnut oil", "fat&oil", 200).
tovar(5, "apple", "fruit", 20).
tovar(6, "banana", "fruit", 50).
tovar(7, "eggs", "fat&oil", 270).
tovar(8, "cookies", "snacks", 250).
tovar(9, "book", "stationery", 120).
tovar(10, "pen", "stationery", 25).

/*client (name, telephone number, gender, client_status)
    status enum: gold, silver, bronze
*/
/*5clients*/

client("Tom", "89012345467", male, bronze).
client("Mark", "89254312634", male, gold).
client("Becky", "89015467856", female, bronze).
client("Soler",  "89217450987", male, silver).
client("Laura", "89043249021", female, gold).

/*20sales*/

/*sales(number, tovar(id), количество, day, month)*/

sales("89254312634", 10, 11, 5, "may").
sales("89015467856", 2, 3, 5, "may").
sales("89012345467", 5, 20, 5, "may").
sales("89254312634", 3, 5, 5, "may").
sales("89015467856", 1, 7, 5, "may").

sales("89217450987", 4, 2, 6, "may").
sales("89043249021", 8, 1, 6, "may").
sales("89254312634", 10, 3, 6, "may").
sales("89217450987", 3, 6, 6, "may").
sales("89012345467", 9, 7, 6, "may").

sales("89043249021", 4, 9, 7, "may").
sales ("89015467856", 7, 3, 7, "may").
sales("89012345467", 9, 8, 7, "may").
sales("89254312634", 1, 6, 7, "may").
sales("89043249021", 3, 15, 7, "may").

sales("89217450987", 5, 19, 8, "may").
sales("89012345467", 8, 16, 8, "may").
sales("89043249021", 7, 10, 8, "may").
sales("89217450987", 4, 7, 8, "may").
sales("89015467856", 2, 4, 8, "may").


/*правила*/
%money(Number, Price):-sales(Number, Id,_,_),tovar(Id,_,_,Price).


/*sum_sales(D, M, Sale):-
    sales(_,_,Sale1,D,M),
    Sale=Sale1.
amount_spent_by(Num, Money):-
    money(Num, M1),
    Money = M1.
*/
sales_by(Num, Tovar, Purchased ):-
    sales(Num,Id,Quant,_,_),
    tovar(Id,Good,_,_),
    Tovar=Good,
    Purchased = Quant.
   
who_bought(Id, Person, Ti):-
    sales(Num,Id,Quan,_,_),
    client(Name,Num,Gend,_),
    tovar(Id, Title,_,_),
    Person=Name,
    Ti=Title.
    
%male
customer_gender(Id, Gender):-
    sales(Num,Id,_,_,_),
    client(Name,Num,Gen,_),
    Gender=Gen.
goods_sold_on(D,M,Good):-
    sales(_,Id,_,D,M),
    tovar(Id,Name,_,_),
    Good=Name.

/*
1 - sales_by(89015467856,Good, Quantity)
2- who_bought(4,Person,Good)
3- customer_gender(7,GENDER)
4 - goods_sold_on(5,"may",Goods)
*/