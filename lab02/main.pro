% Copyright

implement main
    open core, stdio, file

domains
    client_status = bronze; gold; silver.
    gender = male; female.
    str_type = string.
    int_type = integer.
    clist = clist(str_type Client_name, str_type Client_number, client_status Status).
    slist = slist(str_type Good_name, int_type Quantity, real Price).

class facts - projectDb
    s : (real Sum) single.
    s1 : (real Sum) single.
    tovar : (int_type Id, str_type Name, str_type Category, real Price) nondeterm.
    client : (str_type Name, str_type Telephone, gender Gender, client_status ClientStatus) nondeterm.
    sales : (str_type Telephone, int_type Id, int_type Количество, int_type Day, str_type Month) nondeterm.

class predicates
    sum_sales : (int_type D, str_type M) determ.
    sales_by : (str_type Num, str_type Tovar [out], int_type Purchased [out]) nondeterm.
    who_bought : (int_type Id, str_type Person [out], str_type Ti [out]) nondeterm.
    customer_gender : (int_type Id, gender Gender [out]) nondeterm.
    goods_sold_on : (int_type Day, str_type Month) nondeterm.
    total_income_on : (int_type D, str_type M).

clauses
    s(0).
    s1(0).
    sum_sales(D, M) :-
        sales(_, _, Sale, D, M),
        s(Sum),
        asserta(s(Sum + Sale)),
        fail.

    sum_sales(D, M) :-
        sales(_, _, _, D, M),
        s(Sum),
        write("Sum of sale is ", Sum),
        nl,
        !.
    sales_by(Num, Tovar, Purchased) :-
        sales(Num, Id, Purchased, _, _),
        tovar(Id, Tovar, _, _).

    who_bought(Id, Person, Ti) :-
        sales(Num, Id, _, _, _),
        client(Person, Num, _, _),
        tovar(Id, Ti, _, _).

    customer_gender(Id, Gender) :-
        sales(Num, Id, _, _, _),
        client(_, Num, Gender, _).

    goods_sold_on(Day, Month) :-
        sales(_, Id, _, Day, Month),
        tovar(Id, Good, _, _),
        write("Goods sold on ", Day, " ", Month, " is ", Good).

    total_income_on(D, M) :-
        sales(_, Id, Quant, D, M),
        tovar(Id, _, _, Price),
        Sales = Price * Quant,
        s1(Sum),
        asserta(s1(Sum + Sales)),
        fail.

    total_income_on(D, M) :-
        s1(Sum),
        write("\nTotal income for ", D, "/", M, " is: ", Sum),
        nl,
        !.

class predicates
    length : (A*) -> integer N.
    sum_list : (real* List) -> real Sum.
    average_list : (real* List) -> real Average determ.
    client_list_on : (int_type Day, str_type Month) -> string*.
    saleslist : (int_type Day, str_type Month) -> real*.
    sales_count : (int_type Day, str_type Month) -> real N.
    sum_sales : (int_type Day, str_type Month) -> real.
    average_sales : (int_type Day, str_type Month) -> real N determ.
    sales_list : (int_type Day, str_type Month) -> slist*.
    client_list : (int_type Day, str_type Month) -> clist*.

clauses
    length([]) = 0.
    length([_ | T]) = length(T) + 1.

    sum_list([]) = 0.
    sum_list([H | T]) = sum_list(T) + H.

    average_list(L) = sum_list(L) / length(L) :-
        length(L) > 0.
%how many sales do we have. i need a list to take the sales
    client_list_on(Day, Month) = Client :-
        Client =
            [ Client_name ||
                sales(Num, _, _, Day, Month),
                client(Client_name, Num, _, _)
            ].
    saleslist(Day, Month) = Amount :-
        Amount =
            [ Unit * Price ||
                sales(_, Id, Unit, Day, Month),
                tovar(Id, _, _, Price)
            ].
    sales_count(Day, Month) = length(saleslist(Day, Month)).
    sum_sales(Day, Month) = sum_list(saleslist(Day, Month)).
    average_sales(Day, Month) = average_list(saleslist(Day, Month)).
    sales_list(Day, Month) =
        [ slist(Name, Kol, Price) ||
            sales(_, Id, Kol, Day, Month),
            tovar(Id, Name, _, Price)
        ].
    client_list(Day, Month) =
        [ clist(Name, Number, Status) ||
            sales(Number, _, _, Day, Month),
            client(Name, Number, _, Status)
        ].

class predicates  %print to the screen the list
    write_saleslist : (slist* Goods_and_Price).
    write_clientslist : (clist* Client_and_Details).

clauses
    write_saleslist(L) :-
        foreach slist(Name, Kol, Price) = list::getMember_nd(L) do
            writef("\t%\t%\t%\n", Name, Kol, Price)
        end foreach.
    write_clientslist(L) :-
        foreach clist(Name, Number, Status) = list::getMember_nd(L) do
            writef("\t%\t%\t%\n", Name, Number, Status)
        end foreach.

clauses
    run() :-
        consult("../database.txt", projectDb),
        fail.
        /*run() :-
        tovar(A, B, C, D),
        write("tovar with Id ", A, " is ", B, " from the class of  ", C, " and the price is ", D),
        nl,
        fail.*/

    run() :-
        sum_sales(5, "May"),
        nl,
        fail.
    run() :-
        sales_by("89015467856", Good, Quantity),
        write(Good, " купил ", Quantity, " раз"),
        nl,
        fail.
        %whitespace
    run() :-
        write("\n"),
        write("\n"),
        fail.
    run() :-
        who_bought(4, Name, Good),
        write(Good, " bought by : ", Name),
        nl,
        fail.

    run() :-
        customer_gender(7, Gender),
        write("Gender = ", Gender),
        nl,
        fail.

    run() :-
        goods_sold_on(5, "May"),
        nl,
        fail.
    run() :-
        total_income_on(5, "May"),
        nl,
        fail.
        %List comprehension
    run() :-
        L = [ Price || tovar(_, _, _, Price) ],
        write(L),
        nl,
        fail.
    run() :-
        write("Sales list for the 5th of May:- \n"),
        write_saleslist(sales_list(5, "May")),
        nl,
        fail.
    run() :-
        write("Client list for sales on 5th of May:- \n"),
        write_clientslist(client_list(5, "May")),
        nl,
        fail.
    run() :-
        write("List of client on 5th of May is "),
        write(client_list_on(5, "May")),
        nl,
        fail.
    run() :-
        %Using 5th of May for Code Testing
        write("List of sale on 5th of May is "),
        write(saleslist(5, "May")),
        nl,
        write("Total number of sales on May 5 is  "),
        write(sales_count(5, "May")),
        nl,
        write("Total sum of sales on May 5 is"),
        write(sum_sales(5, "May")),
        nl,
        write("Average sale on May 5 is "),
        write(average_sales(5, "May")),
        nl,
        fail.

    run().

end implement main

goal
    console::runUtf8(main::run).
