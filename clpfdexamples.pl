:- use_module(library(clpfd)).

always_true(B) :-
	A #= min(B, C),
	B #< 5,
	C #= 7,
	label([A]),
	writeln(A).

depends_on(B) :-
	A #= min(B, C),
	C #= 7,
	label([A]),
	writeln(A).

foo(X) :-
	X = [_A,_B,_C,_D],
	bar(X).

bar(X) :-
	X ins 1 .. 4,
	all_different(X).


sum_demo(X) :-
	length(X, 4),
	X ins 0 .. 75,
	sum(X, #>=, 100),
	label(X).


in_demo :-
	X in 1..4,
	indomain(X),
	writeln(X),
	fail.
in_demo.

% changing ff to leftmost changes time from 69,570 inferences to
% 4021 inferences
labeling_demo :-
	length(List, 100),
	List ins 0..1,
	time(labeling([ff], List)).

scalar_demo(A, B, C) :-
	Cs = [1, 0, 0, 1], % must be list of integers
	Vs = [A, B, C, 2],  % mix of integers and variables
	scalar_product(Cs, Vs, #=, 5),
	[A, B, C] ins 0..10.

trains([[1,2,0,1],
        [2,3,4,5],
        [2,3,0,1],
        [3,4,5,6],
        [3,4,2,3],
        [3,4,8,9]]).

threepath(A, D, Ps) :-
        Ps = [[A,B,_T0,T1],[B,C,T2,T3],[C,D,T4,_T5]],
        T2 #> T1,
        T4 #> T3,
        trains(Ts),
        tuples_in(Ps, Ts).  % notice no labeling

% threepath(1, 4, P).

reified_boolean(X, B) :-
	X #= 4 #<==> B,
	X #\= 4.
% B = 0,
% X in inf..3\/5..sup.


% pension payments make a good example


/*
global_cardinality(+Vs, +Pairs, +Options)

Global Cardinality constraint.

Vs is a list of finite domain variables,
	Pairs is a list of Key-Num pairs,
where Key is an integer and
Num is a finite domain variable.

global_cardinality([A,B,C,D], [1-1, 2-2, 3-1, 4-0], [])

A

The
  constraint holds iff each V in Vs is equal to some key,

  and for each
  Key-Num pair in Pairs, the number of occurrences of Key in Vs is Num.

  Options is a list of options. Supported options are:
  consistency(value) A weaker form of consistency is used.
  cost(Cost, Matrix) Matrix is a list of rows, one for each variable,
      in the order they occur in Vs. Each of these rows is a list
      of integers, one for each key, in the order these keys occur in
      Pairs. When variable v_i is assigned the value of key k_j, then
      the associated cost is Matrix_{ij}.
      Cost is the sum of all costs.

Used for situations like "we need
*/

global_test(A,B,C,D) :-
	% there must be a single 1, two 2's, and a single 3
	global_cardinality([A,B,C,D], [11-1, 21-2, 31-1, 4-0], []),
	A #= 11,
	B #= 21,
	C #= 21.
	% D must be 31
/*
	% c:/docs/prolog/tutorials/swiplclpfd/clpfdexamples compiled 0.05 sec, 1,643 clauses
17 ?- global_test(A,B,C,D).
A = 1,
B = C, C = 2,
D = 3.
*/

/*
circuit induces a Hamiltonian circuit

A hamiltonian circuit is a path that visits each vertex exactly once.
So this matches a list where each integer from one to len(List) is
present exactly once

?- length(Vs, _), circuit(Vs), label(Vs).
Vs = [] ;
Vs = [1] ;
Vs = [2, 1] ;
Vs = [2, 3, 1] ;
Vs = [3, 1, 2] ;
Vs = [2, 3, 4, 1] .

so, we assume we have a 'ring' where successors are tied, and 1 is tied
to last

*/

/*
Cumulative demo

*/
tasks_starts(Tasks, [S1,S2,S3]) :-
        Tasks = [task(S1,3,_,1,_), % start, duration, end, resources, task_id
                 task(S2,2,_,1,_),
                 task(S3,2,_,1,_)].

cumulative_demo(Tasks, Starts) :-
	tasks_starts(Tasks, Starts),
	Starts ins 0..10,
	cumulative(Tasks, [limit(2)]),
	label(Starts).

/*
Tasks = [task(0, 3, 3, 1, _G36), task(0, 2, 2, 1, _G45), ...],
Starts = [0, 0, 2] .
*/

puzzle([S,E,N,D] + [M,O,R,E] = [M,O,N,E,Y]) :-
        Vars = [S,E,N,D,M,O,R,Y],
        Vars ins 0..9,
        all_different(Vars),
                  S*1000 + E*100 + N*10 + D +
                  M*1000 + O*100 + R*10 + E #=
        M*10000 + O*1000 + N*100 + E*10 + Y,
        M #\= 0, S #\= 0,
	label(Vars).


domains(X, Y) :-
	X in 1..Y.

two_domains(Bases, Var) :-
	make_two_domains(Bases, Term),
	Var in Term.

make_two_domains([H], H..HT) :-
	HT is H + 2.
make_two_domains([H | T], '\\/'(H .. HT, TDomain)) :-
	HT is H + 2,
	make_two_domains(T, TDomain).


/*
	In a chemical plant there is a reaction vessel. The
temperature in the vessel is constrained to be less
than 800 degrees, and to be more than 300 degrees,
except when in 'startup' mode.

	*/

chem_tank(Temp, Startup) :-
	Temp #< 800,
	#\ Startup #==> Temp #> 300.

chem_demo(Temp, TimeNow, StartTime) :-
	chem_tank(Temp, TimeNow - StartTime #< 10).

chain_example([A,B,C,D]) :-
	chain([A,B,C,D], #>=).

/*

	useful when you do fd_inf

We have to do 4 tasks, A,B,C,D
in order.
We're uncertain how long each task will take, but have
these ranges.
A   20..40
B   20..40
C   50..120
D   30..50

B must end at least 100 minutes before D starts
(for some process like letting paint dry)

What is the latest start time for A that guarantees
finishing D by time zero?
*/




/*
	Alan Baljeu

	call_residue_vars

	Execute Goal, then receive a list of Vars whose attributes changed during execution.  More specifically, it only counts those that changed or were added.  It doesn't count variables whose attributes were deleted.  (This is my expectation.  I have never used the predicate, as CHR handles all this stuff for me.)

	6 ?- residue_demo(Now, Start, Vars, Temp).
Now = 10,
Start = 0,
Vars = [Temp],
Temp in 301..799
	*/
residue_demo(Now, Start, Vars, Temp) :-
	 Now in 0..10,   % constrain Now to 10 indirectly
	 Now in 10..20,
	 Start = 0,
	 % knows that only Temp got new constraints
	 call_residue_vars(chem_demo(Temp, Now, Start), Vars).


/*
	 much shorter quarreling children

	 16 children are to be seated in a
	 4 x 4 array of chairs.

         the children are 8 girls (numbered 1..8) and
	 8 boys (numbered 9..16).

         1,3,5,8 think boys are ucky
	 9,10,11,14 think girls are gross

	 these pairs are enemies

	 [[1,2], [4,6], [4,7], [4, 9],[9,11], [12, 14], [14,16]]

 */

length_(Length, List) :- length(List, Length).

child_row(X) :- X ins 1..16 .

ww(X) :-
	write(X),
	write('/').

print_row(Row) :-
	maplist(ww, Row),
	nl.

children(Class) :-
	length(Class, 4),
	maplist(length_(4), Class),
	maplist(child_row , Class),
	maplist(row_compatible, Class),
	transpose(Class, TransClass),
	maplist(row_compatible, TransClass),
	flatten(Class, FlatClass),
	all_different(FlatClass),
	maplist(label, Class),
	maplist(print_row, Class).

row_compatible([A,B,C,D]) :-
	compatible(A, B),
	compatible(B, C),
	compatible(C, D).

compatible(A, B) :-
	not_enemy(A, B),
	not_enemy(B, A),
	sex_compatible(A, B),
	sex_compatible(B, A).

not_enemy(A, B) :-
	NotA #\= A #\/ NotB #\= B,
	tuples_in([[NotA, NotB]],
		    [[1,2], [4,6], [4,7], [4, 9],[9,11], [12, 14], [14,16]]).

sex_compatible(A, B) :-
	A in 1\/3\/5\/8 #==> B #=< 8,
	A in  9..11\/14 #==> B #> 8.


%
%  penny candy example
%  Timmy has 25 cents
%  gumballs cost a penny
%  snickers cost 10 cents
%  toffees are 2 cents
%  licorice costs 5 cents
%
%  what are Timmys alternatives?
%  assume Timmy spends the entire 25 cents
scalar_test(Candy) :-
	Candy = [_Gumball, _Snickers, _Toffee, _Licorice],
	Candy ins 0..sup,
	scalar_product([1, 10, 2, 5], Candy, #=, 25),
	label(Candy).


%
% Suzy wants to flirt with Nathan
% But not when her old boyfriend John is around
%
% Suzy, Nathan, and John all must take classes 1..6
%
% How can Suzy arrange her schedule so she can flirt
% in at least 3 classes?

flirt_constraint(Suzy, Nathan, John, FlirtPeriods) :-
	length(Suzy, 6),
	length(Nathan, 6),
	length(John, 6),
	Suzy ins 1..6,
	Nathan ins 1..6,
	John ins 1..6,
	all_different(Suzy),
	all_different(Nathan),
	all_different(John),
	FlirtPeriods = [A,B,C],
	FlirtPeriods ins 1..6,
	A #< B,    % remove unwanted symmetry
	B #< C,
	flirty_period(A, Suzy, Nathan, John),
	flirty_period(B, Suzy, Nathan, John),
	flirty_period(C, Suzy, Nathan, John),
	label(Suzy),
	label(FlirtPeriods).

flirty_period(Period, Suzy, Nathan, John) :-
	Class in 1..6,
	DiffClass #\= Class,
	element(Period, Suzy, Class),
	element(Period, Nathan, Class),
	element(Period, John, DiffClass).


/*
	automaton demonstration

 */
two_consecutive_ones(Vs) :-
        automaton(Vs, [source(a),sink(c)],
                  [arc(a,0,a), arc(a,1,b),
                   arc(b,0,a), arc(b,1,c),
                   arc(c,0,c), arc(c,1,c)]).

demo_automaton(Vs) :-
	length(Vs, 3),
	two_consecutive_ones(Vs),
	label(Vs).



multi_source_automaton(Vs) :-
	automaton(Vs, [source(a),source(e), sink(d), sink(h)],
		  [arc(a,0,b),
		   arc(b,0,b),
		   arc(b,1,c),
		   arc(c,2,d),
		   arc(e,10,f),
		   arc(f,10,f),
		   arc(f,11,g),
		   arc(g,12,h)]).

demo_len(Vs) :-
	length(Vs, 4),
	multi_source_automaton(Vs),
	label(Vs).


single_source_automaton(Vs) :-
	automaton(Vs, [source(a), sink(d)],
		  [arc(a,0,b),
		   arc(b,0,b),
		   arc(b,1,c),
		   arc(c,2,d)
		   ]).

demo_single_source(Vs) :-
	length(Vs, 4),
	single_source_automaton(Vs),
	label(Vs).


%
%  accepts any sequence of 0,1, and 2
%  that contains exactly 7 0's
%  and has no occurances of the same number twice in a row
%
needs_7_as(Vs) :-
	automaton(_, _, Vs,
		 [source(start), sink(a), sink(b), sink(c)],
		  [
		     arc(start, 0, a, [C+1]),
		     arc(start, 1, b),
		     arc(start, 2, c),
		     arc(a, 1, b),
		     arc(a, 2, c),
		     arc(b, 0, a, [C+1]),
		     arc(b, 2, c),
		     arc(c, 0, a, [C+1]),
		     arc(c, 1, b)
		 ],
		  [C],
		  [0],
		  [7]
		 ).

demo_7_as(Vs) :-
	length(Vs, 20),
	Vs ins 0..2,
	needs_7_as(Vs),
	label(Vs).


:- use_module(library(pairs)).

my_schedule_today(Starts, Durations) :-
  % unordered list of stuff to do today
  % in a real problem we'd probably use minutes
    Starts = [PrepForSmith, MeetWithSmith, _WriteDBInstaller, Lunch, _CallAlice, _ReadDocs],
  % and how long they'll take
    Durations = [2, 1, 2, 1, 1, 1],
  % make all of them start in 9am to 5pm
    Starts ins 9..17,
  % and make sure lunch happens at noon or 1pm
    Lunch in 12 \/ 13,
  % Meeting with Smith is planned for 1pm
    MeetWithSmith #= 13,
  % have to do the prep before the meeting
	PrepForSmith #< MeetWithSmith,
  % enforce being serialized
    serialized(Starts, Durations).

demo_my_schedule(Starts, Durations) :-
	my_schedule_today(Starts, Durations),
	append(Starts, Durations, Vars),
	label(Vars),
	pairs_keys_values(NameDurs ,
       ['Prep for Smith', 'Meet With Smith', 'Write DB Installer', 'Lunch', 'Call Alice', 'Read Flubbercalc Docs'], Durations),
	pairs_keys_values(Pairs, Starts, NameDurs),
	keysort(Pairs, Sorted),
	pairs_keys_values(Sorted, SortStarts, SortNameDurs),
	print_sched(SortStarts, SortNameDurs).

print_sched([], _).
print_sched([Start | ST], [Name-Duration | T]) :-
	format('~w: ~w  (~w hr)~n', [Start, Name, Duration]),
	print_sched(ST, T).


names([amy,bill,charley,deanna,eric,frieda,george,harley]).
genders([1,0,0,1,0,1,0,0]).
ages([22,19,73,65,40,38,25,27]).

% maps compatible names
romance(A, B) :-
    names(Names),
    length(Names, NameLength),
    AIndex in 1..NameLength,
    BIndex in 1..NameLength,
    genders(G),
    element(AIndex, G, AG),
    element(BIndex, G, BG),
    AG #\= BG,
    ages(Ages),
    element(AIndex, Ages, AAge),
    element(BIndex, Ages, BAge),
    AAge #< BAge #==> AAge + 10 #>= BAge,
    AAge #>= BAge #==> BAge + 10 #>= AAge,
    AIndex #< BIndex, % remove unwanted symmetry and reflexiveness
    label([AIndex, BIndex]),
    nth1(AIndex, Names, A),
    nth1(BIndex, Names, B).


% test global_cardinality/3
%
shifts([1,2,3,1,2,3,1,2,3,1,2,3,1,2,3,4,5,6,4,5,3]).

shifts_ok(A,B,C,D) :-
     shifts(Shifts),
     global_cardinality(Shifts, [1-5, 2-5, 3-A, 4-B, 5-C, 6-D], []).

count_shifts(Counts) :-
     shifts(Shifts),
     bagof(X, between(1,6,X), Keys),
     length(Values, 6),
     pairs_keys_values(Counts, Keys, Values),
     global_cardinality(Shifts, Counts, []).


post_shifts(Counts) :-
     length(UnknownShifts, 21),
     bagof(X, between(1,6,X), Keys),
     length(Values, 6),
     pairs_keys_values(Counts, Keys, Values),
     global_cardinality(UnknownShifts, Counts, []),
     % at this point I have Counts and UnknownShifts constrained,
     % though I don't know UnknownShifts
     shifts(UnknownShifts).


%
%  We have 3 mechanics, and a number of repair jobs to do
%  Transmission jobs take two mechanics
%
%  Find a set of start times for the jobs during a 10 hour day
%
task_names([
    transmission, brake_job_1, brake_job_2, diagnosis_1,
    diagnosis_2, fuel_injection]).

tasks([
    task(S1,3,_,2,1),
    task(S2,1,_,1,2),
    task(S3,1,_,1,3),
    task(S4,3,_,1,4),
    task(S5,3,_,1,5),
    task(S6,2,_,1,6)], [S1, S2, S3, S4, S5, S6]).

find_task_starts(S) :-
	length(S, 6),
	S ins 0..9,
	tasks(Tasks, S),
	cumulative(Tasks, [limit(3)]),
	label(S).

sort_of_near_to(X, Y, N, M) :-
	X #> Y #==> X - N #>= Y  #/\  X - M - 1 #< Y,
	X #=< Y #==> Y - N #>= X #/\ Y - M - 1 #< X.

test_sort_near :-
	sort_of_near_to(4,4,0,3),
	sort_of_near_to(4,5,1,3),
	sort_of_near_to(5,4,1,3),
	\+ sort_of_near_to(4,4,1,3),
	\+ sort_of_near_to(5,2,1,2).


:- multifile clpfd:run_propagator/2.

oneground(X, Y, Z) :-
        clpfd:make_propagator(oneground(X, Y, Z), Prop),
        clpfd:init_propagator(X, Prop),
        clpfd:init_propagator(Y, Prop),
        clpfd:trigger_once(Prop).

% Z must be one if either X or Y are instantiated
%
clpfd:run_propagator(oneground(X, Y, Z), MState) :-
        (   integer(X) -> clpfd:kill(MState), Z = 1
        ;   integer(Y) -> clpfd:kill(MState), Z = 1
        ;   true
        ).


even(X) :-
        clpfd:make_propagator(even(X), Prop),
        clpfd:init_propagator(X, Prop),
        clpfd:trigger_once(Prop).

clpfd:run_propagator(even(X), MState) :-
        (   integer(X) -> clpfd:kill(MState), 0 is X mod 2
        ;   true
        ).


increase([]).
increase([_]).
increase([A, B | T]) :-
	A #< B,
	increase([B | T]).

