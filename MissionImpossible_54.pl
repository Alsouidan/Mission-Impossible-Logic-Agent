% Author:
% Date: 12/26/2020
:-include("KB.pl").
/*
**************************************************************************************************
**************************************************************************************************
************************************HELPER PREDICATES*********************************************
**************************************************************************************************
**************************************************************************************************
*/

% Helper Predicate that returns true when the input is a point that is our of the border
isWall([X,Y]):-
 (X>3;Y>3);
 (X<0;Y<0).
% Helper Predicate that returns true when point given is at submarine
atSubmarine([X,Y]):-
submarine(X,Y).
% Helper Predicate that returns true when the the two points are at the same location
atLoc([X,Y],[X,Y]).

% Helper Predicate nextPosition(A,B,C) returns true when C is the resulting position when B is applied to A , used to know next position
nextPosition([X,Y],left,[X,B]):-
 B is Y-1.
nextPosition([X,Y],right,[X,B]):-
 B is Y+1.
nextPosition([X,Y],up,[A,Y]):-
 A is X-1.
nextPosition([X,Y],down,[A,Y]):-
 A is X+1.



% Helper Predicate canCarry(MembersList,Ethan,Capacity,Member) returns true when Ethan is at Member's location and capacity is more than zero
% Member is in MembersList
canCarry([H|_],Loc,Capacity,H):-
 Capacity>0,
 atLoc(H,Loc).
canCarry([H|T],Loc,Capacity,Member):-
 \+ atLoc(H,Loc),
 canCarry(T,Loc,Capacity,Member).
 
% Helper Predicate carryMember(MembersList,Member,Capacity,CarriedList,NewCarriedList,NewMembersList,NewCapacity)
% Returns true when NewCarriedList is the result from carrying Member from MembersList and NewCapacity is the Capacity after carrying Member
% In other words this predicate carries Member by removing from the members list and decreases the capacity, it returns the updated parameters
 
carryMember(MembersList,Member,Capacity,CarriedList,NewCarriedList,NewMembersList,NewCapacity):-
 delete(MembersList,Member,NewMembersList),
 append(CarriedList,[Member],NewCarriedList),
 NewCapacity is Capacity-1.

% Helper predicate used to check if Ethan can drop (Ethan is ate submarine and is carrying members)
% canDrop(Ethan,CarriedList)
% Returns true when Ethan is at the submarine and CarriedList isn't empty
canDrop(Ethan,[_|_]):-
 atSubmarine(Ethan).

%  Returns true at goal state
% goalTest(EthanLoc,MembersList,CarriedMembers,Capacity)
% True when EthanLoc is at submarine, No Members in MembersList, No Members in CarriedMembers and Capacity is same as start
goalTest(EthanLoc,[],[],Capacity):-
 capacity(Capacity),
 atSubmarine(EthanLoc).

/*
**************************************************************************************************
**************************************************************************************************
************************************Successor State Axioms****************************************
**************************************************************************************************
**************************************************************************************************
*/

% True when initial state
ethanState([X,Y],B,[],D,s0):-
 ethan_loc(X,Y),
 members_loc(B),
 capacity(D).

%  Successor State Axioms
ethanState(EthanLoc,MembersLoc,Carried,Capacity,result(Action,S)):-

 (
 %  Get old State
  ethanState(OldLoc,OldList,OldCarried,OldCapacity,S),
 (
  (  % Axioms for Changing States
 Action=carry,                          % Can Carry
 EthanLoc = OldLoc,
 canCarry(OldList,EthanLoc,OldCapacity,Member),
 carryMember(OldList,Member,OldCapacity,OldCarried,Carried,MembersLoc,Capacity)
 );
 (Action=drop,             % Can drop
  EthanLoc = OldLoc,
 [] = Carried,
 MembersLoc=OldList,
 canDrop(EthanLoc,OldCarried),
 capacity(Capacity)
 );
 (
 nextPosition(OldLoc,Action,EthanLoc),  % Next position isn't a wall
 \+isWall(EthanLoc),
 Action\=carry,Action\=drop,
 MembersLoc= OldList,
 OldCarried = Carried,
 OldCapacity= Capacity
 )
 )
);
% State Persistence
 (
 ethanState(EthanLoc,MembersLoc,Carried,Capacity,S),
 ( (Action\=drop,Action\=carry) -> (nextPosition(EthanLoc,Action,NewLoc), isWall(NewLoc)),
   (Action=drop -> \+ canDrop(EthanLoc,Carried)),
   (Action=carry -> \+canCarry(MembersLoc,EthanLoc,Capacity,_))
   )
   ).



goalHelper1(Limit,S,R):- R\=depth_limit_exceeded.
goalHelper1(Limit,S,depth_limit_exceeded):-
 (call_with_depth_limit(once(goalHelper2(S)),Limit,R)),
% Increment Limit of DF Tree by 10
  New_Limit is Limit+10,
  goalHelper1(New_Limit,S,R).
  
goalHelper2(S):-
 goalTest(A,B,C,D),
 ethanState(A,B,C,D,S).
goal(S):-
 goalHelper1(1,S,_).