open util/integer
open util/ordering[State]


sig State { }
sig Player { }


enum Color {
	LightBlue, Brown, Blue, Green, Yellow, Red, Orange, Pink
}

abstract sig Building {}
sig House extends Building {
	house : set State
}
sig Hotel extends Building {
	hotel : set State
}

abstract sig Property {
--	owner : lone Player -> State
	owner : Player lone -> State
}

sig Street extends Property {
	color : one Color,
	buildings : set (House + Hotel) -> State
}

sig Station extends Property { }

sig Service extends Property { }



/* ========================================================
                                      INVARIANTS
  ========================================================= */

-- A building can only exist in one street
pred building_in_one_street[s : State] {
	buildings.s.~(buildings.s) in iden
}


-- A building must be in a street and must exist
pred building_must_exist[ s : State] {
	(house.s + hotel.s) = Street.buildings.s
}


-- A building's owner must be the owner of the entire color
pred building_owner_owns_color[ s : State] {
	(buildings.s).~(buildings.s).owner = color.~color.owner
}


-- A street can have up to 4 houses or 1 hotel
pred max_4_houses_1_hotel[ s : State] {
	~(buildings.s).buildings.s in (house.s)->(house.s) + iden
	all str : Street | lte[#{str.buildings.s}, 4]
}


-- No construction without owner
pred building_must_have_owner[ s : State] {
	all str : Street | some str.buildings.s implies one str.owner.s
}

/*
fact {
	all s : State {
		building_in_one_street[s]

		building_must_exist[s]

		building_owner_owns_color[s]

		max_4_houses_1_hotel[s]

		building_must_have_owner[s]
		-- The number of houses in the same color must not differ from 2
	}
} 
*/

check valid_construction {
	all disj s1, s2 : Street | s1.color = s2.color and s1.owner != s2.owner implies no (s1.buildings + s2.buildings)

--	all disj s1, s2 : Street | s1.color = s2.color and s1.owner = s2.owner implies lte[minus[#{s1.buildings}, #{s2.buildings}], 1]
} for 3 but exactly 5 House

check hotel_or_house {
	all s : State {
		-- A property must have either a hotel or houses
		all str : Street | str.buildings.s & Hotel = str.buildings.s or str.buildings.s & house.s = str.buildings.s

		-- A property cannot have multiple hotels
		all str : Street, h : Hotel | h in str.buildings.s implies no str.buildings.s - h

		-- A property can only have a maximum of 4 houses
		all str : Street | lte[#{str.buildings.s}, 4]

	}	
} for 3 but exactly 5 House




/* ========================================================
                                      PREDICATES
  ========================================================= */


/* * * * * * * * * *
	BUY
 * * * * * * * * * */
pred buy[s : State, s' : State, pl : Player, p : Property]  {
	// pre
	no (p.buildings.s)
	p.owner.s != pl

	// pos
	owner.s' = owner.s + p->pl

	// frame
	no (p.buildings.s')
	house.s = house.s'
	hotel.s = hotel.s'
	(Property - p).owner.s = (Property - p).owner.s'
	buildings.s' = buildings.s
}

run buy_ec {
	some s : State, pl : Player, p : Property | buy[s, s.next, pl, p]
} for 3 but 2 State

check buy_ic {
	all s : State, pl : Player, p : Property {
		building_in_one_street[s] and buy[s, s.next, pl, p] implies building_in_one_street[s.next]
		building_must_exist[s] and buy[s, s.next, pl, p] implies building_must_exist[s.next]
		building_owner_owns_color[s] and buy[s, s.next, pl, p] implies building_owner_owns_color[s.next]
		max_4_houses_1_hotel[s] and buy[s, s.next, pl, p] implies max_4_houses_1_hotel[s.next]
		building_must_have_owner[s] and buy[s, s.next, pl, p] implies building_must_have_owner[s.next]
	}
} for 3 but 2 State

check {
	all s1, s2 : Street | some s1.owner and some s2.owner and s1.color = s2.color implies s1.owner = s2.owner
} for 3 but 2 State


/* * * * * * * * * * *
	BUILD
 * * * * * * * * * * */
pred build_house[s : State, s' : State, str : Street] {
	// pre
	some str.owner
	str.color.~color.owner.s in str.owner.s
	(house.s + hotel.s) = Street.buildings.s

	all strx : str.color.~color | gte[#{strx.buildings.s}, #{str.buildings.s}]
	no str.buildings.s & Hotel

	// pos
	some h : House - house.s {
		house.s' = house.s + h
		buildings.s' = buildings.s + str->h
	}

	// frame
	owner.s' = owner.s
	hotel.s' = hotel.s 
}


check build_house_ic {
	all s : State, str : Street {
		building_in_one_street[s] and build_house[s, s.next, str] implies building_in_one_street[s]
		building_must_exist[s] and build_house[s, s.next, str] implies building_must_exist[s.next]
		building_owner_owns_color[s] and build_house[s, s.next, str] implies building_owner_owns_color[s.next]
		max_4_houses_1_hotel[s] and build_house[s, s.next, str] implies max_4_houses_1_hotel[s.next]
		building_must_have_owner[s] and build_house[s, s.next, str] implies building_must_have_owner[s.next]
	}
} for 3 but 2 State

run {} for 3 but exactly 6 House, 2 Hotel, 5 Street
