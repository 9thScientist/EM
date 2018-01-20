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
                                      EVENTS
  ========================================================= */


abstract sig Event {
	pre, pos : one State
}

sig Nop extends Event {} {
	nop[pre,pos]
}

sig BuyProperty extends Event {
	pl : one Player,
	p : one Property
} {
	buy[pre, pos, pl, p]
}

sig BuildHouse extends Event {
	str : one Street
} {
	build_house[pre, pos, str]
}

sig BuildHotel extends Event {
	str : one Street
} {
	build_hotel[pre, pos, str]
}

sig SellBuilding extends Event {
	b : one Building 
} {
	sell_building[pre, pos, b]
}

sig SellProperty extends Event {
	p : one Property
} {
	sell_property[pre, pos, p]
}

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
--	some buildings.s implies (buildings.s).~(buildings.s).owner = color.~color.owner
	all b : Building | no str : b.~(buildings.s).color.~color | str.owner != b.~(buildings.s).owner
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

pred consistente[ s : State ] {
	building_in_one_street[s] and
	building_must_exist[s] and 
	building_owner_owns_color[s] and
	max_4_houses_1_hotel[s] and
	building_must_have_owner[s]
}


fact {
	all s : State {
		building_in_one_street[s]
/*
		building_must_exist[s]

		building_owner_owns_color[s]

		max_4_houses_1_hotel[s]

		building_must_have_owner[s]
		-- The number of houses in the same color must not differ from 2
	*/
	}
} 


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



/* * * * * * * * * * *
	BUILD
 * * * * * * * * * * */

pred build_house[s : State, s' : State, str : Street] {
	// pre
	some str.owner
	str.color.~color.owner.s in str.owner.s
	(house.s + hotel.s) = Street.buildings.s -- TODO remover isto
	lte[#{str.buildings.s}, 3]

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


pred build_hotel[s : State, s' : State, str : Street] {
	// pre
	some str.owner
	str.color.~color.owner.s in str.owner.s
	(house.s + hotel.s) = Street.buildings.s -- TODO remover isto
	eq[#{str.buildings.s}, 4]

	all strx : str.color.~color | strx.buildings.s in house.s => eq[#{strx.buildings.s}, 4] else eq[#{strx.buildings.s}, 1] 

	// pos
	some h : Hotel - hotel.s {
		hotel.s' = hotel.s + h
		buildings.s' = buildings.s - str->House + str->h
	}
	house.s' = house.s - str.buildings.s

	// frame
	owner.s' = owner.s
}

/* * * * * * * * * * *
	SELL BUILDING
 * * * * * * * * * * */
pred sell_building[s : State, s' : State, h : Building] {
	// Pre
	h in (house + hotel).s
	no strx : h.~(buildings.s).color.~color | gt[#{strx.buildings.s}, #{h.~(buildings.s).buildings.s}]

	// Pos
	(house + hotel).s' = (house + hotel).s - h
--	no h.~(buildings.s')
	buildings.s' = buildings.s - Street->h

	// frame
	owner.s' = owner.s
}


/* * * * * * * * * * *
	SELL PROPERTY
 * * * * * * * * * * */
pred sell_property[s : State, s' : State, p : Property] {
	// Pre
	some p.owner.s
	no p.buildings.s	

	// Pos
	owner.s' = owner.s - p->p.owner.s

	// frame
	house.s' = house.s
	hotel.s' = hotel.s
	buildings.s' = buildings.s
}

/* * * * * * * * * * *
	SELL PROPERTY
 * * * * * * * * * * */
pred nop[s : State, s' : State] {
	buildings.s' = buildings.s
	hotel.s' = hotel.s
	house.s' = house.s
	owner.s' = owner.s
}

/* ========================================================
                               TRACES 
  ========================================================= */

pred traces {
	no house.first
	no hotel.first
	no owner.first

	all s: State-last | one e: Event {
		e.pre = s and e.pos = s.next

		lt[#{house.s}, #{house.(s.next)}] => e in BuildHouse
		lt[#{hotel.s}, #{hotel.(s.next)}] => e in BuildHotel 

		gt[#{buildings.s}, #{buildings.(s.next)}] => e in SellBuilding

		lt[#{owner.s}, #{owner.(s.next)}] => e in BuyProperty
		gt[#{owner.s}, #{owner.(s.next)}] => e in SellProperty
	}
}

run { traces and all s: State - last | pre.s not in Nop } for 4 but
exactly 5 State, 6 Street, 3 Player, 6 House 



/* ========================================================
                           VERIFICATIONS 
  ========================================================= */

run buy_ec {
	some s : State, pl : Player, p : Property | consistente[s] and buy[s, s.next, pl, p]
} for 3 but 2 State

check buy_ic {
	all s : State, pl : Player, p : Property {
		building_in_one_street[s] and buy[s, s.next, pl, p] implies building_in_one_street[s.next]
		building_must_exist[s] and buy[s, s.next, pl, p] implies building_must_exist[s.next]
		building_owner_owns_color[s] and buy[s, s.next, pl, p] implies building_owner_owns_color[s.next]
		max_4_houses_1_hotel[s] and buy[s, s.next, pl, p] implies max_4_houses_1_hotel[s.next]
		building_must_have_owner[s] and buy[s, s.next, pl, p] implies building_must_have_owner[s.next]
	}
} for 3 but 2 State, 5 House, 2 Hotel, 3 Street

check {
	all s1, s2 : Street | some s1.owner and some s2.owner and s1.color = s2.color implies s1.owner = s2.owner
} for 3 but 2 State

run buidl_ec {
	some s : State, str : Street | consistente[s] and build_house[s, s.next, str]
} for 3 but 2 State, 2 Street, 5 House, 2 Hotel


check equilibrado {
	all s : State {
		consistente[s] and consistente[s.next]

		all s1, s2 : Street | s1.color = s2.color and 
		(some (Hotel & (s1.buildings.s + s2.buildings.s)) and 
		some (House & (s1.buildings.s + s2.buildings.s  )) => 
			eq[minus[#{s1.buildings.s}, #{s2.buildings.s}], 3]
		|| no Hotel & (s1.buildings.s + s2.buildings.s) =>
			lte[minus[#{s1.buildings.s}, #{s2.buildings.s}], 1]
		|| no House & (s1.buildings.s + s2.buildings.s) =>
			eq[#{s1.buildings.s}, #{s2.buildings.s}]
		)
	} 
} for 3 but 2 State

check build_house_ic {
	all s : State, str : Street {
		building_in_one_street[s] and build_house[s, s.next, str] implies building_in_one_street[s.next]
		building_must_exist[s] and build_house[s, s.next, str] implies building_must_exist[s.next]
		building_owner_owns_color[s] and build_house[s, s.next, str] implies building_owner_owns_color[s.next]
		max_4_houses_1_hotel[s] and build_house[s, s.next, str] implies max_4_houses_1_hotel[s.next]
		building_must_have_owner[s] and build_house[s, s.next, str] implies building_must_have_owner[s.next]
	}
} for 3 but 2 State, 2 Street, 5 House, 2 Hotel

run buidl_ho_ec {
	some s : State, str : Street | consistente[s] and build_hotel[s, s.next, str]
} for 3 but 2 State, 2 Street, 5 House, 2 Hotel

check build_hotel_ic {
	all s : State, str : Street {
		building_in_one_street[s] and build_hotel[s, s.next, str] implies building_in_one_street[s.next]
		building_must_exist[s] and build_hotel[s, s.next, str] implies building_must_exist[s.next]
		building_owner_owns_color[s] and build_hotel[s, s.next, str] implies building_owner_owns_color[s.next]
		max_4_houses_1_hotel[s] and build_hotel[s, s.next, str] implies max_4_houses_1_hotel[s.next]
		building_must_have_owner[s] and build_hotel[s, s.next, str] implies building_must_have_owner[s.next]
	}
} for 3 but 2 State, 2 Street, 5 House, 2 Hotel


run run_sell {
	some s : State, h : Building | consistente[s] and sell_building[s, s.next, h]
} for 3 but 2 State, 2 Street, 5 House, 2 Hotel

check sell_ec {
	all s : State, h : Building {
		building_in_one_street[s] and sell_building[s, s.next, h] implies building_in_one_street[s.next]
		building_must_exist[s] and sell_building[s, s.next, h] implies building_must_exist[s.next]
		building_owner_owns_color[s] and sell_building[s, s.next, h] implies building_owner_owns_color[s.next]
		max_4_houses_1_hotel[s] and sell_building[s, s.next, h] implies max_4_houses_1_hotel[s.next]
		building_must_have_owner[s] and sell_building[s, s.next, h] implies building_must_have_owner[s.next]
	}
} for 3 but 2 State, 2 Street, 5 House, 2 Hotel


check sell_property_ec {
	all s : State, p : Property {
		building_in_one_street[s] and sell_property[s, s.next, p] implies building_in_one_street[s.next]
		building_must_exist[s] and sell_property[s, s.next, p] implies building_must_exist[s.next]
		building_owner_owns_color[s] and sell_property[s, s.next, p] implies building_owner_owns_color[s.next]
		max_4_houses_1_hotel[s] and sell_property[s, s.next, p] implies max_4_houses_1_hotel[s.next]
		building_must_have_owner[s] and sell_property[s, s.next, p] implies building_must_have_owner[s.next]
	}
} for 3 but 2 State

run run_sell_property {
	some s : State, p : Property | consistente[s] and sell_property[s, s.next, p]
} for 3 but 2 State


run {} for 3 but exactly 6 House, 2 Hotel, 5 Street
