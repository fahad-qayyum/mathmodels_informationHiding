note
	description: "Summary description for {TUPLE_ITERATION_CURSOR}."
	author: ""
	date: "$Date$"
	revision: "$Revision$"

class
	TUPLE_ITERATION_CURSOR [V -> attached ANY, K -> attached ANY]

inherit
	ITERATION_CURSOR [TUPLE[V, K]]

create
	make

feature{NONE}-- Attributes
	value : LINKED_LIST[V]
	key : ARRAY[K]
	cur_pos : INTEGER

feature
	make(v : LINKED_LIST[V]; k : ARRAY[K])
		do
			value := v
			key := k
			cur_pos  := key.lower
		end

feature --cursor operations
	item : TUPLE [V, K]
		do
			create result
			result := [ value[cur_pos] , key[cur_pos] ]
		end
	after : BOOLEAN
		do
			result:= cur_pos > key.upper
		end
	forth
		do
			cur_pos := cur_pos + 1
		end

end
