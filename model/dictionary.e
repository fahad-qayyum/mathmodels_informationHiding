note
	description: "A Dictionary ADT mapping from keys to values"
	author: "Jackie and You"
	date: "$Date$"
	revision: "$Revision$"

class
		-- Constrained genericity because V and K will be used
		-- in the math model class FUN, which require both to be always
		-- attached for void safety.
	DICTIONARY [V -> attached ANY, K -> attached ANY]

inherit

	ITERABLE [TUPLE [V, K]]

create
	make

feature -- Do not modify this export status!

	values: LINKED_LIST [V]

	keys: ARRAY [K]

feature -- Abstraction function

	model: FUN [K, V] -- Do not modify the type of this query.
			-- Abstract the dictionary ADT as a mathematical function.
		local
			position: INTEGER
			pair: PAIR [K, V]
		do
				-- Your Task
			create result.make_empty
			from
				position := 1
			until
				position > keys.upper
			loop
				create pair.make (keys [position], values [position])
				result.extend (pair)
				position := position + 1
			end
		ensure
			consistent_model_imp_counts:
					-- Your Task: sizes of model and implementations the same
				count ~ model.count
			consistent_model_imp_contents:
					-- Your Task: applying the model function on each key gives back the corresponding value
				across 1 |..| result.count as j all result.has (create {PAIR [K, V]}.make (keys [j.item], values [j.item])) end
		end

feature -- feature required by ITERABLE

	new_cursor: TUPLE_ITERATION_CURSOR [V, K] -- Do not change this return type.
		do
			create result.make (values, keys) -- Your Task
		end

feature -- Constructor

	make
			-- Initialize an empty dictionary.
		do
				-- Your Task: add more code here

			create values.make
			create keys.make_empty
			values.compare_objects
			keys.compare_objects
		ensure
			empty_model: model.is_empty
			object_equality_for_keys:
					-- Do not modify this.
				keys.object_comparison
			object_equality_for_values:
					-- Do not modify this.
				values.object_comparison
		end

feature -- Commands

	add_entry (v: V; k: K)
		require
			non_existing_key_in_model: not model.domain.has (k)
		do
				-- Your Task.
			keys.force (k, keys.count + 1)
			values.extend (v)
		ensure
			entry_added_to_model:
					-- Your Task.
					-- Hint: Look at feature 'test_add' in class 'EXAMPLE_DICTIONARY_TESTS'.
				model ~ old model.extended ([k, v])
		end

	add_entries (entries: SET [TUPLE [k: K; v: V]])
		require
			non_existing_keys_in_model: -- Your Task.
				across entries as cursor all not model.as_set.has (cursor.item) end
		local
			i: INTEGER
			tuple: TUPLE [k: K; v: V]
		do
				-- Your Task.
			create tuple
			from
				i := 1
			until
				i > entries.count
			loop
				tuple := entries.as_array.item (i)
				keys.force (tuple.k, keys.count + 1)
				values.extend (tuple.v)
				i := i + 1
			end
		ensure
			entries_added_to_model:
					-- Your Task.
					-- Hint: Look at feature 'test_add' in class 'EXAMPLE_DICTIONARY_TESTS'.
				across entries as cursor all model.as_set.has (cursor.item) end
		end

	remove_entry (k: K)
		require
			existing_key_in_model:
					-- Your Task.
				model.domain.has (k)
		local
			keys_duplicate: ARRAY [k]
			values_duplicate: LINKED_LIST [V]
			index: INTEGER
			counter: INTEGER
		do
				-- Your Task.
			counter := 1
			create keys_duplicate.make_empty
			create values_duplicate.make
			across
				keys as cursor
			loop
				counter := counter + 1
				if cursor.item ~ k then
					index := counter
				elseif cursor.item /~ k then
					keys_duplicate.force (cursor.item, keys_duplicate.count + 1)
				end
			end
			counter := 1
			keys := keys_duplicate
			across
				values as cursor
			loop
				counter := counter + 1
				if counter ~ index then
				else
					values_duplicate.force (cursor.item)
				end
			end
			values := values_duplicate
		ensure
			entry_removed_from_model:
					-- Your Task.
					-- Hint: Look at feature 'test_remove' in class 'EXAMPLE_DICTIONARY_TESTS'.
				model ~ (old model.deep_twin).domain_subtracted_by (k)
		end

	remove_entries (ks: SET [K])
		require
			existing_keys_in_model: across ks as cursor all model.domain.has (cursor.item) end
			-- Your Task.
		local
			i: INTEGER
			ke: K
		do
				-- Your Task.
			from
				i := 1
			until
				i > ks.count
			loop
				ke := ks.as_array.item (i)
				remove_entry (ke)
				i := i + 1
			end
		ensure
			entries_removed_from_model:
					-- Your Task.
					-- Hint: Look at feature 'test_add' in class 'EXAMPLE_DICTIONARY_TESTS'.
				model ~ (old model.deep_twin).domain_subtracted (ks)
		end

feature -- Queries

	count: INTEGER
			-- Number of keys in dictionary.
		do
				-- Your Task
			result := keys.count
		ensure
				-- Your Task
			correct_result: result ~ model.count
		end

	get_keys (v: V): ITERABLE [K]
			-- Keys that are associated with value 'v'.
		local
			key_values: ARRAY [K]
			i: INTEGER
		do
				-- Your Task.
			create key_values.make_empty
			from
				i := values.lower
			until
				i > values.count
			loop
				if values [i] ~ v then
					key_values.force (keys [i], key_values.count + 1)
				end
				i := i + 1
			end
			result := key_values
		ensure
			correct_result:
					-- Your Task: Every key in the result has the right corresponding value in model
				across result as cursor all model.range_restricted_by (v).domain.has (cursor.item) end
		end

	get_value (k: K): detachable V
			-- Assocated value of 'k' if it exists.
			-- Void if 'k' does not exist.
		local
			i: INTEGER
		do
			from
				i := 1
			until
				i > keys.count
			loop
				if keys.at (i) ~ k then
					Result := values.at (i)
				end
				i := i + 1
			end
		ensure
			case_of_void_result: not model.domain.has (k) implies result ~ void
				-- Your Task: void result means the key does not exist in model
			case_of_non_void_result: model.domain.has (k) implies result /~ void

				-- Your Task: void result means the key exists in model
		end

invariant
		-- Do not modify these two invariants.
	consistent_keys_values_counts: keys.count = values.count
	consistent_imp_adt_counts: keys.count = count

end
