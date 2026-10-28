module

public import Theory.GroupTheory.WordSubgroup

/-!
# Sporadic word-subgroup compatibility interface

The generic Schreier--Sims word infrastructure now lives in
`Theory.GroupTheory`.  Older Sporadic certificate modules use the historical
`Sporadic.Mathieu` names, so this module exposes transparent compatibility
aliases while keeping the implementation in the shared theory layer.
-/

namespace Sporadic.Mathieu

public abbrev evalWord := @Theory.GroupTheory.evalWord
public abbrev evalWord_append := @Theory.GroupTheory.evalWord_append
public abbrev evalWord_reverse_map_inv := @Theory.GroupTheory.evalWord_reverse_map_inv
public abbrev wordSubgroup := @Theory.GroupTheory.wordSubgroup
public abbrev evalWord_mem_wordSubgroup := @Theory.GroupTheory.evalWord_mem_wordSubgroup
public abbrev wordSubgroup_le_of_gen_mem := @Theory.GroupTheory.wordSubgroup_le_of_gen_mem
public abbrev wordSubgroup_fix_of_gen_fix := @Theory.GroupTheory.wordSubgroup_fix_of_gen_fix
public abbrev wordSubgroup_card_eq_mul_next :=
  @Theory.GroupTheory.wordSubgroup_card_eq_mul_next
public abbrev wordSubgroup_fin_zero_eq_bot :=
  @Theory.GroupTheory.wordSubgroup_fin_zero_eq_bot
public abbrev wordSubgroup_fin_zero_card := @Theory.GroupTheory.wordSubgroup_fin_zero_card
public abbrev rightInverse_of_leftInverse_fin :=
  @Theory.GroupTheory.rightInverse_of_leftInverse_fin
public abbrev tablePerm := @Theory.GroupTheory.tablePerm

end Sporadic.Mathieu
