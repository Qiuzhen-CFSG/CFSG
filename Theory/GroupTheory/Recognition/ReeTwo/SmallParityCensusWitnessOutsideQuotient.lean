module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityCensusWitnessActions
public import Theory.SpecificGroups.ReeTwo.SylowTailQuotient

/-!
# Tail-quotient exclusions for small parity census witnesses

For 38 of the proposed Frattini witnesses, projection to the order-64 tail
quotient separates the witness from its census node. Each bit mask below
defines a subgroup of the quotient containing the projected node generators
and excluding the projected witness. The generator-closure theorem then puts
the entire node in the inverse image of that subgroup.

Source: the root words in `SmallParityCensusWitnessActions` and
`SmallParityCensusNodes`, using the Shinoda (1975), (2.3), coordinate model
and the projection constructed in `SylowTailQuotient`. External computation
selected the masks; Lean's kernel verifies closure, generator membership,
witness nonmembership, and coverage of the stated indices.
-/

namespace ReeTwo.SylowModel


private def selected (i : Fin 38) : Fin 97 :=
  ![0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 38, 40, 41, 44, 45, 46,
    48, 49, 52, 53, 67, 68, 69, 70, 71, 72, 88, 89] i

private def mask (i : Fin 38) : ℕ :=
  ![1153220576333074433, 2306410632234143745, 153127062403026945, 76578790164140033,
    72340172838076673, 9644916007763985, 281479271743489, 1153220576333074433, 1153220576333074433,
    1153220576333074433, 567348008321025, 9011597301776385, 72057598349672449, 76578790164140033,
    76578790164140033, 76578790164140033, 72340172838076673, 72340172838076673, 72340172838076673,
    72340172838076673, 281479271743489, 281479271743489, 1153220576333074433, 567348008321025,
    9011597301776385, 72057598349672449, 72057598349672449, 76578790164140033, 72340172838076673,
    72340172838076673, 281479271743489, 281479271743489, 567348008321025, 9011597301776385,
    72057598349672449, 72057598349672449, 567348008321025, 9011597301776385] i

private def member (i : Fin 38) (q : TailQuotient.Group) : Prop :=
  (mask i).testBit (TailQuotient.coordinateCode q) = true

private instance (i : Fin 38) (q : TailQuotient.Group) : Decidable (member i q) :=
  inferInstanceAs (Decidable (_ = _))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in

private theorem closed : ∀ i : Fin 38,
    member i 1 ∧ (∀ a b : TailQuotient.Group, member i a → member i b → member i (a * b)) ∧
      (∀ a : TailQuotient.Group, member i a → member i a⁻¹) := by decide +kernel

private def bound (i : Fin 38) : Subgroup TailQuotient.Group where
  carrier := member i
  one_mem' := (closed i).1
  mul_mem' := (closed i).2.1 _ _
  inv_mem' := (closed i).2.2 _

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in

private theorem generators_mem : ∀ (i : Fin 38) (j : Fin 9),
    member i (TailQuotient.projection (smallParityCensusWitnessGenerator (selected i) j)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in

private theorem witness_outside : ∀ i : Fin 38,
    ¬ member i (TailQuotient.projection (smallParityCensusWitness (selected i))) := by
  decide +kernel

private theorem node_le (i : Fin 38) :
    smallParityCensusNode (smallParityCensusWitnessIndex (selected i)) ≤
      (bound i).comap TailQuotient.projection := by
  rw [smallParityCensusWitnessGenerator_closure]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨j, rfl⟩
  exact generators_mem i j

private theorem outside_selected (i : Fin 38) :
    smallParityCensusWitness (selected i) ∉
      smallParityCensusNode (smallParityCensusWitnessIndex (selected i)) := by
  intro h
  exact witness_outside i (node_le i h)

/-- The tail quotient separates these thirty-eight witnesses from their nodes. -/
public theorem smallParityCensusWitness_not_mem_of_quotient
    (k : Fin 97) (hk : k.val ∈ ({0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
    21, 22, 38, 40, 41, 44, 45, 46, 48, 49, 52, 53, 67, 68, 69, 70, 71, 72, 88, 89} : Finset ℕ)) :
    smallParityCensusWitness k ∉ smallParityCensusNode (smallParityCensusWitnessIndex k) := by
  have hc : ∀ k : Fin 97, k.val ∈ ({0, 1, 2, 3, 4, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
    21, 22, 38, 40, 41, 44, 45, 46, 48, 49, 52, 53, 67, 68, 69, 70, 71, 72, 88, 89} : Finset ℕ) →
      ∃ i : Fin 38, k = selected i := by decide +kernel
  obtain ⟨i, rfl⟩ := hc k hk
  exact outside_selected i

end ReeTwo.SylowModel
