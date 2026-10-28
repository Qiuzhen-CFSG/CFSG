module

public import Theory.Representation.G2OrthogonalCover.HyperplaneOrbits
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.PGroup

/-!
# The literal orbit actions on cover hyperplanes

Each affine norm fibre carries the action of the full binary octonion group
and its actual derived subgroup. Both are transitive, with orbit lengths 36
and 28; in particular, their hyperplane stabilizers never have index two.

Source: Aschbacher--Smith, Lemma 12.4.8, printed p.815. The coordinate orbit
certificates and attributed octonion conventions are imported unchanged.
-/

@[expose] public noncomputable section
namespace Atlas.G2.Natural.OrthogonalCover.Hyperplanes

local notation "F" => ZMod 2
local notation "D" => commutator (Model F)

/-- A complete orbit of literal off-scalar cover hyperplanes. -/
abbrev Fibre (q : F) := {a : Parameters // normClass a = q}

instance (q : F) : MulAction (Model F) (Fibre q) where
  smul g a := ⟨act g a.val, (normClass_act g a.val).trans a.property⟩
  one_smul a := Subtype.ext (act_one a.val)
  mul_smul g h a := Subtype.ext (act_mul g h a.val)

instance derived_pretransitive (q : F) : MulAction.IsPretransitive D (Fibre q) where
  exists_smul_eq a b := by
    obtain ⟨g, hg⟩ := (exists_derived_act_iff a.val b.val).mpr
      (a.property.trans b.property.symm)
    exact ⟨g, Subtype.ext hg⟩

instance full_pretransitive (q : F) : MulAction.IsPretransitive (Model F) (Fibre q) where
  exists_smul_eq a b := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq D a b
    exact ⟨g.val, hg⟩

theorem card_fibre_zero : Nat.card (Fibre 0) = 36 := by
  rw [Nat.card_eq_fintype_card]
  exact normClass_cards.1

theorem card_fibre_one : Nat.card (Fibre 1) = 28 := by
  rw [Nat.card_eq_fintype_card]
  exact normClass_cards.2

theorem index_derived_stabilizer (q : F) (a : Fibre q) :
    (MulAction.stabilizer D a).index = if q = 0 then 36 else 28 := by
  rw [MulAction.index_stabilizer_of_transitive]
  by_cases hq : q = 0
  · rw [hq, if_pos rfl]
    exact card_fibre_zero
  · have hq1 : q = 1 := (by decide +kernel : ∀ a : ZMod 2, a ≠ 0 → a = 1) q hq
    rw [hq1, if_neg one_ne_zero]
    exact card_fibre_one

theorem index_full_stabilizer (q : F) (a : Fibre q) :
    (MulAction.stabilizer (Model F) a).index = if q = 0 then 36 else 28 := by
  rw [MulAction.index_stabilizer_of_transitive]
  by_cases hq : q = 0
  · rw [hq, if_pos rfl]
    exact card_fibre_zero
  · have hq1 : q = 1 := (by decide +kernel : ∀ a : ZMod 2, a ≠ 0 → a = 1) q hq
    rw [hq1, if_neg one_ne_zero]
    exact card_fibre_one

theorem index_derived_stabilizer_ne_two (q : F) (a : Fibre q) :
    (MulAction.stabilizer D a).index ≠ 2 := by
  rw [index_derived_stabilizer]
  split <;> decide

theorem index_full_stabilizer_ne_two (q : F) (a : Fibre q) :
    (MulAction.stabilizer (Model F) a).index ≠ 2 := by
  rw [index_full_stabilizer]
  split <;> decide

end Atlas.G2.Natural.OrthogonalCover.Hyperplanes
