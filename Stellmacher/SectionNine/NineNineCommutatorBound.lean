module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic

/-!
# The maximal commutator-bounded subgroup in Stellmacher (9.9)

When the ambient subgroup normalizes the target, elements whose commutators
with the acting subgroup belong to the target form a subgroup. Its universal
property identifies the source's maximal subgroup without making a choice.
An index-two intersection contained in a core, together with a commutator
bound for that core intersection, bounds the index of this maximal subgroup.

This supplies the last algebraic step on printed pp.56–57 of
`refs/files/stellmacher-n-group.pdf`. It does not produce the source's
normalizer/conjugation configuration or assert the numbered distance bound.
-/

open scoped commutatorElement

namespace Stellmacher.SectionNine

universe u

@[expose] public def nineNineCommutatorBound
    {G : Type u} [Group G] (ambient acting target : Subgroup G)
    (hnormalizes : ambient ≤ Subgroup.normalizer (target : Set G)) : Subgroup G where
  carrier := {element | element ∈ ambient ∧
    ∀ actor ∈ acting, ⁅element, actor⁆ ∈ target}
  one_mem' := ⟨ambient.one_mem, by simp⟩
  mul_mem' := by
    rintro first second ⟨hfirst, hfirstComm⟩ ⟨hsecond, hsecondComm⟩
    refine ⟨ambient.mul_mem hfirst hsecond, ?_⟩
    intro actor hactor
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact target.mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hnormalizes hfirst) _).mp
        (hsecondComm actor hactor)) (hfirstComm actor hactor)
  inv_mem' := by
    rintro element ⟨helement, hcomm⟩
    refine ⟨ambient.inv_mem helement, ?_⟩
    intro actor hactor
    rw [commutatorElement_inv_left, ← commutatorElement_inv]
    simpa using
      (Subgroup.mem_normalizer_iff.mp (hnormalizes (ambient.inv_mem helement)) _).mp
        (target.inv_mem (hcomm actor hactor))

public theorem le_nineNineCommutatorBound_iff
    {G : Type u} [Group G] (ambient acting target candidate : Subgroup G)
    (hnormalizes : ambient ≤ Subgroup.normalizer (target : Set G)) :
    candidate ≤ nineNineCommutatorBound ambient acting target hnormalizes ↔
      candidate ≤ ambient ∧ ⁅candidate, acting⁆ ≤ target := by
  constructor
  · intro hle
    exact ⟨fun element helement => (hle helement).1,
      Subgroup.commutator_le.mpr (fun element helement => (hle helement).2)⟩
  · rintro ⟨hle, hcomm⟩ element helement
    exact ⟨hle helement, Subgroup.commutator_le.mp hcomm element helement⟩

public theorem nine_nine_maximal_commutator_index
    {G : Type u} [Group G] [Finite G]
    (ambient acting target localGroup core : Subgroup G)
    (hnormalizes : ambient ≤ Subgroup.normalizer (target : Set G))
    (hindex : Nat.card ambient = 2 * Nat.card (ambient ⊓ localGroup : Subgroup G))
    (hcore : ambient ⊓ localGroup ≤ core)
    (hcomm : ⁅ambient ⊓ core, acting⁆ ≤ target) :
    Nat.card ambient ≤
      2 * Nat.card (nineNineCommutatorBound ambient acting target hnormalizes) := by
  have hle : ambient ⊓ localGroup ≤
      nineNineCommutatorBound ambient acting target hnormalizes := by
    apply (le_nineNineCommutatorBound_iff ambient acting target _ hnormalizes).mpr
    exact ⟨inf_le_left,
      (Subgroup.commutator_mono (le_inf inf_le_left hcore) le_rfl).trans hcomm⟩
  rw [hindex]
  exact Nat.mul_le_mul_left 2 (Subgroup.card_le_of_le hle)

public theorem nine_nine_maximal_commutator_contradiction
    {G : Type u} [Group G] [Finite G]
    (ambient acting target localGroup core : Subgroup G)
    (hnormalizes : ambient ≤ Subgroup.normalizer (target : Set G))
    (hlarge : 4 * Nat.card (nineNineCommutatorBound ambient acting target hnormalizes) ≤
      Nat.card ambient)
    (hindex : Nat.card ambient = 2 * Nat.card (ambient ⊓ localGroup : Subgroup G))
    (hcore : ambient ⊓ localGroup ≤ core)
    (hcomm : ⁅ambient ⊓ core, acting⁆ ≤ target) : False := by
  have hsmall := nine_nine_maximal_commutator_index ambient acting target localGroup core
    hnormalizes hindex hcore hcomm
  have hpositive := Nat.card_pos
    (α := nineNineCommutatorBound ambient acting target hnormalizes)
  omega

end Stellmacher.SectionNine
