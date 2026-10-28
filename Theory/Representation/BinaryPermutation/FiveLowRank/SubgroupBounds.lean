module
public import Theory.Representation.BinaryPermutation.FiveLowRank
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.FieldTheory.Finiteness

/-!
# Low-rank obstructions in the binary five-point core

An even permutation cannot have displacement rank one. In particular it
cannot fix an arbitrary eight-element subgroup pointwise. The dimension
and rank-nullity bounds turn the concrete low-rank calculation into these
coordinate-independent tests used on the original quaternion seed.

Source: Aschbacher–Smith,G.2.4(8), printed p.335.
-/

@[expose] public section
open Subgroup
namespace BinaryPermutation.FiveLowRank
theorem even_low_rank (a : alternatingGroup (Fin 5))
    (h : Module.finrank (ZMod 2) (LinearMap.range
      (BinaryPermutation.coreRepresentation (Fin 5) a.val - LinearMap.id)) ≤ 1) : a = 1 := by
  rcases BinaryPermutation.FiveLowRank.low_rank a.val h with ha | ⟨i,j,hij,ha⟩
  · exact Subtype.ext ha
  · have hm := a.property
    rw [Equiv.Perm.mem_alternatingGroup, ha, Equiv.Perm.sign_swap hij] at hm
    exact False.elim ((by decide : (-1 : ℤˣ) ≠ 1) hm)

private noncomputable def subspace : Subgroup (Multiplicative (BinaryPermutation.core (Fin 5))) ≃o
    Submodule (ZMod 2) (BinaryPermutation.core (Fin 5)) :=
  AddSubgroup.toSubgroup.symm.trans (AddSubgroup.toZModSubmodule 2)

private theorem subspace_card (A : Subgroup (Multiplicative (BinaryPermutation.core (Fin 5)))) :
    Nat.card A = 2 ^ Module.finrank (ZMod 2) (subspace A) := by
  have he : Nat.card A = Nat.card (subspace A) := rfl
  rw [he, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

/-- An even five-point permutation fixing an eight-subgroup of the core is trivial. -/
theorem eq_one_of_fixes_eight (a : alternatingGroup (Fin 5))
    (A : Subgroup (Multiplicative (BinaryPermutation.core (Fin 5)))) (hA : Nat.card A = 8)
    (hfix : ∀ x ∈ A, BinaryPermutation.coreRepresentation (Fin 5) a.val x.toAdd = x.toAdd) :
    a = 1 := by
  let f := BinaryPermutation.coreRepresentation (Fin 5) a.val - LinearMap.id
  have hdim : Module.finrank (ZMod 2) (subspace A) = 3 := by
    have h := subspace_card A
    rw [hA] at h
    exact Nat.pow_right_injective (by decide : 1 < 2) h.symm
  have hle : subspace A ≤ f.ker := by
    intro x hx
    exact sub_eq_zero.mpr (hfix (Multiplicative.ofAdd x) hx)
  have hk : 3 ≤ Module.finrank (ZMod 2) f.ker := by
    simpa only [hdim] using Submodule.finrank_mono hle
  have hr := LinearMap.finrank_range_add_finrank_ker f
  norm_num only [BinaryPermutation.finrank_core, Fintype.card_fin] at hr
  apply even_low_rank a
  change Module.finrank (ZMod 2) f.range ≤ 1
  omega

/-- An even five-point permutation with displacement in a two-subgroup is trivial. -/
theorem eq_one_of_displacement_two (a : alternatingGroup (Fin 5))
    (A : Subgroup (Multiplicative (BinaryPermutation.core (Fin 5)))) (hA : Nat.card A = 2)
    (hmove : ∀ x : BinaryPermutation.core (Fin 5),
      Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 5) a.val x - x) ∈ A) :
    a = 1 := by
  have hdim : Module.finrank (ZMod 2) (subspace A) = 1 := by
    have h := subspace_card A
    rw [hA] at h
    exact Nat.pow_right_injective (by decide : 1 < 2) h.symm
  apply even_low_rank a
  have hle : LinearMap.range
      (BinaryPermutation.coreRepresentation (Fin 5) a.val - LinearMap.id) ≤ subspace A := by
    rintro _ ⟨x, rfl⟩
    exact hmove x
  exact (Submodule.finrank_mono hle).trans hdim.le



end BinaryPermutation.FiveLowRank
end
