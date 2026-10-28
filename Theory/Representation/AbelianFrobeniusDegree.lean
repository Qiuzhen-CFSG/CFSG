module

public import Theory.Representation.AbelianWeightAutomizer
public import Theory.Representation.ExtendScalars
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.FixedPointFree

/-!
# Degree bounds from abelian Frobenius kernels

A subgroup acting freely by conjugation on a nontrivial finite abelian kernel
has order at most the degree of every faithful cross-characteristic
representation. Over an algebraically closed field, faithfulness supplies a
nontrivial occurring character. Its stabilizer is trivial: the commutator map
of a fixed-point-free automorphism is surjective, and an invariant character
is trivial on that map. The independent character spaces bound the orbit size.
Scalar extension proves the same statement over an arbitrary field, without
assuming irreducibility of the whole representation.

This is the representation-theoretic argument for the Frobenius exclusions in
Aschbacher--Smith, *The Classification of Quasithin Groups*, G.7.2(2),
combined manuscript of 1 March 2004, printed pp.347--348.
-/

public section

open scoped IsMulCommutative
namespace Representation

private theorem character_eq_one_of_fixedPointFree {K A : Type*}
    [Group K] [Finite K] [Group A]
    (a : MulAut K) (hfixed : MonoidHom.FixedPointFree a)
    (chi : K →* A) (hchi : ∀ k, chi (a k) = chi k) : chi = 1 := by
  ext k
  obtain ⟨x, rfl⟩ := hfixed.commutatorMap_surjective k
  change chi (x / a x) = 1
  rw [map_div, hchi, div_self']

variable {E G V : Type*} [Field E] [Group G] [AddCommGroup V] [Module E V]

/-- A free conjugation action on an abelian kernel gives a free orbit of weights. -/
theorem card_le_finrank_of_fixedPointFree_normalizer [IsAlgClosed E]
    [FiniteDimensional E V] (rho : Representation E G V)
    (K C : Subgroup G) [Finite K] [Nontrivial K] [IsMulCommutative K]
    (hrho : Function.Injective rho) (horder : (Nat.card K : E) ≠ 0)
    (hnorm : C ≤ (Subgroup.normalizer (K : Set G)))
    (hfree : ∀ c : C, c ≠ 1 → ∀ k : K,
      (c : G) * k * (c : G)⁻¹ = k → k = 1) :
    Nat.card C ≤ Module.finrank E V := by
  classical
  let n : C →* (Subgroup.normalizer (K : Set G)) := Subgroup.inclusion hnorm
  let a : C →* MulAut K := K.normalizerMonoidHom.comp n
  let p : C →* Equiv.Perm (CharacterWeight (rho.comp K.subtype)) :=
    (automizerWeightPerm rho K).comp (K.normalizerMonoidHom.rangeRestrict.comp n)
  obtain ⟨k, hk⟩ := exists_ne (1 : K)
  have hchi : ∃ chi : CharacterWeight (rho.comp K.subtype), chi.val ≠ 1 := by
    by_contra! h
    apply hk
    apply eq_of_characterWeight_values (rho.comp K.subtype)
      (hrho.comp Subtype.val_injective) horder
    intro chi
    simp [h chi]
  obtain ⟨chi, hchi⟩ := hchi
  have hp (c : C) : (p c chi).val = chi.val.comp (a c).symm.toMonoidHom := rfl
  have hstab (c : C) (hc : p c chi = chi) : c = 1 := by
    by_contra hne
    apply hchi
    apply character_eq_one_of_fixedPointFree (a c).symm
    · intro x hx
      apply hfree c hne x
      have hx' : a c x = x := by
        exact (congrArg (a c) hx).symm.trans ((a c).apply_symm_apply x)
      exact congrArg Subtype.val hx'
    · intro x
      exact DFunLike.congr_fun ((hp c).symm.trans (congrArg Subtype.val hc)) x
  have hinj : Function.Injective (fun c : C => p c chi) := by
    intro c d h
    change p c chi = p d chi at h
    have hcd : p (d⁻¹ * c) chi = chi := by
      rw [map_mul, map_inv]
      change (p d).symm (p c chi) = chi
      rw [h]
      exact (p d).symm_apply_apply chi
    exact (inv_mul_eq_one.mp (hstab _ hcd)).symm
  obtain ⟨hfinite, hcard⟩ := characterWeight_card_le (rho.comp K.subtype) horder
  let := hfinite
  exact (Nat.card_le_card_of_injective _ hinj).trans hcard

/-- The Frobenius degree bound over any cross-characteristic coefficient field. -/
theorem card_le_finrank_of_fixedPointFree_normalizer_of_field
    [FiniteDimensional E V] (rho : Representation E G V)
    (K C : Subgroup G) [Finite K] [Nontrivial K] [IsMulCommutative K]
    (hrho : Function.Injective rho) (horder : (Nat.card K : E) ≠ 0)
    (hnorm : C ≤ (Subgroup.normalizer (K : Set G)))
    (hfree : ∀ c : C, c ≠ 1 → ∀ k : K,
      (c : G) * k * (c : G)⁻¹ = k → k = 1) :
    Nat.card C ≤ Module.finrank E V := by
  let L := AlgebraicClosure E
  have horder' : (Nat.card K : L) ≠ 0 := by
    intro h
    apply horder
    apply (algebraMap E L).injective
    simpa using h
  have h := card_le_finrank_of_fixedPointFree_normalizer (rho.extendScalars L) K C
    ((extendScalars_faithful_iff L rho).mp hrho) horder' hnorm hfree
  simpa only [Module.finrank_baseChange] using h

end Representation
