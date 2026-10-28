module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.Torus
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.Overlap.FixedSeparation

/-!
# Torus kernels and relative normality for Ree normalizer words

A root-monomial matrix has a unique root permutation, and inversion inverts
that permutation. The coroot torus has identity permutation. Consequently,
conjugating a torus element by any normalizer word has identity permutation
and is height triangular. The explicit triangular-kernel hypothesis then
puts it back in the torus. Taking fixed intersections gives normality inside
the specified normalizer, rather than ambient normality in the Ree group.

Source: GLS3 1.9.5(f) and 2.3.4(a), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.SectionGeometry.BNPair.QuotientGeometry
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Matrix Subgroup
open Parabolics
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open NormalizerGeometry

section Matrices
variable {C R K : Type*} [Fintype C] [Fintype R] [DecidableEq C] [DecidableEq R]
  [Field K]

omit [Fintype C] [Fintype R] in
/-- Nonzero root columns determine their permutation uniquely. -/
theorem monomial_perm_unique {A : Matrix (C ⊕ R) (C ⊕ R) K}
    {e f : Equiv.Perm R} {s t : R → Kˣ}
    (hA : RootMonomial A e s) (hB : RootMonomial A f t) : e = f := by
  ext r
  have h := (hA.1 (.inr (e r)) r).symm.trans (hB.1 (.inr (e r)) r)
  simp only [ite_true, Sum.inr.injEq] at h
  by_contra he
  rw [if_neg he] at h
  exact Units.ne_zero _ h

/-- Inversion retains the exact inverse root permutation and reciprocal scalars. -/
theorem monomial_inv {A : (Matrix (C ⊕ R) (C ⊕ R) K)ˣ}
    {e : Equiv.Perm R} {s : R → Kˣ} (hA : RootMonomial A.val e s) :
    RootMonomial A⁻¹.val e⁻¹ (fun r => (s (e⁻¹ r))⁻¹) := by
  constructor
  · intro i r
    have h := congrArg (fun B : Matrix (C ⊕ R) (C ⊕ R) K => B i (.inr (e⁻¹ r)))
      (congrArg Units.val (inv_mul_cancel A))
    change (A⁻¹.val * A.val) i (.inr (e⁻¹ r)) =
      (1 : Matrix (C ⊕ R) (C ⊕ R) K) i (.inr (e⁻¹ r)) at h
    simp only [Matrix.mul_apply, hA.1, mul_ite, mul_zero] at h
    simp only [Equiv.Perm.inv_def, Equiv.apply_symm_apply, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Matrix.one_apply] at h
    apply (mul_right_cancel₀ (Units.ne_zero (s (e⁻¹ r))))
    exact h.trans (by split_ifs <;> simp_all)
  · intro r c
    have h := congrArg (fun B : Matrix (C ⊕ R) (C ⊕ R) K => B (.inr (e r)) (.inl c))
      (congrArg Units.val (mul_inv_cancel A))
    change (A.val * A⁻¹.val) (.inr (e r)) (.inl c) =
      (1 : Matrix (C ⊕ R) (C ⊕ R) K) (.inr (e r)) (.inl c) at h
    simp only [Matrix.mul_apply, rootMonomial_row hA, Equiv.symm_apply_apply,
      ite_mul, zero_mul] at h
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Matrix.one_apply,
      reduceCtorEq, if_false] at h
    exact (mul_eq_zero.mp h).resolve_left (Units.ne_zero _)

end Matrices

/-- Coroot torus matrices fix every root line. -/
theorem torus_rootMonomial {m : ℕ} {t : SplitGroup m} (ht : t ∈ splitTorus m) :
    ∃ c : F4Chevalley.Root → (CoefficientField m)ˣ,
      RootMonomial t.val.val 1 c := by
  rw [splitTorus_eq_diagonalTorus] at ht
  obtain ⟨u, hu⟩ := ht
  change diagonalTorusHom m u = t.val at hu
  refine ⟨fun r => chevalleyBasisTorusUnit (P := typeF4RootPairing) u (.inr r), ?_⟩
  rw [← hu]
  change RootMonomial (Matrix.diagonal _) 1 _
  constructor
  · intro i r
    simp only [Matrix.diagonal_apply, Equiv.Perm.one_apply]
    split_ifs with h
    · subst i; simp
    · simp [h]
  · intro r c
    simp

/-- The actual F₄ Weyl group acts faithfully on its roots. -/
theorem weyl_perm_injective :
    Function.Injective typeF4RootPairing.weylGroupToPerm := by
  intro w v h
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective
  apply LinearEquiv.toLinearMap_injective
  apply typeF4RootPairing_base.toWeightBasis.ext
  intro i
  simp only [LinearEquiv.coe_coe, RootPairing.Base.toWeightBasis_apply]
  change w • typeF4RootPairing.root i = v • typeF4RootPairing.root i
  rw [typeF4RootPairing.weylGroup_apply_root, typeF4RootPairing.weylGroup_apply_root, h]

/-- The triangular-kernel input makes the torus invariant under normalizer words. -/
theorem torus_conj_mem (m : ℕ)
    (hkernel : ∀ n ∈ splitNormalizerWords m,
      Overlap.IsHeightTriangular n → n ∈ diagonalTorus m)
    {n t : SplitGroup m} (hn : n ∈ splitNormalizerWords m) (ht : t ∈ splitTorus m) :
    n * t * n⁻¹ ∈ splitTorus m := by
  obtain ⟨e, c, hc⟩ := splitNormalizerWords_rootMonomial hn
  obtain ⟨d, hd⟩ := torus_rootMonomial ht
  have hh := rootMonomial_mul (rootMonomial_mul hc hd) (monomial_inv hc)
  simp only [mul_one, mul_inv_cancel] at hh
  rw [splitTorus_eq_diagonalTorus]
  exact hkernel _ ((splitNormalizerWords m).mul_mem
    ((splitNormalizerWords m).mul_mem hn (splitTorus_le_splitNormalizerWords m ht))
    ((splitNormalizerWords m).inv_mem hn))
    (Overlap.heightTriangular_of_rootMonomial_one (n * t * n⁻¹) _ hh)

end QuotientGeometry

open Parabolics
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover

/-- Normality is relative to the concrete normalizer-word subgroup. -/
theorem borel_inf_normalizerWords_normal_of_kernel (m : ℕ)
    (hkernel : ∀ n ∈ splitNormalizerWords m,
      Overlap.IsHeightTriangular n → n ∈ diagonalTorus m) :
    ((borel m ⊓ normalizerWords m).subgroupOf (normalizerWords m)).Normal := by
  rw [borel_inf_normalizerWords]
  constructor
  intro x hx n
  change toSplitGroup m ((n : Model m) * (x : Model m) * (n : Model m)⁻¹) ∈ splitTorus m
  rw [map_mul, map_mul, map_inv]
  exact QuotientGeometry.torus_conj_mem m hkernel n.property hx

end ReeF4.SectionGeometry.BNPair
