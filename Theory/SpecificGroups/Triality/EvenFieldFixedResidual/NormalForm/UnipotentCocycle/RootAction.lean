module

public import Theory.SpecificGroups.Triality.EvenFieldFixedResidual.Twist
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates

/-!
# Scalar and root-curve inputs to binary triality cocycle lifting

The literal coefficient automorphism preserves the split positive subgroup and
acts on each of its twelve integral root curves by the same field automorphism.
For the canonical involution of GF(2^(3n)), with n = 2m and m positive, the
additive trace has image exactly the fixed field. Consequently every fixed
root parameter is a coboundary in its actual root subgroup. This includes m = 1.

The additive trace calculation reuses `Theory.PSL2.fixed_iff_exists_add_conjugate`;
the coefficient-curve calculation follows the existing calculation in
`StandardTwoRank/FourSemilinear/HighestRoot.lean`. These are inputs to the
split-positive filtration argument, not an assumption of its conclusion.

Sources: GLS3 §§2.3–2.5, especially 2.5.13 and 2.5.17,
`refs/KGroup/GLS3/chapter2.tex`; Aschbacher–Smith 16.1.3–4, printed p.1171,
`refs/quasithin.pdf`.
-/

public section
noncomputable section
namespace Triality.Standard.EvenField.NormalForm.UnipotentCocycle
open OuterOdd Parabolics PositiveCoordinates
open Theory.AlgebraicGroup.StandardRootSystem
local instance : DecidableEq ((typeDRootPairing_base 2).support ⊕ TypeDRootIndex (2 + 2)) :=
  instDecidableEqSum

/-- The actual split positive subgroup is invariant under every coefficient automorphism. -/
theorem coefficientSplit_positiveSubgroup (P : Parameters) (e : CoefficientAut P) :
    (positiveSubgroup P).map (coefficientSplit P e).toMonoidHom = positiveSubgroup P := by
  have hm (e : CoefficientAut P) : ∀ x ∈ positiveSubgroup P,
      coefficientSplit P e x ∈ positiveSubgroup P := by
    intro x hx
    have h : positiveSubgroup P ≤ (positiveSubgroup P).comap
        (coefficientSplit P e).toMonoidHom := by
      apply (Subgroup.closure_le _).mpr
      rintro _ ⟨i, t, rfl⟩
      change coefficientSplit P e (positiveRoot P i t) ∈ positiveSubgroup P
      rw [positiveRoot, coefficientSplit_positive]
      exact Subgroup.subset_closure ⟨i, e t, rfl⟩
    exact h hx
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact hm e x hx
  · intro x hx
    refine ⟨coefficientSplit P e⁻¹ x, hm e⁻¹ x hx, ?_⟩
    change coefficientSplit P e (coefficientSplit P e⁻¹ x) = x
    rw [← coefficientSplit_mul, mul_inv_cancel, coefficientSplit_one]

open RootPairing.IntegralGeckConstruction in
/-- Coefficient action on each of the twelve canonical integral root curves. -/
theorem coefficientSplit_curve (P : Parameters) (e : CoefficientAut P)
    (i : Fin 12) (t : ExtensionField P) :
    coefficientSplit P e (curve P i t) = curve P i (e t) := by
  apply Subtype.ext
  apply Units.ext
  change (rootCurveMatrix _ (rootIndex i) t).map e = rootCurveMatrix _ (rootIndex i) (e t)
  ext j k
  simp [rootCurveMatrix, specializeMatrix, Matrix.one_apply]

/-- The published ordered product intertwines the literal coefficient actions. -/
theorem coefficientSplit_orderedProduct (P : Parameters) (e : CoefficientAut P)
    (a : Coordinates P) :
    coefficientSplit P e (orderedProduct P a) = orderedProduct P (fun i => e (a i)) := by
  simp only [orderedProduct, map_list_prod, List.map_ofFn, Function.comp_def,
    coefficientSplit_curve]

/-- Additive Hilbert 90 for the canonical cubic-field involution, including `m = 1`. -/
theorem canonical_scalar_trace (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) (t : ExtensionField (binaryParameters n hn)) :
    coefficientFrobenius n hn (3*m) t = t ↔
      ∃ s, s + coefficientFrobenius n hn (3*m) s = t := by
  have ho := coefficientFrobenius_order_two n hn m hm hnm
  have hs : coefficientFrobenius n hn (3*m) ^ 2 = 1 :=
    ho ▸ pow_orderOf_eq_one _
  apply Theory.PSL2.fixed_iff_exists_add_conjugate _
    (fun x => DFunLike.congr_fun hs x)
  intro he
  have he' : coefficientFrobenius n hn (3*m) = 1 := he
  rw [he', orderOf_one] at ho
  omega

/-- Application of the scalar trace equation in each actual positive root subgroup. -/
theorem canonical_curve_coboundary (n : ℕ) (hn : 0 < n) (m : ℕ) (hm : 0 < m)
    (hnm : n = 2*m) (i : Fin 12) (t : ExtensionField (binaryParameters n hn))
    (ht : coefficientFrobenius n hn (3*m) t = t) :
    ∃ s, curve (binaryParameters n hn) i t = (curve (binaryParameters n hn) i s)⁻¹ *
      coefficientSplit (binaryParameters n hn) (coefficientFrobenius n hn (3*m))
        (curve (binaryParameters n hn) i s) := by
  obtain ⟨s, hs⟩ := (canonical_scalar_trace n hn m hm hnm t).mp ht
  refine ⟨s, ?_⟩
  rw [coefficientSplit_curve, curve_inv, show -s = s from CharTwo.neg_eq s, ← curve_add, hs]

end Triality.Standard.EvenField.NormalForm.UnipotentCocycle
