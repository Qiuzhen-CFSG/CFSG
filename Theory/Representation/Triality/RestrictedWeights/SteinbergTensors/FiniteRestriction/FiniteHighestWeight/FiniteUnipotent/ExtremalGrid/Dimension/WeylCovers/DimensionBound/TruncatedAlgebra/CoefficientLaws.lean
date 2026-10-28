module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.RootOperators
public import Mathlib.Algebra.Polynomial.Taylor
public import Theory.AlgebraicGroup.RootSubgroups.GeneratedSubgroup

/-!
# One-root coefficient algebra and torus transport

The polynomial orbit of an additive root group intertwines translation with
Hasse differentiation. Taking two coefficients gives the divided-power product
law without dividing by factorials. At a power of the characteristic, the
binomial coefficient vanishes whenever addition crosses the truncation bound.
Consequently the truncated coefficients for one root span a subalgebra.

We also transport coefficients through scaled intertwiners, prove commutation
for commuting root groups, and prove the torus action and vanishing of positive
coefficients on highest vectors. These results do not assert PBW spanning or
normalization by the full ambient group. Opposite-root straightening and the
noncommuting root-pair relations remain separate obligations.

Source: Steinberg, *Representations of algebraic groups*, Nagoya Math. J. 22
(1963), §2, with higher polynomial coefficients for characteristic powers.
The torus formula respects the raw inverse-conjugation root convention.
-/

open Theory.AlgebraicGroup
open Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension

public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Translating the root parameter translates its matrix-coefficient polynomial. -/
theorem curvePolynomial_action (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (x : Morphism (KPlus k) K) (l : Module.Dual k V) (v : V) (t : k) :
    curvePolynomial rho hr x l ((rho.action (x.onPoints (kPlusPoint t))).val v) =
      Polynomial.taylor t (curvePolynomial rho hr x l v) := by
  apply Polynomial.funext
  intro s
  simp only [Polynomial.taylor_apply, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C, curvePolynomial_eval]
  rw [← kPlusPoint_mul, map_mul, map_mul, Units.val_mul, Module.End.mul_apply]

/-- Composing a covector with a coefficient is Hasse differentiation. -/
theorem curvePolynomial_dual_coefficient (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (x : Morphism (KPlus k) K) (l : Module.Dual k V) (v : V) (i : ℕ) :
    curvePolynomial rho hr x (l.comp (curveCoefficient rho hr x i)) v =
      Polynomial.hasseDeriv i (curvePolynomial rho hr x l v) := by
  apply Polynomial.funext
  intro t
  rw [curvePolynomial_eval, LinearMap.comp_apply, dual_curveCoefficient]
  rw [curvePolynomial_action, Polynomial.taylor_coeff]

/-- Coefficient multiplication for an additive root group, in every characteristic. -/
theorem curveCoefficient_mul (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x : Morphism (KPlus k) K) (i j : ℕ) :
    curveCoefficient rho hr x i * curveCoefficient rho hr x j =
      ((i + j).choose i : k) • curveCoefficient rho hr x (i + j) := by
  ext v
  apply (Module.finBasis k V).repr.injective
  ext b
  change (Module.finBasis k V).coord b
    (curveCoefficient rho hr x i (curveCoefficient rho hr x j v)) =
      (Module.finBasis k V).coord b
        (((i + j).choose i : k) • curveCoefficient rho hr x (i + j) v)
  change ((Module.finBasis k V).coord b).comp (curveCoefficient rho hr x i)
    (curveCoefficient rho hr x j v) = _
  rw [dual_curveCoefficient, curvePolynomial_dual_coefficient, Polynomial.hasseDeriv_coeff]
  simp only [map_smul, dual_curveCoefficient, smul_eq_mul,
    Nat.add_comm j i]

omit [IsAlgClosed k] in
/-- Crossing a power-of-two truncation bound forces a binary carry. -/
theorem choose_add_eq_zero_of_binary_carry [CharP k 2] (n i j : ℕ)
    (hi : i < 2 ^ n) (hj : j < 2 ^ n) (hij : 2 ^ n ≤ i + j) :
    ((i + j).choose i : k) = 0 := by
  let m := i + j - 2 ^ n
  have hm : m < i := by dsimp [m]; omega
  have he : i + j = m + 2 ^ n := by dsimp [m]; omega
  rw [← Polynomial.coeff_X_add_one_pow k]
  rw [he, pow_add, add_pow_char_pow, one_pow, mul_add, mul_one,
    Polynomial.coeff_add, Polynomial.coeff_mul_X_pow']
  simp only [not_le.mpr hi, if_false, zero_add]
  rw [Polynomial.coeff_X_add_one_pow, Nat.choose_eq_zero_of_lt hm, Nat.cast_zero]

/-- Products crossing the truncation bound vanish in characteristic two. -/
theorem curveCoefficient_mul_eq_zero [CharP k 2]
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (x : Morphism (KPlus k) K) (n i j : ℕ)
    (hi : i < 2 ^ n) (hj : j < 2 ^ n) (hij : 2 ^ n ≤ i + j) :
    curveCoefficient rho hr x i * curveCoefficient rho hr x j = 0 := by
  rw [curveCoefficient_mul, choose_add_eq_zero_of_binary_carry n i j hi hj hij, zero_smul]

/-- Transport all coefficients through a parameter-scaled intertwiner. -/
theorem curveCoefficient_intertwine (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x y : Morphism (KPlus k) K)
    (L : Module.End k V) (c : k)
    (h : ∀ t, L * (rho.action (x.onPoints (kPlusPoint t))).val =
      (rho.action (y.onPoints (kPlusPoint (c * t)))).val * L) (j : ℕ) :
    L * curveCoefficient rho hr x j =
      c ^ j • (curveCoefficient rho hr y j * L) := by
  ext v
  apply (Module.finBasis k V).repr.injective
  ext b
  let l := (Module.finBasis k V).coord b
  have hp : curvePolynomial rho hr x (l.comp L) v =
      (curvePolynomial rho hr y l (L v)).comp (Polynomial.C c * Polynomial.X) := by
    apply Polynomial.funext
    intro t
    simp only [curvePolynomial_eval, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, LinearMap.comp_apply]
    exact congrArg l (LinearMap.congr_fun (h t) v)
  change (l.comp L) (curveCoefficient rho hr x j v) =
    l (c ^ j • curveCoefficient rho hr y j (L v))
  rw [dual_curveCoefficient, hp, Polynomial.comp_C_mul_X_coeff, map_smul,
    dual_curveCoefficient, smul_eq_mul, mul_comm]

/-- Positive coefficients kill a vector fixed by the one-parameter group. -/
theorem curveCoefficient_eq_zero_of_fixed (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x : Morphism (KPlus k) K) (v : V)
    (hv : ∀ t, (rho.action (x.onPoints (kPlusPoint t))).val v = v)
    (j : ℕ) (hj : j ≠ 0) : curveCoefficient rho hr x j v = 0 := by
  apply (Module.finBasis k V).repr.injective
  ext b
  let l := (Module.finBasis k V).coord b
  have hp : curvePolynomial rho hr x l v = Polynomial.C (l v) := by
    apply Polynomial.funext
    intro t
    simp only [curvePolynomial_eval, hv, Polynomial.eval_C]
  change l (curveCoefficient rho hr x j v) = l 0
  rw [dual_curveCoefficient, hp, Polynomial.coeff_C, if_neg hj, map_zero]

/-- Commuting root subgroups have commuting coefficients in every degree. -/
theorem curveCoefficient_commute (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x y : Morphism (KPlus k) K)
    (h : ∀ s t, Commute (x.onPoints (kPlusPoint s)) (y.onPoints (kPlusPoint t)))
    (i j : ℕ) : Commute (curveCoefficient rho hr x i) (curveCoefficient rho hr y j) := by
  change _ * _ = _ * _
  have hx (s : k) : (rho.action (x.onPoints (kPlusPoint s))).val *
      curveCoefficient rho hr y j =
        curveCoefficient rho hr y j * (rho.action (x.onPoints (kPlusPoint s))).val := by
    have hs := curveCoefficient_intertwine rho hr y y
      (rho.action (x.onPoints (kPlusPoint s))).val 1 (fun t => ?_) j
    · simpa only [one_pow, one_smul] using hs
    simpa only [one_mul, ← Units.val_mul, ← map_mul] using
      congrArg (fun g => (rho.action g).val) (h s t).eq
  have hi := curveCoefficient_intertwine rho hr x x
    (curveCoefficient rho hr y j) 1 (fun s => ?_) i
  · simpa only [one_pow, one_smul] using hi.symm
  simpa only [one_mul] using (hx s).symm

/-- The span of the first q coefficients on one root curve. -/
@[expose] def truncatedCurveSpan (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x : Morphism (KPlus k) K) (q : ℕ) :
    Submodule k (Module.End k V) :=
  Submodule.span k (Set.range fun j : Fin q => curveCoefficient rho hr x j)

theorem curveCoefficient_mem_truncatedCurveSpan (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x : Morphism (KPlus k) K) (q j : ℕ)
    (hj : j < q) : curveCoefficient rho hr x j ∈ truncatedCurveSpan rho hr x q :=
  Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩

theorem one_mem_truncatedCurveSpan (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x : Morphism (KPlus k) K) (q : ℕ)
    (hq : 0 < q) : 1 ∈ truncatedCurveSpan rho hr x q := by
  simpa only [curveCoefficient_zero] using
    curveCoefficient_mem_truncatedCurveSpan rho hr x q 0 hq

theorem truncatedCurveSpan_mul_mem [CharP k 2] (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x : Morphism (KPlus k) K) (n : ℕ)
    (a b : Module.End k V) (ha : a ∈ truncatedCurveSpan rho hr x (2 ^ n))
    (hb : b ∈ truncatedCurveSpan rho hr x (2 ^ n)) :
    a * b ∈ truncatedCurveSpan rho hr x (2 ^ n) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨i, rfl⟩ := ha
    induction hb using Submodule.span_induction with
    | mem b hb =>
      obtain ⟨j, rfl⟩ := hb
      by_cases hij : i.val + j.val < 2 ^ n
      · rw [curveCoefficient_mul]
        exact (truncatedCurveSpan rho hr x (2 ^ n)).smul_mem _
          (curveCoefficient_mem_truncatedCurveSpan rho hr x (2 ^ n) _ hij)
      · rw [curveCoefficient_mul_eq_zero rho hr x n i j i.isLt j.isLt (by omega)]
        exact Submodule.zero_mem _
    | zero => simpa only [mul_zero] using (truncatedCurveSpan rho hr x (2 ^ n)).zero_mem
    | add a b _ _ ha hb =>
      simpa only [mul_add] using (truncatedCurveSpan rho hr x (2 ^ n)).add_mem ha hb
    | smul c a _ ha =>
      simpa only [mul_smul_comm] using (truncatedCurveSpan rho hr x (2 ^ n)).smul_mem c ha
  | zero => simpa only [zero_mul] using (truncatedCurveSpan rho hr x (2 ^ n)).zero_mem
  | add a b _ _ ha hb =>
    simpa only [add_mul] using (truncatedCurveSpan rho hr x (2 ^ n)).add_mem ha hb
  | smul c a _ ha =>
    simpa only [smul_mul_assoc] using (truncatedCurveSpan rho hr x (2 ^ n)).smul_mem c ha

/-- The one-root algebra really is spanned by orders below the characteristic power. -/
theorem adjoin_curveCoefficients_toSubmodule [CharP k 2]
    (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (x : Morphism (KPlus k) K) (n : ℕ) :
    (Algebra.adjoin k (Set.range fun j : Fin (2 ^ n) =>
      curveCoefficient rho hr x j)).toSubmodule = truncatedCurveSpan rho hr x (2 ^ n) := by
  let U := truncatedCurveSpan rho hr x (2 ^ n)
  let A := U.toSubalgebra (one_mem_truncatedCurveSpan rho hr x (2 ^ n) (by positivity))
    (truncatedCurveSpan_mul_mem rho hr x n)
  apply le_antisymm
  · change (Algebra.adjoin k _).toSubmodule ≤ A.toSubmodule
    apply Subalgebra.toSubmodule.monotone
    rw [Algebra.adjoin_le_iff]
    rintro a ⟨j, rfl⟩
    exact curveCoefficient_mem_truncatedCurveSpan rho hr x (2 ^ n) _ j.isLt
  · apply Submodule.span_le.mpr
    intro a ha
    exact Algebra.subset_adjoin ha

variable [CharP k 2]
open Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction
open Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid

theorem rootCoefficient_mul (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (r : S.roots.Root) (i j : ℕ) :
    rootCoefficient S rho hr r i * rootCoefficient S rho hr r j =
      ((i + j).choose i : k) • rootCoefficient S rho hr r (i + j) :=
  curveCoefficient_mul rho hr (rootCurve S r) i j

theorem rootCoefficient_mul_eq_zero (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (r : S.roots.Root) (n i j : ℕ)
    (hi : i < 2 ^ n) (hj : j < 2 ^ n) (hij : 2 ^ n ≤ i + j) :
    rootCoefficient S rho hr r i * rootCoefficient S rho hr r j = 0 :=
  curveCoefficient_mul_eq_zero rho hr (rootCurve S r) n i j hi hj hij

/-- Direct conjugation uses the inverse of the raw root character. -/
theorem rootCoefficient_torus (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (r : S.roots.Root)
    (t : Variety.Point S.torus.carrierVariety) (j : ℕ) :
    (rho.action (S.torus.includePoint t)).val * rootCoefficient S rho hr r j =
      ((S.roots.rootWeight r).pointCharacter t⁻¹) ^ j •
        (rootCoefficient S rho hr r j * (rho.action (S.torus.includePoint t)).val) := by
  apply curveCoefficient_intertwine
  intro s
  have h := (S.realized.2.2.1 r).2 (S.rootParameter r) s t⁻¹
  rw [show S.torus.includePoint t⁻¹ = (S.torus.includePoint t)⁻¹ from
    map_inv S.torus.inclusion.onPoints t, inv_inv] at h
  have he : S.torus.includePoint t * (rootCurve S r).onPoints (kPlusPoint s) =
      (rootCurve S r).onPoints
        (kPlusPoint ((S.roots.rootWeight r).pointCharacter t⁻¹ * s)) *
          S.torus.includePoint t := by
    exact (mul_inv_eq_iff_eq_mul).mp h
  simpa only [map_mul, Units.val_mul] using congrArg (fun g => (rho.action g).val) he

omit [CharP k 2] [IsAlgClosed k] [FiniteDimensional k V] in
theorem adjoin_intertwine_mem (X : Set (Module.End k V)) (L : Module.End k V)
    (h : ∀ a ∈ X, ∃ b ∈ Algebra.adjoin k X, L * a = b * L)
    (a : Module.End k V) (ha : a ∈ Algebra.adjoin k X) :
    ∃ b ∈ Algebra.adjoin k X, L * a = b * L := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha => exact h a ha
  | algebraMap c => exact ⟨algebraMap k (Module.End k V) c,
      (Algebra.adjoin k X).algebraMap_mem c, (Algebra.commutes c L).symm⟩
  | add a b _ _ ha hb =>
    obtain ⟨a', ha', ea⟩ := ha
    obtain ⟨b', hb', eb⟩ := hb
    exact ⟨a' + b', (Algebra.adjoin k X).add_mem ha' hb', by rw [mul_add, ea, eb, add_mul]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨a', ha', ea⟩ := ha
    obtain ⟨b', hb', eb⟩ := hb
    exact ⟨a' * b', (Algebra.adjoin k X).mul_mem ha' hb', by
      rw [← mul_assoc, ea, mul_assoc, eb, ← mul_assoc]⟩

/-- Every actual torus point transports the entire root-coefficient algebra. -/
theorem coefficientAlgebra_torus (S : Geometry K) (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (q : ℕ) (t : Variety.Point S.torus.carrierVariety)
    (a : Module.End k V) (ha : a ∈ coefficientAlgebra S rho hr q) :
    ∃ b ∈ coefficientAlgebra S rho hr q,
      (rho.action (S.torus.includePoint t)).val * a = b * (rho.action (S.torus.includePoint t)).val := by
  apply adjoin_intertwine_mem _ _ _ a ha
  rintro _ ⟨⟨r, j⟩, rfl⟩
  refine ⟨((S.roots.rootWeight r).pointCharacter t⁻¹) ^ j.val • rootCoefficient S rho hr r j,
    (coefficientAlgebra S rho hr q).smul_mem (rootCoefficient_mem S rho hr q r j j.isLt) _, ?_⟩
  rw [smul_mul_assoc]
  exact rootCoefficient_torus S rho hr r t j

/-- Every positive-degree coefficient from the chosen Borel kills a high vector. -/
theorem rootCoefficient_eq_zero_of_highWeight
    (S : Geometry K) (rho : RationalRepresentation K V) (hr : IsRationalRepresentation rho)
    (Q : Set S.roots.Root) (B : ClosedSubgroup K)
    (hB : IsBorelOfPositiveSystem S.roots Q B)
    (v : V) (chi : TorusWeight S.torus) (hv : HasHighWeight rho B S.torus v chi)
    (r : S.roots.Root) (hrQ : r ∈ Q) (j : ℕ) (hj : j ≠ 0) :
    rootCoefficient S rho hr r j v = 0 := by
  apply curveCoefficient_eq_zero_of_fixed rho hr (rootCurve S r) v _ j hj
  intro t
  apply invariantLine_fixed_of_unipotent_subgroup rho hr B hB.unipotent v
    hv.1 hB.radical.1 hB.radical.2.1
  change (rootCurve S r).onPoints (kPlusPoint t) ∈ hB.unipotent.toSubgroup
  rw [hB.root_generated]
  apply rootSubgroup_le_RootSubgroupGenerated S.roots hrQ
  exact ((S.roots.rootSubgroup r).pointEquiv ((S.rootParameter r).value t)).property

end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
