module

public import Theory.Representation.SL2.HighestWeightBasis
public import Theory.Representation.BinaryOffender.NaturalTensorFixedCodimension.Basic
public import Theory.SpecificGroups.PSL2.InvolutionFusion
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Algebra.CharP.Two

/-!
# Involution displacement on binary highest-weight spans

For a positive restricted weight in characteristic two, the Weyl matrix
exchanges the admissible binomial monomials in pairs. The only possible fixed
index is the middle coefficient, which is even and therefore inadmissible.
Projection onto one member of each pair embeds fixed vectors into the actual
displacement image. Rank-nullity gives the half-dimension bound, and genuine
SL₂ conjugacy transports it to every nonidentity involution.

The weighted-monomial construction follows `HighestWeightBasis`; its private
spanning calculation is repeated here to preserve that existing module's API
and avoid rebuilding its consumers. No small-module recognition is used.

Source: Guralnick–Malle, Classification of 2F-modules II, §3.5 and
Proposition 4.1(2), manuscript pp.20,22; Aschbacher–Smith, K.3.1,
printed pp.453–454. This is the inner involution calculation before the
source's degree selection.
-/

open MvPolynomial
open scoped MatrixGroups
open Representation.BinaryOffender.NaturalTensor
namespace Representation.SL2.BinaryInvolutionDisplacement
variable {K F : Type*} [Field K] [Field F]

private noncomputable def weightedMonomial (n : ℕ) (r : Fin (n + 1)) : MvPolynomial (Fin 2) F :=
  (n.choose r : F) • (X 0 ^ (r : ℕ) * X 1 ^ (n-r))

private theorem binomial_expansion (n : ℕ) (a b : F) :
    (C a * X 0 + C b * X 1 : MvPolynomial (Fin 2) F) ^ n =
      ∑ r : Fin (n+1), (a ^ (r : ℕ) * b ^ (n-r)) • weightedMonomial n r := by
  rw [add_pow, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r _
  simp only [weightedMonomial, mul_pow, Algebra.smul_def, map_mul, map_pow,
    map_natCast, MvPolynomial.algebraMap_eq]
  ring

private theorem action_X_pow (e : K →+* F) (n : ℕ) (g : SL(2, K)) :
    polynomialAction F (Matrix.SpecialLinearGroup.map e g) (X 0 ^ n) =
      (C (e (g 0 0)) * X 0 + C (e (g 1 0)) * X 1) ^ n := by
  simp [polynomialAction, Fin.sum_univ_two]

private theorem highestWeightSpan_le_weighted (e : K →+* F) (n : ℕ) :
    (highestWeightSpan e n).toSubmodule ≤
      Submodule.span F (Set.range (weightedMonomial (F := F) n)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g, rfl⟩
  dsimp only
  rw [action_X_pow, binomial_expansion]
  exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)

private def sampleMatrix (t : K) : SL(2, K) :=
  ⟨!![t, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

private theorem weighted_mem_highestWeightSpan (e : K →+* F) (n : ℕ)
    (x : Fin (n+1) → K) (hx : Function.Injective x) (r : Fin (n+1)) :
    weightedMonomial (F := F) n r ∈ highestWeightSpan e n := by
  apply (highestWeightSpan e n).toSubmodule.coeff_mem_of_sum_pow_smul_mem
    (weightedMonomial n) (fun a => e (x a)) (e.injective.comp hx) _ r
  intro a
  have h : polynomialAction F (Matrix.SpecialLinearGroup.map e (sampleMatrix (x a))) (X 0 ^ n) ∈
      highestWeightSpan e n := Submodule.subset_span ⟨sampleMatrix (x a), rfl⟩
  rw [action_X_pow, binomial_expansion] at h
  change _ ∈ (highestWeightSpan e n).toSubmodule at h
  simpa [sampleMatrix] using h

private theorem highestWeightSpan_eq_weighted (e : K →+* F) (n : ℕ)
    (x : Fin (n+1) → K) (hx : Function.Injective x) :
    (highestWeightSpan e n).toSubmodule =
      Submodule.span F (Set.range (weightedMonomial (F := F) n)) := by
  apply le_antisymm (highestWeightSpan_le_weighted e n)
  apply Submodule.span_le.mpr
  rintro _ ⟨r, rfl⟩
  exact weighted_mem_highestWeightSpan e n x hx r

private theorem weighted_span_eq_admissible (n : ℕ) :
    Submodule.span F (Set.range (weightedMonomial (F := F) n)) =
      Submodule.span F (Set.range fun r : {r : Fin (n+1) // (n.choose r : F) ≠ 0} =>
        weightedMonomial n r.val) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    by_cases hr : (n.choose r : F) = 0
    · simp [weightedMonomial, hr]
    · exact Submodule.subset_span ⟨⟨r, hr⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨r, rfl⟩
    exact Submodule.subset_span ⟨r.val, rfl⟩

private theorem monomials_independent (n : ℕ) :
    LinearIndependent F (fun r : Fin (n+1) =>
      (X 0 ^ (r : ℕ) * X 1 ^ (n-r) : MvPolynomial (Fin 2) F)) := by
  let d : Fin (n+1) → Fin 2 →₀ ℕ := fun r =>
    Finsupp.equivFunOnFinite.symm ![r.val, n-r.val]
  have hd : Function.Injective d := by
    intro r s hrs
    apply Fin.ext
    have h := congrArg (fun d : Fin 2 →₀ ℕ => d 0) hrs
    simpa [d] using h
  have h := (MvPolynomial.basisMonomials (Fin 2) F).linearIndependent.comp d hd
  have heq : (fun r : Fin (n+1) => (X 0 ^ (r : ℕ) * X 1 ^ (n-r) : MvPolynomial (Fin 2) F)) =
      (MvPolynomial.basisMonomials (Fin 2) F) ∘ d := by
    funext r
    simp [d, MvPolynomial.coe_basisMonomials, monomial_eq, Finsupp.prod_fintype,
      Fin.prod_univ_two]
  rw [heq]
  exact h

private theorem admissible_weighted_independent (n : ℕ) :
    LinearIndependent F (fun r : {r : Fin (n+1) // (n.choose r : F) ≠ 0} =>
      weightedMonomial (F := F) n r.val) := by
  have h := (monomials_independent (F := F) n).comp
    (fun r : {r : Fin (n+1) // (n.choose r : F) ≠ 0} => r.val) Subtype.val_injective
  have hu := h.units_smul (fun r => Units.mk0 (n.choose r.val : F) r.property)
  convert hu using 1
  funext r
  rfl


private theorem highestWeightSpan_eq_admissible [Finite K] (e : K →+* F) (n : ℕ)
    (hn : n < Nat.card K) :
    (highestWeightSpan e n).toSubmodule =
      Submodule.span F (Set.range fun r : {r : Fin (n+1) // (n.choose r : F) ≠ 0} =>
        weightedMonomial n r.val) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨x⟩ := Function.Embedding.nonempty_of_card_le (α := Fin (n+1)) (β := K)
    (by simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using Nat.succ_le_of_lt hn)
  exact (highestWeightSpan_eq_weighted e n x x.injective).trans
    (weighted_span_eq_admissible n)

private noncomputable def monomialBasis [Finite K] (e : K →+* F) (n : ℕ)
    (hn : n < Nat.card K) :
    Module.Basis {r : Fin (n+1) // (n.choose r : F) ≠ 0} F
      (highestWeightSpan e n).toSubmodule :=
  (Module.Basis.span (admissible_weighted_independent (F := F) n)).map
    (LinearEquiv.ofEq _ _ (highestWeightSpan_eq_admissible e n hn).symm)

private theorem monomialBasis_coe [Finite K] (e : K →+* F) (n : ℕ)
    (hn : n < Nat.card K) (r : {r : Fin (n+1) // (n.choose r : F) ≠ 0}) :
    (monomialBasis e n hn r : MvPolynomial (Fin 2) F) = weightedMonomial n r.val := by
  simp only [monomialBasis, Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply]

private theorem paired_basis_bound {I W : Type*} [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] [CharP F 2]
    (b : Module.Basis I F W) (A : Module.End F W) (τ : I → I)
    (s : I → Prop) [DecidablePred s]
    (hs : ∀ i, s (τ i) ↔ ¬ s i) (hA : ∀ i, A (b i) = b (τ i)) :
    Module.finrank F W ≤ 2 * operatorFixedCodim A := by
  let P : Module.End F W := b.constr F (fun i => if s i then b i else 0)
  have hP (i : I) : P (b i) = if s i then b i else 0 := b.constr_basis _ _ i
  have hAP : (A - 1) * P + P * (A - 1) = A := by
    apply b.ext
    intro i
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_sub, hP, hA]
    by_cases hi : s i
    · have ht : ¬ s (τ i) := by simpa only [hs, not_not] using hi
      simp only [if_pos hi, if_neg ht, hA, zero_sub]
      have htwo : b i + b i = 0 := by
        rw [← two_smul F, CharTwo.two_eq_zero, zero_smul]
      have hneg : -b i = b i := neg_eq_of_add_eq_zero_right htwo
      rw [hneg, sub_add_cancel]
    · have ht : s (τ i) := (hs i).mpr hi
      simp only [if_neg hi, if_pos ht, map_zero,
        sub_zero, zero_add]
  let C := LinearMap.ker (A - 1)
  let j : C →ₗ[F] LinearMap.range (A - 1) :=
    ((A - 1).rangeRestrict.comp P).comp C.subtype
  have hj (v : C) : (j v : W) = v := by
    have hh := LinearMap.congr_fun hAP (v : W)
    have hv : (A - 1) (v : W) = 0 := v.property
    have hfix : A (v : W) = v := sub_eq_zero.mp hv
    change (A - 1) (P (v : W)) = (v : W)
    simpa only [LinearMap.add_apply, Module.End.mul_apply, hv, map_zero, add_zero, hfix]
      using hh
  have hinj : Function.Injective j := by
    intro v w he
    apply Subtype.ext
    simpa only [hj] using congrArg Subtype.val he
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  have hr := operatorFixedCodim_add_finrank A
  change Module.finrank F (LinearMap.ker (A - 1)) ≤ operatorFixedCodim A at hd
  omega

private def weyl [CharP K 2] : SL(2,K) :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two, CharTwo.neg_eq]⟩

private theorem weyl_monomial [CharP K 2] [CharP F 2]
    (e : K →+* F) (n : ℕ) (r : Fin (n+1)) :
    polynomialAction F (Matrix.SpecialLinearGroup.map e (weyl (K := K)))
      (weightedMonomial (F := F) n r) =
      weightedMonomial n (⟨n-r.val, by omega⟩ : Fin (n+1)) := by
  have hr : r.val ≤ n := by omega
  have he : Matrix.SpecialLinearGroup.map e (weyl (K := K)) = weyl (K := F) := by
    ext i j
    change e (!![0, 1; 1, 0] i j) = !![0, 1; 1, 0] i j
    fin_cases i <;> fin_cases j <;> simp
  rw [he]
  simp [weightedMonomial, polynomialAction, weyl, Fin.sum_univ_two,
    Nat.choose_symm hr, Nat.sub_sub_self hr, mul_comm]

private theorem admissible_ne_middle [CharP F 2] (n : ℕ) (hn : 0 < n)
    (r : {r : Fin (n+1) // (n.choose r : F) ≠ 0}) :
    r.val.val ≠ n - r.val.val := by
  intro he
  have hr : 0 < r.val.val := by omega
  have hn' : n = 2 * r.val.val := by omega
  apply r.property
  apply (CharP.cast_eq_zero_iff F 2 _).mpr
  simpa only [Nat.centralBinom_eq_two_mul_choose, ← hn'] using
    Nat.two_dvd_centralBinom_of_one_le hr

private theorem highestWeight_weyl_bound [Finite K] [CharP K 2] [CharP F 2]
    (e : K →+* F) (n : ℕ) (hn : n < Nat.card K) (hpos : 0 < n) :
    Module.finrank F (highestWeightSpan e n).toSubmodule ≤
      2 * operatorFixedCodim ((highestWeightSpan e n).toRepresentation (weyl (K := K))) := by
  classical
  let I := {r : Fin (n+1) // (n.choose r : F) ≠ 0}
  let τ : I → I := fun r => ⟨⟨n-r.val.val, by omega⟩, by
    simpa only [Nat.choose_symm (by omega : r.val.val ≤ n)] using r.property⟩
  apply paired_basis_bound (monomialBasis e n hn) _ τ (fun r => r.val.val < n-r.val.val)
  · intro r
    have hne := admissible_ne_middle (F := F) n hpos r
    dsimp [τ]
    have hr := r.val.isLt
    omega
  · intro r
    apply Subtype.ext
    change polynomialAction F (Matrix.SpecialLinearGroup.map e weyl)
      (monomialBasis e n hn r) = (monomialBasis e n hn (τ r) : MvPolynomial (Fin 2) F)
    rw [monomialBasis_coe, monomialBasis_coe, weyl_monomial]

private theorem weyl_order [CharP K 2] : orderOf (weyl (K := K)) = 2 := by
  apply orderOf_eq_prime (p := 2)
  · rw [pow_two]
    apply Subtype.ext
    change (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) * !![0, 1; 1, 0] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · intro he
    have hh := congrArg (fun g : SL(2,K) => g.val 0 0) he
    exact zero_ne_one hh

/-- Every nonidentity involution exchanges the admissible monomials in pairs,
after actual SL₂ conjugacy with the Weyl matrix. -/
public theorem highestWeight_involution_bound [Finite K] [CharP K 2] [CharP F 2]
    (e : K →+* F) (n : ℕ) (hn : n < Nat.card K) (hpos : 0 < n)
    (g : SL(2,K)) (hg : g ≠ 1) (hg2 : g ^ 2 = 1) :
    Module.finrank F (highestWeightSpan e n).toSubmodule ≤
      2 * operatorFixedCodim ((highestWeightSpan e n).toRepresentation g) := by
  let q := Theory.PSL2.sl2QuotientEquiv K
  have hc := Theory.PSL2.involutions_isConj (q g) (q weyl)
    ((q.orderOf_eq g).trans (orderOf_eq_prime hg2 hg))
    ((q.orderOf_eq weyl).trans weyl_order)
  have hs : IsConj g (weyl (K := K)) := by
    simpa only [MulEquiv.coe_toMonoidHom, q.symm_apply_apply] using
      q.symm.toMonoidHom.map_isConj hc
  obtain ⟨d, hd⟩ := isConj_iff.mp hs
  let ρ := (highestWeightSpan e n).toRepresentation
  let D : (highestWeightSpan e n).toSubmodule ≃ₗ[F] (highestWeightSpan e n).toSubmodule :=
    { toLinearMap := ρ d
      invFun := ρ d⁻¹
      left_inv := ρ.inv_self_apply d
      right_inv := ρ.self_inv_apply d }
  have hdisp : operatorFixedCodim (ρ g) = operatorFixedCodim (ρ weyl) := by
    apply operatorFixedCodim_eq_of_equiv _ _ D
    intro v
    change ρ d (ρ g v) = ρ weyl (ρ d v)
    rw [← hd]
    simp only [map_mul, Module.End.mul_apply, Representation.inv_self_apply]
  rw [hdisp]
  exact highestWeight_weyl_bound e n hn hpos

end Representation.SL2.BinaryInvolutionDisplacement
