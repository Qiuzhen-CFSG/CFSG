module

public import Theory.Representation.SL2.HighestWeightDimension
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Paired half-period highest weights for binary SL₂

Let `K` have `2^r` elements, with `r ≥ 2` even, and let `K → F` be a field
embedding in characteristic two. Every positive weight `n < |K|` satisfying
`(|K|-1) ∣ n * (2^(r/2)-1)` has an actual representation equivalence to
`τ ⊗ (τ ∘ δ)`, where `δ` is the half-degree Frobenius and `dim τ ≥ 2`.
The maximal weight `|K|-1` is included.

Writing `Q = 2^(r/2)`, cancellation gives `n = a + Q*a` with `0 < a < Q`.
Take the weight-`a` polynomial orbit span for the first factor. The
coefficient-linear substitution `Xᵢ ↦ Xᵢ^Q` intertwines its Frobenius twist
with the polynomial action. Multiplication then maps the tensor product to
polynomials and its invariant image contains `X₀^n`. The digit-product
formula gives equal dimensions, proving that this multiplication map is a
bijection onto the weight-`n` span. A basis transports both factors to the
same coordinate space. The elementary digit recurrence follows the proof
in `Theory.Combinatorics.PeriodicDigitProduct`.

This supplies the paired-tensor premise of the Schur-linear outer-involution
argument for Aschbacher--Smith K.3.1, printed pp.453--454, and
Guralnick--Malle, Classification of 2F-modules II, §3.5 and Proposition 4.1(2),
manuscript pp.20,22. No degree bound or recognition hypothesis is used.
-/

open scoped MatrixGroups TensorProduct
open MvPolynomial
namespace Representation.SL2.HighestWeightPair
noncomputable section

private def digitProd (k n : ℕ) : ℕ := ∏ i : Fin k, (n / 2 ^ (i : ℕ) % 2 + 1)

private theorem digitProd_zero (n : ℕ) : digitProd 0 n = 1 := by simp [digitProd]

private theorem digitProd_succ (k n : ℕ) :
    digitProd (k + 1) n = (n % 2 + 1) * digitProd k (n / 2) := by
  rw [digitProd, Fin.prod_univ_succ]
  simp only [Fin.val_zero, pow_zero, Nat.div_one]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [Fin.val_succ, pow_succ, Nat.div_div_eq_div_mul, mul_comm]

private theorem digitProd_append (s k a b : ℕ) (ha : a < 2 ^ s) :
    digitProd (s + k) (a + 2 ^ s * b) = digitProd s a * digitProd k b := by
  induction s generalizing a with
  | zero =>
      have h : a = 0 := by simpa using ha
      simp only [h, pow_zero, zero_add, one_mul, digitProd_zero]
  | succ s ih =>
      have hdiv : a / 2 < 2 ^ s :=
        Nat.div_lt_of_lt_mul (by simpa only [pow_succ, mul_comm] using ha)
      rw [show s + 1 + k = (s + k) + 1 by omega, digitProd_succ,
        pow_succ', mul_assoc, Nat.add_mul_mod_self_left,
        Nat.add_mul_div_left _ _ (by decide : 0 < 2), ih (a / 2) hdiv, digitProd_succ]
      exact mul_assoc _ _ _ |>.symm

private theorem digitProd_ge_two (k n : ℕ) (hn : 0 < n) (hbound : n < 2 ^ k) :
    2 ≤ digitProd k n := by
  induction k generalizing n with
  | zero => simp at hbound; omega
  | succ k ih =>
      rw [digitProd_succ]
      by_cases hr : n % 2 = 0
      · have hdiv : 0 < n / 2 := by omega
        have hsmall : n / 2 < 2 ^ k :=
          Nat.div_lt_of_lt_mul (by simpa only [pow_succ, mul_comm] using hbound)
        simpa [hr] using ih (n / 2) hdiv hsmall
      · have h1 : 2 ≤ n % 2 + 1 := by omega
        have hp : 0 < digitProd k (n / 2) :=
          Finset.prod_pos (fun _ _ => Nat.zero_lt_succ _)
        exact h1.trans (Nat.le_mul_of_pos_right _ hp)

private theorem exists_half_block {r n : ℕ} (hr : 2 ≤ r) (heven : Even r)
    (hn : 0 < n) (hlt : n < 2 ^ r)
    (hp : 2 ^ r - 1 ∣ n * (2 ^ (r / 2) - 1)) :
    ∃ a, 0 < a ∧ a < 2 ^ (r / 2) ∧ n = a + 2 ^ (r / 2) * a := by
  have hhalf : r / 2 + r / 2 = r := by
    have := Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp heven)
    omega
  have hQ : 1 < 2 ^ (r / 2) := one_lt_pow₀ (by decide) (by omega)
  have hfactor : (1 + 2 ^ (r / 2)) * (2 ^ (r / 2) - 1) = 2 ^ r - 1 := by
    rw [show 2 ^ r = 2 ^ (r / 2) * 2 ^ (r / 2) by rw [← pow_add, hhalf]]
    have hsub := Nat.sub_add_cancel hQ.le
    have hsquare : 1 ≤ 2 ^ (r / 2) * 2 ^ (r / 2) := by nlinarith
    have hsubsquare := Nat.sub_add_cancel hsquare
    nlinarith
  have hd : (1 + 2 ^ (r / 2)) ∣ n := by
    apply Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < 2 ^ (r / 2) - 1)
    rwa [hfactor]
  obtain ⟨a, ha⟩ := hd
  have hapos : 0 < a := by nlinarith [ha]
  have halt : a < 2 ^ (r / 2) := by
    have hle : (1 + 2 ^ (r / 2)) * a ≤
        (1 + 2 ^ (r / 2)) * (2 ^ (r / 2) - 1) := by
      rw [← ha, hfactor]
      omega
    have := Nat.le_of_mul_le_mul_left hle (by omega : 0 < 1 + 2 ^ (r / 2))
    omega
  exact ⟨a, hapos, halt, by rw [ha]; ring⟩

variable {K F : Type*} [Field K] [Field F] [Finite K] [CharP K 2] [CharP F 2]

private abbrev polyRep (j : K →+* F) :
    Representation F SL(2,K) (MvPolynomial (Fin 2) F) :=
  (polynomialRepresentation F).comp (Matrix.SpecialLinearGroup.map j)

private abbrev delta (m : ℕ) : MulAut SL(2,K) :=
  Theory.PSL2.sl2FieldAut (iterateFrobeniusEquiv K 2 m)

private def powerSubstitution (m : ℕ) :
    MvPolynomial (Fin 2) F →ₐ[F] MvPolynomial (Fin 2) F :=
  aeval fun i => X i ^ (2 ^ m)

private theorem powerSubstitution_intertwines (j : K →+* F) (m : ℕ) (g : SL(2,K))
    (f : MvPolynomial (Fin 2) F) :
    powerSubstitution m (polynomialAction F (Matrix.SpecialLinearGroup.map j (delta m g)) f) =
      polynomialAction F (Matrix.SpecialLinearGroup.map j g) (powerSubstitution m f) := by
  have h : (powerSubstitution (F := F) m).comp
      (polynomialAction F (Matrix.SpecialLinearGroup.map j (delta m g))) =
      (polynomialAction F (Matrix.SpecialLinearGroup.map j g)).comp
        (powerSubstitution m) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [powerSubstitution, polynomialAction, Fin.sum_univ_two, delta,
      Theory.PSL2.sl2FieldAut, iterateFrobenius_def, add_pow_char_pow, mul_pow]
  exact DFunLike.congr_fun h f

private def firstMap (j : K →+* F) (a : ℕ) :
    (highestWeightSpan j a).toRepresentation.IntertwiningMap (polyRep j) where
  toLinearMap := (highestWeightSpan j a).toSubmodule.subtype
  isIntertwining' _ := rfl

private def secondMap (j : K →+* F) (m a : ℕ) :
    Representation.IntertwiningMap
      ((highestWeightSpan j a).toRepresentation.comp (delta m).toMonoidHom) (polyRep j) where
  toLinearMap := (powerSubstitution m).toLinearMap.comp (highestWeightSpan j a).toSubmodule.subtype
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact powerSubstitution_intertwines j m g v.val

private def polyMul (j : K →+* F) :
    ((polyRep j).tprod (polyRep j)).IntertwiningMap (polyRep j) where
  toLinearMap := LinearMap.mul' F (MvPolynomial (Fin 2) F)
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro u v
    exact (map_mul (polynomialAction F (Matrix.SpecialLinearGroup.map j g)) u v).symm

private abbrev pairRep (j : K →+* F) (m a : ℕ) :
    Representation F SL(2,K)
      ((highestWeightSpan j a).toSubmodule ⊗[F] (highestWeightSpan j a).toSubmodule) :=
  (highestWeightSpan j a).toRepresentation.tprod
    ((highestWeightSpan j a).toRepresentation.comp (delta m).toMonoidHom)

private def productMap (j : K →+* F) (m a : ℕ) :
    (pairRep j m a).IntertwiningMap (polyRep j) :=
  (polyMul j).comp ((firstMap j a).tensor (secondMap j m a))

private theorem productMap_tmul (j : K →+* F) (m a : ℕ)
    (u v : (highestWeightSpan j a).toSubmodule) :
    productMap j m a (u ⊗ₜ[F] v) = u.val * powerSubstitution m v.val := by
  change LinearMap.mul' F _
    (TensorProduct.map (highestWeightSpan j a).toSubmodule.subtype
      ((powerSubstitution m).toLinearMap.comp (highestWeightSpan j a).toSubmodule.subtype)
      (u ⊗ₜ[F] v)) = _
  rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
  rfl

private def productRange (j : K →+* F) (m a : ℕ) : Subrepresentation (polyRep j) where
  toSubmodule := (productMap j m a).toLinearMap.range
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, rfl⟩
    exact ⟨pairRep j m a g v,
      Representation.IntertwiningMap.isIntertwining _ _ (productMap j m a) g v⟩

private theorem highestWeight_le_range (j : K →+* F) (m a : ℕ) :
    highestWeightSpan j (a + 2 ^ m * a) ≤ productRange j m a := by
  apply (highestWeightSpan_le_iff j _ _).mpr
  let x : (highestWeightSpan j a).toSubmodule := ⟨X 0 ^ a, X_pow_mem_highestWeightSpan j a⟩
  refine ⟨x ⊗ₜ[F] x, ?_⟩
  change productMap j m a (x ⊗ₜ[F] x) = _
  rw [productMap_tmul]
  simp [x, powerSubstitution, pow_mul, pow_add]

omit [CharP K 2] in
private theorem pair_finrank (j : K →+* F) (m a : ℕ)
    (hc : Nat.card K = 2 ^ (m + m)) (ha : a < 2 ^ m)
    (hn : a + 2 ^ m * a < Nat.card K) :
    Module.finrank F (highestWeightSpan j (a + 2 ^ m * a)).toSubmodule =
      Module.finrank F (highestWeightSpan j a).toSubmodule ^ 2 := by
  have ham : a < 2 ^ (m + m) := by
    rw [pow_add]
    exact ha.trans_le (Nat.le_mul_of_pos_right _ (by positivity))
  rw [highestWeightSpan_finrank_eq_prod_digits j 2 (by decide) _ (m + m) hc (by rwa [← hc]),
    highestWeightSpan_finrank_eq_prod_digits j 2 (by decide) a (m + m) hc ham]
  change digitProd (m + m) (a + 2 ^ m * a) = digitProd (m + m) a ^ 2
  rw [digitProd_append m m a a ha]
  have hz : digitProd (m + m) a = digitProd m a := by
    simpa [digitProd] using digitProd_append m m a 0 ha
  rw [hz, pow_two]

omit [CharP K 2] in
private theorem factor_finrank_ge_two (j : K →+* F) (m a : ℕ)
    (hc : Nat.card K = 2 ^ (m + m)) (hpos : 0 < a) (ha : a < 2 ^ m) :
    2 ≤ Module.finrank F (highestWeightSpan j a).toSubmodule := by
  have ham : a < 2 ^ (m + m) := by
    rw [pow_add]
    exact ha.trans_le (Nat.le_mul_of_pos_right _ (by positivity))
  rw [highestWeightSpan_finrank_eq_prod_digits j 2 (by decide) a (m + m) hc ham]
  exact digitProd_ge_two (m + m) a hpos ham

private theorem productRange_eq (j : K →+* F) (m a : ℕ)
    (hc : Nat.card K = 2 ^ (m + m)) (ha : a < 2 ^ m)
    (hn : a + 2 ^ m * a < Nat.card K) :
    (highestWeightSpan j (a + 2 ^ m * a)).toSubmodule =
      (productMap j m a).toLinearMap.range := by
  apply Submodule.eq_of_le_of_finrank_le (S₂ := (productMap j m a).toLinearMap.range)
    (highestWeight_le_range j m a)
  rw [pair_finrank j m a hc ha hn, pow_two]
  simpa only [Module.finrank_tensorProduct] using (productMap j m a).toLinearMap.finrank_range_le

private def productToSpan (j : K →+* F) (m a : ℕ)
    (hc : Nat.card K = 2 ^ (m + m)) (ha : a < 2 ^ m)
    (hn : a + 2 ^ m * a < Nat.card K) :
    (pairRep j m a).IntertwiningMap (highestWeightSpan j (a + 2 ^ m * a)).toRepresentation where
  toLinearMap := (productMap j m a).toLinearMap.codRestrict _ (fun v => by
    rw [productRange_eq j m a hc ha hn]
    exact LinearMap.mem_range_self _ v)
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _ (productMap j m a) g v

private theorem productToSpan_surjective (j : K →+* F) (m a : ℕ)
    (hc : Nat.card K = 2 ^ (m + m)) (ha : a < 2 ^ m)
    (hn : a + 2 ^ m * a < Nat.card K) :
    Function.Surjective (productToSpan j m a hc ha hn) := by
  intro v
  have hv : (v : MvPolynomial (Fin 2) F) ∈ (productMap j m a).toLinearMap.range :=
    (productRange_eq j m a hc ha hn).le v.property
  obtain ⟨w, hw⟩ := hv
  exact ⟨w, Subtype.ext hw⟩

private def productSpanEquiv (j : K →+* F) (m a : ℕ)
    (hc : Nat.card K = 2 ^ (m + m)) (ha : a < 2 ^ m)
    (hn : a + 2 ^ m * a < Nat.card K) :
    (pairRep j m a).Equiv (highestWeightSpan j (a + 2 ^ m * a)).toRepresentation := by
  let f := (productToSpan j m a hc ha hn).toLinearMap
  have hd : Module.finrank F
      ((highestWeightSpan j a).toSubmodule ⊗[F] (highestWeightSpan j a).toSubmodule) =
      Module.finrank F (highestWeightSpan j (a + 2 ^ m * a)).toSubmodule := by
    rw [pair_finrank j m a hc ha hn, Module.finrank_tensorProduct, pow_two]
  have hs : Function.Surjective f := productToSpan_surjective j m a hc ha hn
  have hi : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := F)
      (V := (highestWeightSpan j a).toSubmodule ⊗[F] (highestWeightSpan j a).toSubmodule)
      (V₂ := (highestWeightSpan j (a + 2 ^ m * a)).toSubmodule) (f := f) hd).mpr hs
  exact (productToSpan j m a hc ha hn).ofBijective ⟨hi, hs⟩

private def tensorEquiv {H U V U' V' : Type*} [Monoid H]
    [AddCommGroup U] [Module F U] [AddCommGroup V] [Module F V]
    [AddCommGroup U'] [Module F U'] [AddCommGroup V'] [Module F V']
    {ρ : Representation F H U} {σ : Representation F H V}
    {ρ' : Representation F H U'} {σ' : Representation F H V'}
    (e : ρ.Equiv ρ') (f : σ.Equiv σ') : (ρ.tprod σ).Equiv (ρ'.tprod σ') := by
  refine Representation.Equiv.mk (TensorProduct.congr e.toLinearEquiv f.toLinearEquiv) ?_
  intro g
  apply TensorProduct.ext'
  intro v w
  exact congrArg₂ (fun v w => v ⊗ₜ[F] w) (congrArg (fun t => t v) (e.isIntertwining' g))
    (congrArg (fun t => t w) (f.isIntertwining' g))

/-- A half-period highest weight is a genuine tensor pair for the literal
half-degree field automorphism, with a factor of dimension at least two. -/
public theorem _root_.Representation.SL2.exists_highestWeight_pairedTensor
    (j : K →+* F) {r : ℕ} (hr : 2 ≤ r) (heven : Even r)
    (hc : Nat.card K = 2 ^ r) (n : ℕ) (hn : 0 < n) (hlt : n < Nat.card K)
    (hp : (Nat.card K - 1) ∣ n * (2 ^ (r / 2) - 1)) :
    ∃ d : ℕ, 2 ≤ d ∧ ∃ τ : Representation F SL(2,K) (Fin d → F),
      Nonempty ((highestWeightSpan j n).toRepresentation.Equiv
        (τ.tprod (τ.comp (Theory.PSL2.sl2FieldAut
          (iterateFrobeniusEquiv K 2 (r / 2))).toMonoidHom))) := by
  obtain ⟨a, hapos, ha, hna⟩ := exists_half_block hr heven hn (by rwa [← hc]) (by rwa [← hc])
  have hhalf : r / 2 + r / 2 = r := by
    have := Nat.mod_eq_zero_of_dvd (even_iff_two_dvd.mp heven)
    omega
  have hc' : Nat.card K = 2 ^ (r / 2 + r / 2) := by rwa [hhalf]
  subst n
  let ρ := (highestWeightSpan j a).toRepresentation
  let b := (Module.finBasis F (highestWeightSpan j a).toSubmodule).equivFun
  let τ : Representation F SL(2,K)
      (Fin (Module.finrank F (highestWeightSpan j a).toSubmodule) → F) :=
    b.conjRingEquiv.toMonoidHom.comp ρ
  let φ : ρ.Equiv τ := Representation.Equiv.mk b (by
    intro g
    apply LinearMap.ext
    intro v
    simp [τ, LinearEquiv.conjRingEquiv])
  let ψ : Representation.Equiv (ρ.comp (delta (K := K) (r / 2)).toMonoidHom)
      (τ.comp (delta (K := K) (r / 2)).toMonoidHom) :=
    Representation.Equiv.mk b (fun g => φ.isIntertwining' (delta (r / 2) g))
  exact ⟨_, factor_finrank_ge_two j (r / 2) a hc' hapos ha, τ,
    ⟨(productSpanEquiv j (r / 2) a hc' ha hlt).symm.trans (tensorEquiv φ ψ)⟩⟩

end
end Representation.SL2.HighestWeightPair
