module
public import Theory.SpecificGroups.LieType.F4RootSL2.Separation
public import Theory.AlgebraicGroup.RootSystems.SimpleGeckGroup.Commutation
public import Theory.SpecificGroups.LieType.F4RootCentralizer.Subsystem
public import Mathlib.GroupTheory.NoncommCoprod
public import Theory.GroupTheory.PrimeRankWitness

/-!
# A defining-prime plane in the F₄ fundamental centralizer

The literal positive α₂ and negative α₃ root curves commute with each other
and with both signed fundamental α₀ curves. Their product survives the
central quotient: commutation with positive α₁(1) detects the first parameter,
and then commutation with negative α₂(1) detects the second. Both decisive
matrix entries have coefficient one, including in characteristic three.

The product has exponent p in characteristic p, so it lies in the actual
O^{p′} centralizer. Restriction to the prime field embeds C_p² and yields the
defining-rank obstruction needed by A.2.17. No identification with Sp₆ or
centralizer exhaustion is used.

Source: Aschbacher–Smith A.2.17, printed p.39 of refs/quasithin.pdf;
GLS3 §§1.12 and 2.6 for the integral root-curve conventions.
-/

@[expose] public noncomputable section
namespace ExceptionalSplit.F4RootCentralizer.DefiningPair
open Matrix
open scoped MatrixGroups
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
open ReeF4.Cartan.FieldSeparation.TraceValues
local instance : InvolutiveNeg typeF4Roots := typeF4RootPairing.indexNeg
local instance basisDecidableEq : DecidableEq Basis := fun a b => instDecidableEqSum a b
set_option linter.unusedSimpArgs false
variable {F : Type*} [Field F]

private lemma positive_sum_entry (i j : typeF4RootPairing_base.support) (r : typeF4Roots)
    (hr : typeF4RootPairing.root r = typeF4RootPairing.root i + typeF4RootPairing.root j)
    (t : F) : positiveMatrix i t (Sum.inr r) (Sum.inr j.val) = t := by
  have h0 : r ≠ j.val := by
    intro h
    apply typeF4RootPairing.ne_zero i
    ext k
    have he := congrFun hr k
    simp only [h, Pi.add_apply, Pi.zero_apply] at he ⊢
    linarith
  have h2 : typeF4RootPairing.root r ≠ typeF4RootPairing.root j +
      2 • typeF4RootPairing.root i := by
    intro h
    apply typeF4RootPairing.ne_zero i
    ext k
    have he := congrFun h k
    have he' := congrFun hr k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at he he' ⊢
    norm_num only [typeF4RootPairing_root, nsmul_eq_mul, Nat.cast_ofNat] at he he' ⊢
    linarith
  have h3 : typeF4RootPairing.root r ≠ typeF4RootPairing.root j +
      3 • typeF4RootPairing.root i := by
    intro h
    apply typeF4RootPairing.ne_zero i
    ext k
    have he := congrFun h k
    have he' := congrFun hr k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at he he' ⊢
    norm_num only [typeF4RootPairing_root, nsmul_eq_mul, Nat.cast_ofNat] at he he' ⊢
    linarith
  simp only [positiveMatrix_formula, Matrix.add_apply, Matrix.smul_apply,
    Matrix.map_apply, Int.coe_castRingHom, smul_eq_mul]
  simp only [eDividedPower, eMatrix, Matrix.fromBlocks_apply₂₂, Matrix.of_apply,
    Matrix.one_apply, Sum.inr.injEq, if_neg h0, if_pos hr, if_neg h2, if_neg h3,
    RootPairing.Base.chainBotCoeff_eq_zero]
  norm_num

private lemma first_root_sum : typeF4RootPairing.root (root 5) =
    typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) +
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 1) := by
  ext k
  fin_cases k <;> norm_num [root, realCoord, coord, typeF4SimpleRootIndex,
    typeF4SimpleRoot, basisVector, Pi.single_apply, Fin.ext_iff]

private lemma first_entry (t : F) :
    positiveMatrix (typeF4RootPairing_baseEquiv 2) t
      (Sum.inr (root 5)) (Sum.inr (typeF4RootPairing_baseEquiv 1).val) = t :=
  positive_sum_entry _ _ _ first_root_sum t



private lemma second_root_sum : typeF4RootPairing.root (root 41) =
    typeF4RootPairing.root (typeF4RootPairing_baseEquiv 3) +
      typeF4RootPairing.root (typeF4RootPairing_baseEquiv 2) := by
  ext k
  fin_cases k <;> norm_num [root, realCoord, coord, typeF4SimpleRootIndex,
    typeF4SimpleRoot, basisVector, Pi.single_apply, Fin.ext_iff]

private lemma negative_cartan (i j : typeF4RootPairing_base.support) (t : F) :
    negativeMatrix i t *ᵥ Pi.single (Sum.inl j) 1 =
      Pi.single (Sum.inl j) 1 +
        (t * ((|typeF4RootPairing_base.cartanMatrix i j| : ℤ) : F)) •
          Pi.single (Sum.inr (-i : typeF4Roots)) 1 := by
  rw [negativeMatrix_formula, fDividedPower_one]
  ext (a | a) <;>
    simp [fMatrix, fDividedPower, Matrix.mul_apply, omegaMatrix,
      eDividedPower, Matrix.one_apply, Pi.single_apply, smul_eq_mul,
      -typeF4RootPairing_root, -RootPairing.indexNeg_neg]

private lemma negative_entry (i : typeF4RootPairing_base.support)
    (r j : typeF4Roots) (t : F) :
    negativeMatrix i t (Sum.inr (-r)) (Sum.inr (-j)) =
      positiveMatrix i t (Sum.inr r) (Sum.inr j) := by
  simp [negativeMatrix_formula, positiveMatrix_formula, fDividedPower,
    Matrix.mul_apply, omegaMatrix, Matrix.one_apply,
    -typeF4RootPairing_root, -RootPairing.indexNeg_neg]

private lemma fixes_of_commute (A B : (Matrix Basis Basis F)ˣ) (c v : Basis → F)
    (hc : Commute A B) (ha : A.val *ᵥ c = c) (hb : B.val *ᵥ c = c + v) :
    A.val *ᵥ v = v := by
  have he := congrArg (fun X : (Matrix Basis Basis F)ˣ => X.val *ᵥ c) hc.eq
  change (A.val * B.val) *ᵥ c = (B.val * A.val) *ᵥ c at he
  rw [← mulVec_mulVec, ← mulVec_mulVec, hb, ha, mulVec_add, ha, hb] at he
  exact add_left_cancel he

private lemma first_parameter_zero (t : F)
    (h : Commute (positiveUnit (typeF4RootPairing_baseEquiv 2) t)
      (positiveUnit (typeF4RootPairing_baseEquiv 1) (1 : F))) : t = 0 := by
  let c : Basis → F := Pi.single (Sum.inl (typeF4RootPairing_baseEquiv 0)) 1
  let v : Basis → F := Pi.single (Sum.inr (typeF4RootPairing_baseEquiv 1).val) 1
  have hc : (positiveUnit (typeF4RootPairing_baseEquiv 2) t).val *ᵥ c = c := by
    rw [positiveUnit_val, F4RootSL2.positive_cartan, typeF4RootPairing_base_cartan_apply]
    norm_num [typeF4CartanMatrix, Fin.ext_iff, c]
  have hv : (positiveUnit (typeF4RootPairing_baseEquiv 1) (1 : F)).val *ᵥ c = c + v := by
    rw [positiveUnit_val, F4RootSL2.positive_cartan, typeF4RootPairing_base_cartan_apply]
    norm_num [typeF4CartanMatrix, Fin.ext_iff, c]
    rfl
  have he := congrFun (fixes_of_commute _ _ c v h hc hv) (Sum.inr (root 5))
  have hr : root 5 ≠ (typeF4RootPairing_baseEquiv 1).val := by
    intro h
    apply typeF4RootPairing.ne_zero (typeF4RootPairing_baseEquiv 2)
    ext k
    have he := congrFun first_root_sum k
    simp only [h, Pi.add_apply, Pi.zero_apply] at he ⊢
    linarith
  dsimp only [v] at he
  rw [positiveUnit_val, Matrix.mulVec_single_one, Matrix.col_apply, first_entry] at he
  simpa only [Pi.single_apply, Sum.inr.injEq, if_neg hr] using he

private lemma second_parameter_zero (t : F)
    (h : Commute (negativeUnit (typeF4RootPairing_baseEquiv 3) t)
      (negativeUnit (typeF4RootPairing_baseEquiv 2) (1 : F))) : t = 0 := by
  let c : Basis → F := Pi.single (Sum.inl (typeF4RootPairing_baseEquiv 1)) 1
  let v : Basis → F := Pi.single (Sum.inr (-(typeF4RootPairing_baseEquiv 2) : typeF4Roots)) 1
  have hc : (negativeUnit (typeF4RootPairing_baseEquiv 3) t).val *ᵥ c = c := by
    rw [negativeUnit_val, negative_cartan, typeF4RootPairing_base_cartan_apply]
    norm_num [typeF4CartanMatrix, Fin.ext_iff, c]
  have hv : (negativeUnit (typeF4RootPairing_baseEquiv 2) (1 : F)).val *ᵥ c = c + v := by
    rw [negativeUnit_val, negative_cartan, typeF4RootPairing_base_cartan_apply]
    norm_num [typeF4CartanMatrix, Fin.ext_iff, c]
    rfl
  have he := congrFun (fixes_of_commute _ _ c v h hc hv) (Sum.inr (-(root 41)))
  have hr : root 41 ≠ (typeF4RootPairing_baseEquiv 2).val := by
    intro h
    apply typeF4RootPairing.ne_zero (typeF4RootPairing_baseEquiv 3)
    ext k
    have he := congrFun second_root_sum k
    simp only [h, Pi.add_apply, Pi.zero_apply] at he ⊢
    linarith
  dsimp only [v] at he
  rw [negativeUnit_val, Matrix.mulVec_single_one, Matrix.col_apply, negative_entry,
    positive_sum_entry _ _ _ second_root_sum] at he
  simpa only [Pi.single_apply, Sum.inr.injEq, neg_inj, if_neg hr] using he

open F4RootSL2
/-- The actual positive simple-root curve in the elementary F₄ matrix group. -/
abbrev positiveCurve (i : Fin 4) (t : F) : Elementary F :=
  elementaryRoot typeF4RootPairing typeF4RootPairing_base F (typeF4RootPairing_baseEquiv i) t
/-- The actual negative simple-root curve in the same elementary group. -/
abbrev negativeCurve (i : Fin 4) (t : F) : Elementary F :=
  elementaryRoot typeF4RootPairing typeF4RootPairing_base F (-(typeF4RootPairing_baseEquiv i) : typeF4Roots) t
private lemma positiveCurve_val (i : Fin 4) (t : F) : (positiveCurve i t).val =
    positiveUnit (typeF4RootPairing_baseEquiv i) t := rootCurveUnit_simple _ _
private lemma negativeCurve_val (i : Fin 4) (t : F) : (negativeCurve i t).val =
    negativeUnit (typeF4RootPairing_baseEquiv i) t := rootCurveUnit_neg_simple _ _

/-- Distinct signed simple roots commute in the literal elementary group. -/
lemma positive_negative_commute (i j : Fin 4) (hij : i ≠ j) (t u : F) :
    Commute (positiveCurve i t) (negativeCurve j u) := by
  show positiveCurve i t * negativeCurve j u = negativeCurve j u * positiveCurve i t
  apply Subtype.ext
  simp only [Subgroup.coe_mul, positiveCurve_val, negativeCurve_val]
  exact congrArg Subtype.val (commute_positive_negative (typeF4RootPairing_baseEquiv i)
    (typeF4RootPairing_baseEquiv j) (fun h => hij (typeF4RootPairing_baseEquiv.injective h)) t u).eq

/-- The selected commuting root curves, before the defining central quotient. -/
def elementaryPair : Multiplicative F × Multiplicative F →* Elementary F :=
  MonoidHom.noncommCoprod
    { toFun := fun t => positiveCurve 2 t.toAdd
      map_one' := elementaryRoot_zero _ _ _ _
      map_mul' := fun t u => elementaryRoot_add _ _ _ _ t.toAdd u.toAdd }
    { toFun := fun t => negativeCurve 3 t.toAdd
      map_one' := elementaryRoot_zero _ _ _ _
      map_mul' := fun t u => elementaryRoot_add _ _ _ _ t.toAdd u.toAdd }
    (fun t u => positive_negative_commute 2 3 (by decide) t.toAdd u.toAdd)

/-- No nonidentity element of the two-root plane is killed by the actual central quotient. -/
theorem elementaryPair_mem_center_iff (a : Multiplicative F × Multiplicative F) :
    elementaryPair a ∈ Subgroup.center (Elementary F) ↔ a = 1 := by
  constructor
  · intro h
    have hC : Commute (positiveCurve 2 a.1.toAdd * negativeCurve 3 a.2.toAdd) (positiveCurve 1 (1 : F)) :=
      (Subgroup.mem_center_iff.mp h _).symm
    have hB := (positive_negative_commute 1 3 (by decide) (1 : F) a.2.toAdd).symm
    have hA : Commute (positiveCurve 2 a.1.toAdd) (positiveCurve 1 (1 : F)) := by
      simpa only [mul_inv_cancel_right] using hC.mul_left hB.inv_left
    have ht : a.1.toAdd = 0 := first_parameter_zero _ (by
      have he := hA.map (Elementary F).subtype
      simpa only [Subgroup.coe_subtype, positiveCurve_val] using he)
    have hC' : Commute (negativeCurve 3 a.2.toAdd) (negativeCurve 2 (1 : F)) := by
      have he := (Subgroup.mem_center_iff.mp h (negativeCurve 2 (1 : F))).symm
      simpa [elementaryPair, ht, positiveCurve, commute_iff_eq] using he
    have hu : a.2.toAdd = 0 := second_parameter_zero _ (by
      have he := hC'.map (Elementary F).subtype
      simpa only [Subgroup.coe_subtype, negativeCurve_val] using he)
    exact Prod.ext (congrArg Multiplicative.ofAdd ht) (congrArg Multiplicative.ofAdd hu)
  · rintro rfl
    simp

/-- The literal two-root map into the actual central quotient defining F₄. -/
def projectedPair : Multiplicative F × Multiplicative F →* F4 F :=
  (projection typeF4RootPairing typeF4RootPairing_base F).comp elementaryPair

/-- Faithfulness survives the original adjoint central quotient, in every characteristic. -/
theorem projectedPair_injective : Function.Injective (projectedPair (F := F)) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro a ha
  apply (elementaryPair_mem_center_iff a).mp
  exact (projection_eq_one_iff _ _ F _).mp ha


private lemma positive_positive_commute (i j : Fin 4) (hij : i ≠ j)
    (hc : typeF4CartanMatrix j i = 0) (t u : F) : Commute (positiveCurve i t) (positiveCurve j u) := by
  show positiveCurve i t * positiveCurve j u = positiveCurve j u * positiveCurve i t
  apply Subtype.ext
  simp only [Subgroup.coe_mul, positiveCurve_val]
  exact congrArg Subtype.val (commute_positive_positive_of_cartan_eq_zero
    (typeF4RootPairing_baseEquiv i) (typeF4RootPairing_baseEquiv j)
    (fun h => hij (typeF4RootPairing_baseEquiv.injective h))
    (by simpa only [typeF4RootPairing_base_cartan_apply] using hc) t u).eq

private lemma negative_negative_commute (i j : Fin 4) (hij : i ≠ j)
    (hc : typeF4CartanMatrix j i = 0) (t u : F) : Commute (negativeCurve i t) (negativeCurve j u) := by
  show negativeCurve i t * negativeCurve j u = negativeCurve j u * negativeCurve i t
  apply Subtype.ext
  simp only [Subgroup.coe_mul, negativeCurve_val]
  exact congrArg Subtype.val (commute_negative_negative_of_cartan_eq_zero
    (typeF4RootPairing_baseEquiv i) (typeF4RootPairing_baseEquiv j)
    (fun h => hij (typeF4RootPairing_baseEquiv.injective h))
    (by simpa only [typeF4RootPairing_base_cartan_apply] using hc) t u).eq

private lemma pair_commute_elementaryHom (a : Multiplicative F × Multiplicative F)
    (A : SL(2,F)) : Commute (elementaryPair a) (elementaryHom A) := by
  apply Matrix.SL2.transvection_induction
    (fun A => Commute (elementaryPair a) (elementaryHom A)) ?_ ?_ A
  · intro i j hij t
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change Commute (elementaryPair a) (elementaryHom (upper t))
      rw [elementaryHom_upper]
      exact (positive_positive_commute 2 0 (by decide)
        (by norm_num [typeF4CartanMatrix, Fin.ext_iff]) _ t).mul_left
        (positive_negative_commute 0 3 (by decide) t _).symm
    · change Commute (elementaryPair a) (elementaryHom (lower t))
      rw [elementaryHom_lower]
      exact (positive_negative_commute 2 0 (by decide) _ t).mul_left
        (negative_negative_commute 3 0 (by decide)
          (by norm_num [typeF4CartanMatrix, Fin.ext_iff]) _ t)
    · exact (hij rfl).elim
  · intro A B hA hB
    rw [map_mul]
    exact hA.mul_right hB

/-- The selected plane centralizes the original long-root SL₂ pointwise. -/
theorem projectedPair_mem_centralizer (a : Multiplicative F × Multiplicative F) :
    projectedPair a ∈ Centralizer F := by
  rw [centralizer_eq_range_centralizer]
  apply Subgroup.mem_centralizer_iff.mpr
  rintro _ ⟨A, rfl⟩
  exact ((pair_commute_elementaryHom a A).map
    (projection typeF4RootPairing typeF4RootPairing_base F)).symm.eq

/-- The same literal product, restricted to the marked centralizer. -/
def centralizerPair : Multiplicative F × Multiplicative F →* Centralizer F :=
  projectedPair.codRestrict _ projectedPair_mem_centralizer

private lemma pair_pow (p : ℕ) [CharP F p] (a : Multiplicative F × Multiplicative F) :
    a ^ p = 1 := by
  apply Prod.ext <;>
    apply Multiplicative.toAdd.injective <;>
    simp only [Prod.pow_fst, Prod.pow_snd, Prod.fst_one, Prod.snd_one,
      toAdd_pow, toAdd_one,
      nsmul_eq_mul, CharP.cast_eq_zero F p, zero_mul]

/-- Each pair element lies in O^{p′} by its actual p-power relation. -/
theorem centralizerPair_mem_residual (p : ℕ) [CharP F p]
    (a : Multiplicative F × Multiplicative F) :
    centralizerPair a ∈ Subgroup.primeToResidual p (Centralizer F) := by
  apply Subgroup.mem_primeToResidual_of_pow (n := 1)
  simp only [pow_one, ← map_pow, pair_pow p a, map_one]

/-- The two-root plane in the literal O^{p′} centralizer. -/
def residualPair (p : ℕ) [CharP F p] :
    Multiplicative F × Multiplicative F →* Residual p F :=
  centralizerPair.codRestrict _ (centralizerPair_mem_residual p)

/-- Restricting the faithful central quotient map adds no new kernel. -/
theorem residualPair_injective (p : ℕ) [CharP F p] :
    Function.Injective (residualPair (F := F) p) := by
  intro a b h
  exact projectedPair_injective (congrArg (fun z : Residual p F => (z.val : F4 F)) h)

/-- The actual prime-field plane, with all field and quotient maps retained. -/
def primeFieldPair (p : ℕ) [Fact p.Prime] [CharP F p] :
    Multiplicative (ZMod p) × Multiplicative (ZMod p) →* Residual p F :=
  let c : Multiplicative (ZMod p) →* Multiplicative F :=
    (ZMod.castHom (dvd_refl p) F).toAddMonoidHom.toMultiplicative
  (residualPair p).comp (c.prodMap c)

/-- The prime-field parameters remain independent in the actual residual. -/
theorem primeFieldPair_injective (p : ℕ) [Fact p.Prime] [CharP F p] :
    Function.Injective (primeFieldPair (F := F) p) := by
  intro a b h
  have he := residualPair_injective (F := F) p h
  apply Prod.ext
  · apply Multiplicative.toAdd.injective
    exact (ZMod.castHom (dvd_refl p) F).injective (congrArg (fun z => z.1.toAdd) he)
  · apply Multiplicative.toAdd.injective
    exact (ZMod.castHom (dvd_refl p) F).injective (congrArg (fun z => z.2.toAdd) he)

/-- Defining rank at least two in the marked F₄ complementary residual,
including characteristic three. No symplectic realization or exhaustion is used. -/
theorem two_le_primeRank_residual (p : ℕ) [Fact p.Prime] [CharP F p] [Finite F] :
    2 ≤ primeRank p (Residual p F) := by
  have hp : ∀ a : Multiplicative (ZMod p) × Multiplicative (ZMod p), a ^ p = 1 :=
    pair_pow p
  have hc : Nat.card (Multiplicative (ZMod p) × Multiplicative (ZMod p)) = p ^ 2 := by
    simp [Nat.card_prod, Nat.card_eq_fintype_card, pow_two]
  exact primeRank_ge_of_elementary_embedding hp hc (primeFieldPair p) (primeFieldPair_injective p)

end ExceptionalSplit.F4RootCentralizer.DefiningPair
