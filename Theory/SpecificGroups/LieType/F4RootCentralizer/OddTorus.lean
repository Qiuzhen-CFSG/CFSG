module

public import Theory.SpecificGroups.LieType.F4RootCentralizer.DefiningPair
public import Theory.AlgebraicGroup.Borel.IntegralChevalleyTorusConjugation
public import Theory.AlgebraicGroup.RootSystems.IntegralChevalleyBrackets

/-!
# Odd-field torus actions on the fundamental F₄ root plane

The square of the literal rank-one Tits word is the minus-one coroot
matrix. Its action on the integral Cartan and root bases proves this
identity over every field, including characteristic three. The last two
coroots give partial and total inversion of the positive α₂ / negative α₃
plane already constructed in `DefiningPair`.

The prime-field plane retains its original quotient map, has order p² and
exponent p, and centralizes the original fundamental SL₂ involution. These
are the concrete inputs to the odd-central-cover exclusion in A.2.17.

Source: Aschbacher–Smith, A.2.17, printed p.39; the proof uses the integral
rank-one Tits identities instead of a full Sp₆ centralizer identification.
-/

@[expose] public noncomputable section
namespace ExceptionalSplit.F4RootCentralizer.OddTorus
open Matrix
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
local instance : InvolutiveNeg typeF4Roots := typeF4RootPairing.indexNeg
attribute [local instance] Classical.decEq
local instance : Fintype typeF4Roots := Fintype.ofFinite _
private abbrev Basis := typeF4RootPairing_base.support ⊕ typeF4Roots
local instance : DecidableEq (typeF4RootPairing_base.support ⊕ typeF4Roots) :=
  fun a b => instDecidableEqSum a b
set_option linter.unusedSimpArgs false
variable {F : Type*} [Field F]

private lemma tits_square_cartan (i j : typeF4RootPairing_base.support) :
    (titsLift i * titsLift i) *ᵥ u j = u j := by
  rw [← Matrix.mulVec_mulVec, titsLift_mulVec_u, Matrix.mulVec_sub,
    Matrix.mulVec_smul, titsLift_mulVec_u, titsLift_mulVec_u]
  have hii : |typeF4RootPairing_base.cartanMatrix i i| = 2 := by simp
  rw [hii]
  module

private lemma tits_square_root (i : typeF4RootPairing_base.support) (j : typeF4Roots) :
    (titsLift i * titsLift i) *ᵥ v (b := typeF4RootPairing_base) j =
      (-1 : ℤ) ^ (typeF4RootPairing.chainBotCoeff i j +
        typeF4RootPairing.chainBotCoeff i (typeF4RootPairing.reflectionPerm i j)) •
      v (b := typeF4RootPairing_base) j := by
  rw [← Matrix.mulVec_mulVec, titsLift_mulVec_v, Matrix.mulVec_smul,
    titsLift_mulVec_v, typeF4RootPairing.reflectionPerm_self, smul_smul, ← pow_add]

private lemma chain_sign (i : typeF4RootPairing_base.support) (j : typeF4Roots) :
    (-1 : F) ^ (typeF4RootPairing.chainBotCoeff i j +
      typeF4RootPairing.chainBotCoeff i (typeF4RootPairing.reflectionPerm i j)) =
      (((-1 : Fˣ) ^ (-typeF4RootPairing.pairingIn ℤ j i) : Fˣ) : F) := by
  have hdep : ¬ LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root i] := by
    rw [LinearIndependent.pair_iff]
    intro h
    exact one_ne_zero (h 1 (-1) (by simp)).1
  have htop : typeF4RootPairing.chainTopCoeff i i = 0 :=
    typeF4RootPairing.chainTopCoeff_of_not_linearIndependent hdep
  have hbot : typeF4RootPairing.chainBotCoeff i i = 0 :=
    typeF4RootPairing.chainBotCoeff_of_not_linearIndependent hdep
  by_cases hsame : j = i.val
  · subst j
    simp [htop, hbot]
  by_cases hneg : j = (-i : typeF4Roots)
  · subst j
    simp [htop, hbot, RootPairing.indexNeg_neg]
  have hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j] := by
    apply RootPairing.IsReduced.linearIndependent typeF4RootPairing (Ne.symm hsame)
    intro h
    apply hneg
    apply typeF4RootPairing.root.injective
    simpa only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self] using (neg_eq_iff_eq_neg.mpr h).symm
  have hlinNeg : LinearIndependent ℝ
      ![typeF4RootPairing.root (-i : typeF4Roots), typeF4RootPairing.root j] := by
    rw [LinearIndependent.pair_iff] at hlin ⊢
    intro a b hab
    have hab' : (-a) • typeF4RootPairing.root i + b • typeF4RootPairing.root j = 0 := by
      simpa only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
        RootPairing.reflection_apply_self, smul_neg, neg_smul] using hab
    obtain ⟨ha, hb⟩ := hlin (-a) b hab'
    exact ⟨neg_eq_zero.mp ha, hb⟩
  have hc : typeF4RootPairing.chainBotCoeff i (typeF4RootPairing.reflectionPerm i j) =
      typeF4RootPairing.chainTopCoeff i j := by
    have h := chainBotCoeff_reflectionWord (P := typeF4RootPairing)
      (b := typeF4RootPairing_base) [i] (-i : typeF4Roots) j hlinNeg
    simpa only [reflectionWord, RootPairing.indexNeg_neg,
      typeF4RootPairing.reflectionPerm_self,
      typeF4RootPairing.chainBotCoeff_reflectionPerm_left] using h
  rw [hc]
  have hchain := typeF4RootPairing.chainTopCoeff_sub_chainBotCoeff hlin
  have hp : (-1 : Fˣ) ^ ((typeF4RootPairing.chainBotCoeff i j +
      typeF4RootPairing.chainTopCoeff i j : ℕ) : ℤ) =
      (-1 : Fˣ) ^ (-typeF4RootPairing.pairingIn ℤ j i) := by
    calc
      _ = (-1 : Fˣ) ^ (2 * (typeF4RootPairing.chainBotCoeff i j : ℤ) +
          (-typeF4RootPairing.pairingIn ℤ j i)) := by
            congr 1
            push_cast
            omega
      _ = _ := by rw [_root_.zpow_add, _root_.zpow_mul]; norm_num
  rw [zpow_natCast] at hp
  simpa only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one] using congrArg Units.val hp

private def signDiagonal (i : typeF4RootPairing_base.support) : Matrix Basis Basis ℤ :=
  Matrix.diagonal fun a => match a with
    | .inl _ => 1
    | .inr j => (-1 : ℤ) ^ (typeF4RootPairing.chainBotCoeff i j +
        typeF4RootPairing.chainBotCoeff i (typeF4RootPairing.reflectionPerm i j))

private lemma tits_square_diagonal (i : typeF4RootPairing_base.support) :
    titsLift i * titsLift i = signDiagonal i := by
  apply Matrix.ext_of_mulVec_single
  rintro (j | j)
  · change (titsLift i * titsLift i) *ᵥ u j = _
    rw [tits_square_cartan]
    simp [signDiagonal, u, Matrix.diagonal_mulVec_single]
  · change (titsLift i * titsLift i) *ᵥ v (b := typeF4RootPairing_base) j = _
    rw [tits_square_root]
    ext k
    by_cases hk : k = Sum.inr j
    · subst k
      simp [signDiagonal, v, Matrix.diagonal_mulVec_single]
    · simp [signDiagonal, v, Matrix.diagonal_mulVec_single, Pi.single_apply, hk, Ne.symm hk]

/-- The square of the actual simple Tits word is its minus-one coroot diagonal. -/
theorem tits_square_eq_coroot (i : typeF4RootPairing_base.support) :
    rootCurveTitsWord (P := typeF4RootPairing) (S := F) [i,i] =
      integralChevalleyTorusElement (P := typeF4RootPairing)
        (integralChevalleySimpleCorootParameter i (-1 : Fˣ)) := by
  apply Units.ext
  change specializeMatrix (titsWord [i,i]) = Matrix.diagonal _
  simp only [titsWord, mul_one, tits_square_diagonal]
  ext row col
  by_cases h : row = col
  · subst col
    cases row with
    | inl j =>
        simp [specializeMatrix, signDiagonal, integralChevalleyTorusElement,
          chevalleyBasisTorusUnit, chevalleyBasisWeight]
    | inr j =>
        simp only [specializeMatrix, signDiagonal, Matrix.map_apply, Matrix.diagonal_apply,
          if_true, Int.coe_castRingHom, Int.cast_pow, Int.cast_neg, Int.cast_one]
        rw [chain_sign]
        simp [chevalleyBasisTorusUnit_root]
  · simp [specializeMatrix, signDiagonal, Matrix.diagonal_apply, h]


open F4RootSL2 DefiningPair
open scoped MatrixGroups

/-- The square of the actual three-factor Tits word in the elementary carrier. -/
def elementaryCoroot (i : Fin 4) : Elementary F :=
  (positiveCurve i (1 : F) * negativeCurve i (-1) * positiveCurve i 1) ^ 2

private lemma elementaryCoroot_val (i : Fin 4) :
    (elementaryCoroot (F := F) i).val = integralChevalleyTorusElement (P := typeF4RootPairing)
      (integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) (-1 : Fˣ)) := by
  have hw := tits_square_eq_coroot (F := F) (typeF4RootPairing_baseEquiv i)
  rw [rootCurveTitsWord_cons, rootCurveTitsWord_cons, rootCurveTitsWord_nil] at hw
  change (rootCurveUnit _ _ _ * rootCurveUnit _ _ _ * rootCurveUnit _ _ _) ^ 2 = _
  simp only [rootCurveUnit_simple, rootCurveUnit_neg_simple]
  simpa only [pow_two, mul_one, mul_assoc] using hw

/-- The original minus-one coroot, through the defining central quotient of F₄. -/
def coroot (i : Fin 4) : F4 F :=
  projection typeF4RootPairing typeF4RootPairing_base F (elementaryCoroot i)

private lemma elementaryCoroot_square (i : Fin 4) : elementaryCoroot (F := F) i ^ 2 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, elementaryCoroot_val, pow_two,
    ← integralChevalleyTorusElement_mul]
  have hparam :
      integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) (-1 : Fˣ) *
        integralChevalleySimpleCorootParameter (typeF4RootPairing_baseEquiv i) (-1 : Fˣ) = 1 := by
    ext j
    by_cases hj : j = typeF4RootPairing_baseEquiv i <;>
      simp [integralChevalleySimpleCorootParameter, hj]
  rw [hparam,integralChevalleyTorusElement_one]
  rfl

/-- Each constructed coroot has square one over the original field. -/
theorem coroot_square (i : Fin 4) : coroot (F := F) i ^ 2 = 1 := by
  rw [coroot, ← map_pow, elementaryCoroot_square, map_one]

/-- The actual coroot words commute, by their proved diagonal identity. -/
theorem coroot_commute (i j : Fin 4) : Commute (coroot (F := F) i) (coroot j) := by
  have hc : Commute (elementaryCoroot (F := F) i) (elementaryCoroot j) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, elementaryCoroot_val]
    rw [← integralChevalleyTorusElement_mul, ← integralChevalleyTorusElement_mul, mul_comm]
  exact hc.map (projection typeF4RootPairing typeF4RootPairing_base F)

private lemma coroot_conjugate_root (i : Fin 4) (r : typeF4Roots) (t : F) :
    coroot i * rootElement typeF4RootPairing typeF4RootPairing_base F r t * (coroot i)⁻¹ =
      rootElement typeF4RootPairing typeF4RootPairing_base F r
        ((((-1 : Fˣ) ^ typeF4RootPairing.pairingIn ℤ r (typeF4RootPairing_baseEquiv i) : Fˣ) : F) * t) := by
  have he : (elementaryCoroot (F := F) i)⁻¹ *
      elementaryRoot typeF4RootPairing typeF4RootPairing_base F r t * elementaryCoroot i =
      elementaryRoot typeF4RootPairing typeF4RootPairing_base F r
        ((((-1 : Fˣ) ^ typeF4RootPairing.pairingIn ℤ r (typeF4RootPairing_baseEquiv i) : Fˣ) : F) * t) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, elementaryCoroot_val]
    exact integralChevalleyRootCurve_simpleCoroot_conjugation
      (typeF4RootPairing_baseEquiv i) (-1 : Fˣ) r t
  have hci : (elementaryCoroot (F := F) i)⁻¹ = elementaryCoroot i :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using elementaryCoroot_square (F := F) i)
  rw [hci] at he
  have h := congrArg (projection typeF4RootPairing typeF4RootPairing_base F) he
  have hci' : (coroot (F := F) i)⁻¹ = coroot i :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using coroot_square (F := F) i)
  rw [hci']
  simpa only [map_mul, coroot, rootElement] using h

private lemma simple_pairing (i j : Fin 4) :
    typeF4RootPairing.pairingIn ℤ (typeF4RootPairing_baseEquiv i) (typeF4RootPairing_baseEquiv j) =
      typeF4CartanMatrix i j := typeF4RootPairing_base_cartan_apply i j

private lemma projectedPair_formula (a : Multiplicative F × Multiplicative F) :
    projectedPair a =
      rootElement typeF4RootPairing typeF4RootPairing_base F (typeF4RootPairing_baseEquiv 2) a.1.toAdd *
      rootElement typeF4RootPairing typeF4RootPairing_base F (-(typeF4RootPairing_baseEquiv 3) : typeF4Roots) a.2.toAdd :=
  map_mul (projection typeF4RootPairing typeF4RootPairing_base F) _ _

private lemma coroot_pair_action (i : Fin 4) (a : Multiplicative F × Multiplicative F) :
    coroot i * projectedPair a * (coroot i)⁻¹ =
      rootElement typeF4RootPairing typeF4RootPairing_base F (typeF4RootPairing_baseEquiv 2)
        ((((-1 : Fˣ) ^ typeF4CartanMatrix 2 i : Fˣ) : F) * a.1.toAdd) *
      rootElement typeF4RootPairing typeF4RootPairing_base F (-(typeF4RootPairing_baseEquiv 3) : typeF4Roots)
        ((((-1 : Fˣ) ^ (-typeF4CartanMatrix 3 i) : Fˣ) : F) * a.2.toAdd) := by
  rw [projectedPair_formula]
  rw [← MulAut.conj_apply, map_mul]
  simp only [MulAut.conj_apply]
  rw [coroot_conjugate_root,coroot_conjugate_root]
  simp only [RootPairing.indexNeg_neg, RootPairing.pairingIn_reflectionPerm_self_left, simple_pairing]

/-- The last coroot inverts the first root parameter and fixes the second. -/
theorem coroot_three_pair (a : Multiplicative F × Multiplicative F) :
    coroot 3 * projectedPair a * (coroot 3)⁻¹ = projectedPair (a.1⁻¹,a.2) := by
  rw [coroot_pair_action, projectedPair_formula]
  norm_num [typeF4CartanMatrix, Fin.ext_iff, toAdd_inv]

/-- The preceding short coroot fixes the first parameter and inverts the second. -/
theorem coroot_two_pair (a : Multiplicative F × Multiplicative F) :
    coroot 2 * projectedPair a * (coroot 2)⁻¹ = projectedPair (a.1,a.2⁻¹) := by
  rw [coroot_pair_action, projectedPair_formula]
  norm_num [typeF4CartanMatrix, Fin.ext_iff, toAdd_inv]

/-- The actual product of the two coroot involutions. -/
def inverter : F4 F := coroot 2 * coroot 3

theorem inverter_square : inverter (F := F) ^ 2 = 1 := by
  rw [inverter,(coroot_commute 2 3).mul_pow,coroot_square,coroot_square,mul_one]

/-- The product inverts the whole proved two-root plane. -/
theorem inverter_pair (a : Multiplicative F × Multiplicative F) :
    inverter * projectedPair a * (inverter (F := F))⁻¹ = projectedPair a⁻¹ := by
  rw [inverter]
  rw [show (coroot 2 * coroot 3) * projectedPair a * (coroot 2 * coroot 3)⁻¹ =
    coroot 2 * (coroot 3 * projectedPair a * (coroot 3)⁻¹) * (coroot 2)⁻¹ by group]
  rw [coroot_three_pair,coroot_two_pair]
  rfl

/-- Prime-field points of the original quotient root plane. -/
def planeHom (p : ℕ) [Fact p.Prime] [CharP F p] :
    Multiplicative (ZMod p) × Multiplicative (ZMod p) →* F4 F :=
  (Centralizer F).subtype.comp ((Residual p F).subtype.comp (primeFieldPair p))

private lemma planeHom_apply (p : ℕ) [Fact p.Prime] [CharP F p]
    (a : Multiplicative (ZMod p) × Multiplicative (ZMod p)) :
    planeHom p a = projectedPair
      (Multiplicative.ofAdd (ZMod.castHom (dvd_refl p) F a.1.toAdd),
       Multiplicative.ofAdd (ZMod.castHom (dvd_refl p) F a.2.toAdd)) := rfl

/-- The plane uses the same prime-field and defining-center quotient maps as DefiningPair. -/
theorem planeHom_injective (p : ℕ) [Fact p.Prime] [CharP F p] :
    Function.Injective (planeHom (F := F) p) := by
  exact (Centralizer F).subtype_injective.comp
    ((Residual p F).subtype_injective.comp (primeFieldPair_injective (F := F) p))

def plane (p : ℕ) [Fact p.Prime] [CharP F p] : Subgroup (F4 F) := (planeHom (F := F) p).range

/-- The two marked prime-field generators generate exactly the literal plane image. -/
theorem plane_generated (p : ℕ) [Fact p.Prime] [CharP F p] :
    Subgroup.closure ({planeHom (F := F) p (Multiplicative.ofAdd 1,1),
      planeHom p (1,Multiplicative.ofAdd 1)} : Set (F4 F)) = plane p := by
  apply le_antisymm
  · apply (Subgroup.closure_le (plane p)).mpr
    intro v hv
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl <;> exact ⟨_,rfl⟩
  · rintro v ⟨a,rfl⟩
    have ha : a = (Multiplicative.ofAdd (1 : ZMod p),1) ^ a.1.toAdd.val *
        (1,Multiplicative.ofAdd (1 : ZMod p)) ^ a.2.toAdd.val := by
      apply Prod.ext <;> apply Multiplicative.toAdd.injective <;>
        simp [toAdd_pow,nsmul_eq_mul]
    rw [ha,map_mul,map_pow,map_pow]
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem plane_card (p : ℕ) [Fact p.Prime] [CharP F p] : Nat.card (plane (F := F) p) = p ^ 2 := by
  change Nat.card (planeHom (F := F) p).range = p ^ 2
  rw [← Nat.card_congr (MonoidHom.ofInjective (planeHom_injective (F := F) p)).toEquiv]
  simp [Nat.card_prod,Nat.card_eq_fintype_card,pow_two]

theorem plane_pow (p : ℕ) [Fact p.Prime] [CharP F p] (a : plane (F := F) p) : a ^ p = 1 := by
  obtain ⟨v,hv⟩ := a.property
  apply Subtype.ext
  change a.val ^ p = 1
  rw [← hv,← map_pow]
  have hp : v ^ p = 1 := by
    apply Prod.ext <;> apply Multiplicative.toAdd.injective <;>
      simp only [Prod.pow_fst,Prod.pow_snd,Prod.fst_one,Prod.snd_one,toAdd_pow,toAdd_one,
        nsmul_eq_mul,CharP.cast_eq_zero (ZMod p) p,zero_mul]
  rw [hp,map_one]

private lemma planeHom_three (p : ℕ) [Fact p.Prime] [CharP F p]
    (a : Multiplicative (ZMod p) × Multiplicative (ZMod p)) :
    coroot (F := F) 3 * planeHom p a * (coroot 3)⁻¹ = planeHom p (a.1⁻¹,a.2) := by
  simp only [planeHom_apply,coroot_three_pair,toAdd_inv,map_neg,ofAdd_neg]

theorem plane_partial_inversion (p : ℕ) [Fact p.Prime] [CharP F p] :
    coroot (F := F) 3 * planeHom p (Multiplicative.ofAdd 1,1) * (coroot 3)⁻¹ =
      (planeHom p (Multiplicative.ofAdd 1,1))⁻¹ ∧
    Commute (coroot (F := F) 3) (planeHom p (1,Multiplicative.ofAdd 1)) := by
  constructor
  · simpa only [← map_inv,Prod.inv_mk,inv_one] using
      planeHom_three (F := F) p (Multiplicative.ofAdd 1,1)
  · change coroot 3 * planeHom p (1,Multiplicative.ofAdd 1) =
      planeHom p (1,Multiplicative.ofAdd 1) * coroot 3
    have h' : coroot (F := F) 3 * planeHom p (1,Multiplicative.ofAdd 1) * (coroot 3)⁻¹ =
        planeHom p (1,Multiplicative.ofAdd 1) := by
      simpa only [inv_one] using planeHom_three (F := F) p (1,Multiplicative.ofAdd 1)
    exact mul_inv_eq_iff_eq_mul.mp h'

theorem plane_total_inversion (p : ℕ) [Fact p.Prime] [CharP F p] :
    ∀ v ∈ plane (F := F) p, inverter * v * inverter⁻¹ = v⁻¹ := by
  rintro v ⟨a,rfl⟩
  rw [planeHom_apply,inverter_pair,map_inv]

/-- Every plane element centralizes the original fundamental involution. -/
theorem plane_centralizes (p : ℕ) [Fact p.Prime] [CharP F p] :
    plane (F := F) p ≤ Subgroup.centralizer ({F4RootSL2.hom (-1 : SL(2,F))} : Set (F4 F)) := by
  rintro v ⟨a,rfl⟩
  have hC : planeHom (F := F) p a ∈ Centralizer F :=
    (primeFieldPair (F := F) p a).val.property
  rw [centralizer_eq_range_centralizer] at hC
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    ((Subgroup.mem_centralizer_iff.mp hC) _ ⟨-1,rfl⟩).symm

end ExceptionalSplit.F4RootCentralizer.OddTorus
