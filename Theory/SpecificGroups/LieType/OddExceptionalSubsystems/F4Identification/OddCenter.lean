module

public import Theory.SpecificGroups.LieType.ExceptionalSplit.RootGeneration
public import Theory.AlgebraicGroup.Borel.IntegralChevalleyTorusConjugation
public import Theory.AlgebraicGroup.RootSystems.GeckDiagramAction
public import Mathlib.GroupTheory.IsPerfect

/-!
# Perfectness of the odd-characteristic F4 cover and its center quotient

A squared simple Tits lift is the diagonal coroot element at -1. Its exact
integral signs follow from the root-string lengths; specialization therefore
works in characteristic three as well. Each F4 simple root has a neighbor
with Cartan entry -1. Conjugation by that neighbor's coroot element inverts
its root parameter, expressing every signed simple-root element as a single
commutator when 2 is invertible. Simple-root generation makes the concrete
cover perfect. Grun's lemma then makes its quotient by its full center
centerless. Neither simplicity nor triviality of the cover's center is used.

This proves centerlessness of `ExceptionalSplit.F4`, not yet of the folded
E6 subgroup. The latter needs the independent matrix identification.

Sources: GLS3 §§2.2--2.4 (`refs/KGroup/GLS3/chapter2.tex`), the integral Tits
relations in `IntegralTitsCoherence`, and the F4 inclusion used in
Aschbacher--Smith A.2.17, printed p.39 of `refs/quasithin.pdf`.
-/

@[expose] public section

open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup.StandardRootSystem
open scoped Matrix
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification
set_option linter.unusedSectionVars false
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

private lemma sign_formula {F : Type*} [Field F] (i : b.support) (j : ι) :
    (-1 : F) ^ P.chainBotCoeff i j *
      (-1 : F) ^ P.chainBotCoeff i (P.reflectionPerm i j) =
        (-1 : F) ^ (-P.pairingIn ℤ j i) := by
  have href : P.chainBotCoeff i (P.reflectionPerm i j) = P.chainTopCoeff i j := by
    simpa using (diagram_chainBotCoeff (RootPairing.Equiv.reflection P i)
      i (P.reflectionPerm i j)).symm
  rw [href]
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · rw [← P.chainTopCoeff_sub_chainBotCoeff h]
    rw [zpow_sub₀ (neg_ne_zero.mpr one_ne_zero), zpow_natCast, zpow_natCast]
    simp [div_eq_mul_inv, ← inv_pow, mul_comm]
  · rw [P.chainBotCoeff_of_not_linearIndependent h,
      P.chainTopCoeff_of_not_linearIndependent h]
    obtain he | he := RootPairing.IsReduced.eq_or_eq_neg (P := P) j i (by
      simpa only [LinearIndependent.pair_symm_iff] using h)
    · have hi : j = i := P.root.injective he
      subst j
      simp
    · let := P.indexNeg
      have hi : j = -(i : ι) := P.root.injective (by simpa using he)
      subst j
      simp

private lemma cancellation_torus {F : Type*} [Field F] (i : b.support) :
    specializeMatrix (S := F) (titsLift i * titsLift i) =
      (integralChevalleyTorusElement (P := P)
        (integralChevalleySimpleCorootParameter i (-1 : Fˣ))).val := by
  have heval (a : b.support ⊕ ι) :
      (chevalleyBasisTorusUnit (P := P)
        (integralChevalleySimpleCorootParameter i (-1 : Fˣ)) a : F) =
        (-1 : F) ^ (-chevalleyBasisWeight (P := P) a i) := by
    simp [chevalleyBasisTorusUnit, integralChevalleySimpleCorootParameter]
  ext x y
  change specializeMatrix (titsLift i * titsLift i) x y = Matrix.diagonal _ x y
  rw [Matrix.diagonal_apply]
  cases y with
  | inl j =>
    have hc : (titsLift i * titsLift i) *ᵥ u j = u j := by
      rw [← Matrix.mulVec_mulVec, titsLift_mulVec_u, Matrix.mulVec_sub,
        Matrix.mulVec_smul, titsLift_mulVec_u, titsLift_mulVec_u]
      have hii : |b.cartanMatrix i i| = 2 := by simp
      rw [hii]
      module
    have h := congrArg (Int.castRingHom F) (congrFun hc x)
    by_cases hx : x = Sum.inl j
    · subst x
      simpa [specializeMatrix, u, Matrix.mulVec_single_one, Pi.single_apply,
        heval, chevalleyBasisWeight] using h
    · simpa [specializeMatrix, u, Matrix.mulVec_single_one, Pi.single_apply,
        heval, chevalleyBasisWeight, hx, Ne.symm hx] using h
  | inr j =>
    have hr : (titsLift i * titsLift i) *ᵥ v (b := b) j =
        ((-1 : ℤ) ^ P.chainBotCoeff i j *
          (-1 : ℤ) ^ P.chainBotCoeff i (P.reflectionPerm i j)) • v (b := b) j := by
      let := P.indexNeg
      rw [← Matrix.mulVec_mulVec, titsLift_mulVec_v, Matrix.mulVec_smul,
        titsLift_mulVec_v, P.reflectionPerm_self, smul_smul]
    have h := congrArg (Int.castRingHom F) (congrFun hr x)
    by_cases hx : x = Sum.inr j
    · subst x
      simpa [specializeMatrix, v, Matrix.mulVec_single_one, Pi.single_apply,
        heval, chevalleyBasisWeight, sign_formula] using h
    · simpa [specializeMatrix, v, Matrix.mulVec_single_one, Pi.single_apply,
        heval, chevalleyBasisWeight, hx, Ne.symm hx] using h

private lemma minus_one_torus_mem {F : Type*} [Field F] (i : b.support) :
    integralChevalleyTorusElement (P := P)
      (integralChevalleySimpleCorootParameter i (-1 : Fˣ)) ∈
        ExceptionalSplit.rootGenerated P b F := by
  have he : integralChevalleyTorusElement (P := P)
      (integralChevalleySimpleCorootParameter i (-1 : Fˣ)) =
        rootCurveTitsWord (S := F) [i] * rootCurveTitsWord (S := F) [i] := by
    apply Units.ext
    rw [← cancellation_torus]
    change specializeMatrix (titsLift i * titsLift i) =
      specializeMatrix (titsWord [i]) * specializeMatrix (titsWord [i])
    simp [specializeMatrix_mul, titsWord]
  rw [he]
  change _ ∈ allRootCurveSubgroup b F
  rw [allRootCurveSubgroup_eq_simpleSubgroup]
  exact Subgroup.mul_mem _ (rootCurveTitsWord_mem _) (rootCurveTitsWord_mem _)


open scoped commutatorElement

private lemma elementary_mem_commutator {F : Type*} [Field F]
    (htwo : (2 : F) ≠ 0) (q : b.support) (r : ι)
    (hp : Odd (P.pairingIn ℤ r q)) (t : F) :
    ExceptionalSplit.elementaryRoot P b F r t ∈
      commutator (ExceptionalSplit.rootGenerated P b F) := by
  let z : ExceptionalSplit.rootGenerated P b F :=
    ⟨integralChevalleyTorusElement (P := P)
      (integralChevalleySimpleCorootParameter q (-1 : Fˣ)), minus_one_torus_mem q⟩
  let a := ExceptionalSplit.elementaryRoot P b F r (-t / 2)
  have hz : z⁻¹ * a * z = ExceptionalSplit.elementaryRoot P b F r (-(-t / 2)) := by
    apply Subtype.ext
    have hh := integralChevalleyRootCurve_simpleCoroot_conjugation
      (S := F) q (-1 : Fˣ) r (-t / 2)
    simpa only [z, a, ExceptionalSplit.elementaryRoot, Subgroup.coe_mul, Subgroup.coe_inv,
      Units.val_zpow_eq_zpow_val, Units.val_neg, Units.val_one,
      hp.neg_one_zpow, neg_one_mul] using hh
  have ha : a⁻¹ = ExceptionalSplit.elementaryRoot P b F r (-(-t / 2)) := by
    apply inv_eq_of_mul_eq_one_right
    rw [← ExceptionalSplit.elementaryRoot_add]
    simp
  have he : ⁅z⁻¹, a⁆ = ExceptionalSplit.elementaryRoot P b F r t := by
    rw [commutatorElement_def, inv_inv, hz, ha, ← ExceptionalSplit.elementaryRoot_add]
    congr 1
    field_simp
    ring
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

attribute [local instance] Classical.decEq
local instance oddCenterRootFintype : Fintype typeF4Roots := Fintype.ofFinite _

private def neighbor (i : Fin 4) : Fin 4 := ![1, 0, 3, 2] i

private lemma neighbor_pairing (i : Fin 4) :
    typeF4RootPairing.pairingIn ℤ (typeF4RootPairing_baseEquiv i)
      (typeF4RootPairing_baseEquiv (neighbor i)) = -1 := by
  change typeF4RootPairing_base.cartanMatrix _ _ = _
  rw [typeF4RootPairing_base_cartan_apply]
  fin_cases i <;> norm_num [neighbor, typeF4CartanMatrix, Fin.ext_iff]

/-- The actual F4 adjoint matrix cover is perfect when 2 is invertible. -/
theorem cover_isPerfect (F : Type*) [Field F] (htwo : (2 : F) ≠ 0) :
    Group.IsPerfect (ExceptionalSplit.rootGenerated typeF4RootPairing
      typeF4RootPairing_base F) := by
  let := typeF4RootPairing.indexNeg
  constructor
  apply ExceptionalSplit.elementary_subgroup_eq_top_of_simple
  · intro i t
    obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
    apply elementary_mem_commutator htwo (typeF4RootPairing_baseEquiv (neighbor j)) _ _ t
    rw [neighbor_pairing]
    decide
  · dsimp only
    intro i t
    obtain ⟨j, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
    apply elementary_mem_commutator htwo (typeF4RootPairing_baseEquiv (neighbor j)) _ _ t
    simpa only [RootPairing.indexNeg_neg, RootPairing.pairingIn_reflectionPerm_self_left,
      neighbor_pairing, neg_neg] using (show Odd (1 : ℤ) by decide)

/-- The actual F4 central quotient is centerless in every characteristic other than two. -/
theorem source_center_eq_bot (F : Type*) [Field F] (htwo : (2 : F) ≠ 0) :
    Subgroup.center (ExceptionalSplit.F4 F) = ⊥ := by
  let := cover_isPerfect F htwo
  exact Group.IsPerfect.center_quotient_center_eq_bot _

end TwistedE6.FoldedSubsystem.F4Identification
