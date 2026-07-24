/-
Authors: OpenAI
-/

module

public import Submission.BenderSuzuki.External.Higman.theorem_1b
public import Submission.BenderSuzuki.External.Higman.lemma_12
public import Submission.BenderSuzuki.External.Higman.theorem_1e_scalar_coordinates
import FeitThompson.GroupAction.Quotient

/-!
# Higman's classification theorem for Suzuki 2-groups: extracted branch
-/

namespace BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII

universe u
/-- Theorem 1(e), second clause: action coordinates from the actor-relative
Type-B branch of Lemma 12. -/
public theorem theorem1_typeB_coordinates
    {K P : Type u} [Group K] [Group P] [MulDistribMulAction K P]
    (hP : IsSuzukiTwoGroup P)
    (_hKcyclic : IsCyclic K) (hKfaithful : FaithfulSMul K P)
    (hKregular : ActionRegularOn K P (involutions P))
    (hBActor : ∃ (B : Subgroup P) (actor : K),
      Lemma12TypeBActorBranchData K P actor B) :
    ∃ (n : ℕ) (_ : n ≠ 0)
        (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
        (epsilon : BinaryGaloisField n)
        (tripleLift :
          BinaryGaloisField n → BinaryGaloisField n → BinaryGaloisField n → P)
        (cocycle :
          BinaryGaloisField n → BinaryGaloisField n →
            BinaryGaloisField n → BinaryGaloisField n → BinaryGaloisField n)
        (eK : K ≃* (BinaryGaloisField n)ˣ)
        (eQ : (P ⧸ Subgroup.center P) ≃*
          Multiplicative (BinaryGaloisField n × BinaryGaloisField n))
        (eZ : Subgroup.center P ≃*
          Multiplicative (BinaryGaloisField n)),
      epsilon ≠ 0 ∧
      (∃ r : ℕ, Odd r ∧ 0 < r ∧
        ∀ x : BinaryGaloisField n, theta^[r] x = x) ∧
      (∀ a b : BinaryGaloisField n, a ≠ 0 → b ≠ 0 →
        a * theta a + epsilon * a * theta b + b * theta b ≠ 0) ∧
      (∀ a b e f c d : BinaryGaloisField n,
        cocycle (a + e) (b + f) c d = cocycle a b c d + cocycle e f c d) ∧
      (∀ a b e f c d : BinaryGaloisField n,
        cocycle a b (e + c) (f + d) = cocycle a b e f + cocycle a b c d) ∧
      (∀ a b : BinaryGaloisField n,
        cocycle a b a b = a * theta a + epsilon * a * theta b + b * theta b) ∧
      (∀ c a b : BinaryGaloisField n, tripleLift c a b ∈ (⊤ : Subgroup P)) ∧
      tripleLift 0 0 0 = 1 ∧
      (∀ x : P, ∃ c a b : BinaryGaloisField n, x = tripleLift c a b) ∧
      (∀ c a b d e f : BinaryGaloisField n,
        tripleLift c a b = tripleLift d e f → c = d ∧ a = e ∧ b = f) ∧
      (∀ c a b d e f : BinaryGaloisField n,
        tripleLift c a b * tripleLift d e f =
          tripleLift (c + d + cocycle a b e f) (a + e) (b + f)) ∧
      (∀ k : K, ∀ p : P,
        (eQ (QuotientGroup.mk' (Subgroup.center P) (k • p))).toAdd =
          ((eK k : BinaryGaloisField n) *
              (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd.1,
            (eK k : BinaryGaloisField n) *
              (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd.2)) ∧
      ∀ k : K, ∀ z : BinaryGaloisField n,
        k • ((eZ.symm (Multiplicative.ofAdd z) : Subgroup.center P) : P) =
          ((eZ.symm (Multiplicative.ofAdd
            ((eK k : BinaryGaloisField n) * theta (eK k : BinaryGaloisField n) * z)) :
              Subgroup.center P) : P) := by
  classical
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  obtain ⟨x0, _y0, hx0, _hy0, _hxy0⟩ := hP.2.2.1
  let orbit : K → {x : P // x ∈ involutions P} :=
    fun k => ⟨k • x0, hKregular.1 x0 hx0 k⟩
  have horbit_injective : Function.Injective orbit := by
    intro k l hkl
    have heq : k • x0 = l • x0 := congrArg Subtype.val hkl
    rcases hKregular.2 x0 hx0 (k • x0)
        (hKregular.1 x0 hx0 k) with ⟨a, _ha, huniq⟩
    exact (huniq k rfl).trans (huniq l heq).symm
  have horbit_surjective : Function.Surjective orbit := by
    rintro ⟨y, hy⟩
    rcases hKregular.2 x0 hx0 y hy with ⟨k, hk, _huniq⟩
    exact ⟨k, Subtype.ext hk.symm⟩
  have hKcard_invol : Nat.card K =
      Nat.card {x : P // x ∈ involutions P} :=
    Nat.card_congr (Equiv.ofBijective orbit
      ⟨horbit_injective, horbit_surjective⟩)
  rcases hBActor with ⟨B, actor, hactorData⟩
  rcases hactorData with
    ⟨n, xi, q0, squareMap, hn, hxi_actor, hq0_ker, hq0_surj,
      hq0_actor, hL1_eq_B, hkernel1_bot, hB_le_center, hB_card,
      hfactor0_card, hinvolution_card, hactorCoordinates⟩
  rcases hactorCoordinates with
    ⟨theta, epsilon, tripleLift, cocycle, quotientCoordinates,
      centerCoordinates, lambdaUnit, hepsilon, hperiod, hanisotropic,
      hcocycle_left, hcocycle_right, hcocycle_diag, htriple_mem,
      htriple_one, htriple_surj, htriple_inj, htriple_mul,
      _hsquareCoordinates, hlambda_order, hquotientCoordinates_actor,
      hcenterCoordinates_actor⟩
  have hB : IsSuzukiTwoTypeB (⊤ : Subgroup P) := by
    refine ⟨n, hn, theta, epsilon, tripleLift, cocycle,
      hepsilon, hperiod, hanisotropic, hcocycle_left, hcocycle_right,
      hcocycle_diag, htriple_mem, htriple_one, ?_, htriple_inj, htriple_mul⟩
    intro x _hx
    exact htriple_surj x
  have hcard : Nat.card P = Nat.card (Subgroup.center P) ^ 3 :=
    (theorem1b_typeB_data hB).1
  letI : FaithfulSMul K P := hKfaithful
  letI : Finite K := Finite.of_injective
    (MulDistribMulAction.toMulAut K P) (by
      intro k l hkl
      apply FaithfulSMul.eq_of_smul_eq_smul (α := P)
      intro p
      exact congrArg (fun f : MulAut P => f p) hkl)
  letI : Fintype K := Fintype.ofFinite K
  have hKcard : Nat.card K = 2 ^ n - 1 :=
    hKcard_invol.trans hinvolution_card
  let T := lowerCentralFactorLinearAut xi 0
  have hquotientCoordinates_actor_pow (j : ℕ)
      (a b : BinaryGaloisField n) :
      (T ^ j) (quotientCoordinates (a, b)) =
        quotientCoordinates
          ((((lambdaUnit ^ j : (BinaryGaloisField n)ˣ) :
              BinaryGaloisField n) * a),
            (((lambdaUnit ^ j : (BinaryGaloisField n)ˣ) :
              BinaryGaloisField n) * b)) := by
    induction j generalizing a b with
    | zero => simp
    | succ j ih =>
        rw [pow_succ, LinearEquiv.mul_apply, hquotientCoordinates_actor, ih]
        simp [pow_succ, mul_assoc]
  have hT_pow : T ^ orderOf xi = 1 := by
    change (lowerCentralFactorLinearAut xi 0) ^ orderOf xi = 1
    rw [← lowerCentralFactorLinearAut_pow, pow_orderOf_eq_one]
    exact map_one (lowerCentralFactorLinearAutHom (H := P) 0)
  have hlambda_pow : lambdaUnit ^ orderOf xi = 1 := by
    apply Units.ext
    have happly := congrArg
      (fun f : Additive (LowerCentralFactor P 0) ≃ₗ[ZMod 2]
          Additive (LowerCentralFactor P 0) =>
        f (quotientCoordinates (1, 0))) hT_pow
    change (T ^ orderOf xi) (quotientCoordinates (1, 0)) =
      quotientCoordinates (1, 0) at happly
    rw [hquotientCoordinates_actor_pow] at happly
    have hpairs := quotientCoordinates.injective happly
    simpa using congrArg Prod.fst hpairs
  have hlambda_dvd_xi : 2 ^ n - 1 ∣ orderOf xi := by
    rw [← hlambda_order]
    exact orderOf_dvd_of_pow_eq_one hlambda_pow
  have hxi_dvd_actor : orderOf xi ∣ orderOf actor := by
    rw [hxi_actor]
    exact orderOf_map_dvd (MulDistribMulAction.toMulAut K P) actor
  have hbase_dvd_actor : 2 ^ n - 1 ∣ orderOf actor :=
    hlambda_dvd_xi.trans hxi_dvd_actor
  have hactor_dvd_base : orderOf actor ∣ 2 ^ n - 1 := by
    have hactor_card : orderOf actor ∣ Fintype.card K := orderOf_dvd_card
    rw [← Nat.card_eq_fintype_card, hKcard] at hactor_card
    exact hactor_card
  have hactor_order : orderOf actor = 2 ^ n - 1 :=
    Nat.dvd_antisymm hactor_dvd_base hbase_dvd_actor
  have hactor_generator : ∀ k : K, k ∈ Subgroup.zpowers actor := by
    have htop : Subgroup.zpowers actor = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers,
        hactor_order, hKcard]
    intro k
    rw [htop]
    trivial
  have hlambda_units_card :
      Nat.card (BinaryGaloisField n)ˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, GaloisField.card 2 n hn]
  have hlambda_generator :
      ∀ x : (BinaryGaloisField n)ˣ, x ∈ Subgroup.zpowers lambdaUnit := by
    have htop : Subgroup.zpowers lambdaUnit = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers,
        hlambda_order, hlambda_units_card]
    intro x
    rw [htop]
    trivial
  let eK : K ≃* (BinaryGaloisField n)ˣ :=
    mulEquivOfOrderOfEq hactor_generator hlambda_generator
      (hactor_order.trans hlambda_order.symm)
  have heK_actor : eK actor = lambdaUnit := by
    exact mulEquivOfOrderOfEq_apply_gen _ _ _
  letI : B.Normal := by
    rw [← hq0_ker]
    infer_instance
  let eB : P ⧸ B ≃* LowerCentralFactor P 0 :=
    (QuotientGroup.quotientMulEquivOfEq hq0_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q0 hq0_surj)
  have hquotientB_card :
      Nat.card (P ⧸ B) = Nat.card (LowerCentralFactor P 0) :=
    Nat.card_congr eB.toEquiv
  have hP_card_n : Nat.card P = (2 ^ n) ^ 3 := by
    calc
      Nat.card P = Nat.card (P ⧸ B) * Nat.card B :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup B
      _ = (2 ^ n) ^ 3 := by
        rw [hquotientB_card, hfactor0_card, hB_card]
        ring
  have hcenter_card : Nat.card (Subgroup.center P) = 2 ^ n := by
    apply Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0)
    exact hcard.symm.trans hP_card_n
  have hB_eq_center : B = Subgroup.center P := by
    apply Subgroup.eq_of_le_of_card_ge hB_le_center
    rw [hB_card, hcenter_card]
  have hq0_ker_center : q0.ker = Subgroup.center P :=
    hq0_ker.trans hB_eq_center
  let factorZeroCoordinates : LowerCentralFactor P 0 ≃*
      Multiplicative
        (BinaryGaloisField n × BinaryGaloisField n) :=
    MulEquiv.toMultiplicative_toAdditive.symm.trans
      quotientCoordinates.symm.toAddEquiv.toMultiplicative
  let pi : P →* Multiplicative
      (BinaryGaloisField n × BinaryGaloisField n) :=
    factorZeroCoordinates.toMonoidHom.comp q0
  have hpi_surj : Function.Surjective pi :=
    factorZeroCoordinates.surjective.comp hq0_surj
  have hpi_ker : pi.ker = Subgroup.center P := by
    rw [← hq0_ker_center]
    ext p
    change factorZeroCoordinates (q0 p) = 1 ↔ q0 p = 1
    exact factorZeroCoordinates.map_eq_one_iff
  let eQ : (P ⧸ Subgroup.center P) ≃*
      Multiplicative
        (BinaryGaloisField n × BinaryGaloisField n) :=
    (QuotientGroup.quotientMulEquivOfEq hpi_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective pi hpi_surj)
  have heQ_mk (p : P) :
      eQ (QuotientGroup.mk' (Subgroup.center P) p) = pi p := by
    change QuotientGroup.kerLift pi
        (QuotientGroup.quotientMulEquivOfEq hpi_ker.symm
          (QuotientGroup.mk' (Subgroup.center P) p)) = pi p
    calc
      QuotientGroup.kerLift pi
          (QuotientGroup.quotientMulEquivOfEq hpi_ker.symm
            (QuotientGroup.mk' (Subgroup.center P) p)) =
        QuotientGroup.kerLift pi (QuotientGroup.mk' pi.ker p) := by
          exact congrArg (QuotientGroup.kerLift pi)
            (QuotientGroup.quotientMulEquivOfEq_mk hpi_ker.symm p)
      _ = pi p := QuotientGroup.kerLift_mk pi p
  have hpi_actor (p : P) :
      (pi (actor • p)).toAdd =
        (((lambdaUnit : BinaryGaloisField n) * (pi p).toAdd.1,
          (lambdaUnit : BinaryGaloisField n) * (pi p).toAdd.2)) := by
    change quotientCoordinates.symm (Additive.ofMul (q0 (actor • p))) = _
    rw [hq0_actor]
    let ab := quotientCoordinates.symm (Additive.ofMul (q0 p))
    have hab : Additive.ofMul (q0 p) = quotientCoordinates ab :=
      (quotientCoordinates.apply_symm_apply _).symm
    rw [hab, hquotientCoordinates_actor]
    simp [pi, factorZeroCoordinates]
  have hpi_action : ∀ k : K, ∀ p : P,
      (pi (k • p)).toAdd =
        (((eK k : BinaryGaloisField n) * (pi p).toAdd.1,
          (eK k : BinaryGaloisField n) * (pi p).toAdd.2)) := by
    intro k
    obtain ⟨j, rfl⟩ :=
      mem_powers_iff_mem_zpowers.mpr (hactor_generator k)
    intro p
    induction j generalizing p with
    | zero => simp
    | succ j ih =>
        change (pi ((actor ^ (j + 1)) • p)).toAdd = _
        rw [pow_succ, mul_smul, ih, hpi_actor]
        simp [map_pow, heK_actor]
        constructor <;> ring
  have hquotient_action : ∀ k : K, ∀ p : P,
      (eQ (QuotientGroup.mk' (Subgroup.center P) (k • p))).toAdd =
        (((eK k : BinaryGaloisField n) *
            (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd.1,
          (eK k : BinaryGaloisField n) *
            (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd.2)) := by
    intro k p
    rw [heQ_mk, heQ_mk]
    exact hpi_action k p
  let factorOneEquiv : LowerCentralFactor P 1 ≃*
      higmanLowerCentralSeries P 1 :=
    (QuotientGroup.quotientMulEquivOfEq hkernel1_bot).trans
      (QuotientGroup.quotientBot (G := higmanLowerCentralSeries P 1))
  let centerCoordinatesMul : Multiplicative (BinaryGaloisField n) ≃*
      LowerCentralFactor P 1 :=
    centerCoordinates.toAddEquiv.toMultiplicative.trans
      MulEquiv.toMultiplicative_toAdditive
  let iota : Multiplicative (BinaryGaloisField n) →* P :=
    (higmanLowerCentralSeries P 1).subtype.comp
      (factorOneEquiv.toMonoidHom.comp centerCoordinatesMul.toMonoidHom)
  have hiota : Function.Injective iota := by
    intro z w h
    apply centerCoordinatesMul.injective
    apply factorOneEquiv.injective
    apply Subtype.ext
    exact h
  have hL1_eq_center : higmanLowerCentralSeries P 1 = Subgroup.center P :=
    hL1_eq_B.trans hB_eq_center
  have hiota_range : iota.range = Subgroup.center P := by
    rw [← hL1_eq_center]
    ext p
    constructor
    · rintro ⟨z, rfl⟩
      exact (factorOneEquiv (centerCoordinatesMul z)).property
    · intro hp
      let p1 : higmanLowerCentralSeries P 1 := ⟨p, hp⟩
      let z : Multiplicative (BinaryGaloisField n) :=
        centerCoordinatesMul.symm (factorOneEquiv.symm p1)
      refine ⟨z, ?_⟩
      change ((factorOneEquiv (centerCoordinatesMul z) :
        higmanLowerCentralSeries P 1) : P) = p
      have hz : centerCoordinatesMul z = factorOneEquiv.symm p1 := by
        simp [z]
      rw [hz]
      exact congrArg Subtype.val (factorOneEquiv.apply_symm_apply p1)
  have hfactorOne_mk_outer (y : higmanLowerCentralSeries P 1) :
      factorOneEquiv
          (QuotientGroup.mk' (lowerCentralFactorKernel P 1) y) = y := by
    have hmk :
        (QuotientGroup.quotientMulEquivOfEq hkernel1_bot)
            ((QuotientGroup.mk' (lowerCentralFactorKernel P 1)) y) =
          (QuotientGroup.mk y : higmanLowerCentralSeries P 1 ⧸
            (⊥ : Subgroup (higmanLowerCentralSeries P 1))) := by
      simpa only [QuotientGroup.mk'_apply] using
        (QuotientGroup.quotientMulEquivOfEq_mk hkernel1_bot y)
    calc
      factorOneEquiv
          ((QuotientGroup.mk' (lowerCentralFactorKernel P 1)) y) =
        QuotientGroup.quotientBot
          ((QuotientGroup.quotientMulEquivOfEq hkernel1_bot)
            ((QuotientGroup.mk'
              (lowerCentralFactorKernel P 1)) y)) := by rfl
      _ = QuotientGroup.quotientBot
          (QuotientGroup.mk y : higmanLowerCentralSeries P 1 ⧸
            (⊥ : Subgroup (higmanLowerCentralSeries P 1))) := by rw [hmk]
      _ = y := by
        rfl
  have hfactorOne_mk_equiv (v : LowerCentralFactor P 1) :
      QuotientGroup.mk' (lowerCentralFactorKernel P 1)
          (factorOneEquiv v) = v := by
    apply factorOneEquiv.injective
    rw [hfactorOne_mk_outer]
  have hcenter_factor_actor (z : BinaryGaloisField n) :
      QuotientGroup.mk' (lowerCentralFactorKernel P 1)
          (lowerCentralSeriesMulAut xi 1
            (factorOneEquiv
              (centerCoordinatesMul (Multiplicative.ofAdd z)))) =
        centerCoordinatesMul
          (Multiplicative.ofAdd
            ((lambdaUnit : BinaryGaloisField n) *
              theta (lambdaUnit : BinaryGaloisField n) * z)) := by
    apply Additive.ofMul.injective
    rw [← lowerCentralFactorLinearAut_ofMul_mk]
    rw [hfactorOne_mk_equiv]
    change lowerCentralFactorLinearAut xi 1 (centerCoordinates z) =
      centerCoordinates
        ((lambdaUnit : BinaryGaloisField n) *
          theta (lambdaUnit : BinaryGaloisField n) * z)
    exact hcenterCoordinates_actor z
  have hiota_actor (z : BinaryGaloisField n) :
      actor • iota (Multiplicative.ofAdd z) =
        iota (Multiplicative.ofAdd
          ((lambdaUnit : BinaryGaloisField n) *
            theta (lambdaUnit : BinaryGaloisField n) * z)) := by
    let y : higmanLowerCentralSeries P 1 :=
      factorOneEquiv (centerCoordinatesMul (Multiplicative.ofAdd z))
    have hy_action : actor • (y : P) =
        ((lowerCentralSeriesMulAut xi 1 y :
          higmanLowerCentralSeries P 1) : P) := by
      change actor • (y : P) = xi (y : P)
      rw [hxi_actor]
      rfl
    change actor • (y : P) =
      ((factorOneEquiv
        (centerCoordinatesMul
          (Multiplicative.ofAdd
            ((lambdaUnit : BinaryGaloisField n) *
              theta (lambdaUnit : BinaryGaloisField n) * z))) :
            higmanLowerCentralSeries P 1) : P)
    rw [hy_action]
    apply congrArg Subtype.val
    calc
      lowerCentralSeriesMulAut xi 1 y =
          factorOneEquiv
            (QuotientGroup.mk' (lowerCentralFactorKernel P 1)
              (lowerCentralSeriesMulAut xi 1 y)) :=
        (hfactorOne_mk_outer
          (lowerCentralSeriesMulAut xi 1 y)).symm
      _ = factorOneEquiv
          (centerCoordinatesMul
            (Multiplicative.ofAdd
              ((lambdaUnit : BinaryGaloisField n) *
                theta (lambdaUnit : BinaryGaloisField n) * z))) := by
        rw [hcenter_factor_actor]
  let iotaCenter : Multiplicative (BinaryGaloisField n) →*
      Subgroup.center P :=
    { toFun := fun z =>
        ⟨iota z, by rw [← hiota_range]; exact ⟨z, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        exact map_one iota
      map_mul' := by
        intro z w
        apply Subtype.ext
        exact map_mul iota z w }
  have hiotaCenter_injective : Function.Injective iotaCenter := by
    intro z w hzw
    apply hiota
    simpa [iotaCenter] using congrArg Subtype.val hzw
  have hiotaCenter_surjective : Function.Surjective iotaCenter := by
    intro z
    have hz : (z : P) ∈ iota.range := by
      rw [hiota_range]
      exact z.property
    rcases hz with ⟨w, hw⟩
    exact ⟨w, Subtype.ext hw⟩
  let eZ : Subgroup.center P ≃*
      Multiplicative (BinaryGaloisField n) :=
    (MulEquiv.ofBijective iotaCenter
      ⟨hiotaCenter_injective, hiotaCenter_surjective⟩).symm
  have hiota_action : ∀ k : K, ∀ z : BinaryGaloisField n,
      k • iota (Multiplicative.ofAdd z) =
        iota (Multiplicative.ofAdd
          ((eK k : BinaryGaloisField n) *
            theta (eK k : BinaryGaloisField n) * z)) := by
    intro k
    obtain ⟨j, rfl⟩ :=
      mem_powers_iff_mem_zpowers.mpr (hactor_generator k)
    intro z
    induction j generalizing z with
    | zero => simp
    | succ j ih =>
        change (actor ^ (j + 1)) • iota (Multiplicative.ofAdd z) = _
        rw [pow_succ, mul_smul, hiota_actor, ih]
        simp [map_pow, heK_actor]
        apply congrArg iota
        apply congrArg Multiplicative.ofAdd
        ring
  have hcenter_action : ∀ k : K, ∀ z : BinaryGaloisField n,
      k • ((eZ.symm (Multiplicative.ofAdd z) :
          Subgroup.center P) : P) =
        ((eZ.symm (Multiplicative.ofAdd
          ((eK k : BinaryGaloisField n) *
            theta (eK k : BinaryGaloisField n) * z)) :
              Subgroup.center P) : P) := by
    intro k z
    change k • iota (Multiplicative.ofAdd z) =
      iota (Multiplicative.ofAdd
        ((eK k : BinaryGaloisField n) *
          theta (eK k : BinaryGaloisField n) * z))
    exact hiota_action k z
  exact
    ⟨n, hn, theta, epsilon, tripleLift, cocycle, eK, eQ, eZ,
      hepsilon, hperiod, hanisotropic, hcocycle_left, hcocycle_right,
      hcocycle_diag, htriple_mem, htriple_one, htriple_surj,
      htriple_inj, htriple_mul, hquotient_action, hcenter_action⟩

set_option maxHeartbeats 800000 in
/-- The retained actor-relative Type-B branch supplies two explicit,
actor-equivariantly isomorphic coordinate summands in the central quotient. -/
public theorem theorem1_isomorphic_summands_of_typeB_actor
    {K P : Type u} [Group K] [Group P] [MulDistribMulAction K P]
    (hP : IsSuzukiTwoGroup P)
    (hKcyclic : IsCyclic K) (hKfaithful : FaithfulSMul K P)
    (hKregular : ActionRegularOn K P (involutions P))
    (hBActor : ∃ (B : Subgroup P) (actor : K),
      Lemma12TypeBActorBranchData K P actor B) :
    Theorem1IsomorphicSummands K P := by
  classical
  letI : Finite P := finite_of_isSuzukiTwoGroup hP
  rcases theorem1_typeB_coordinates
      hP hKcyclic hKfaithful hKregular hBActor with
    ⟨n, hn, _theta, _epsilon, _tripleLift, _cocycle, eK, eQ, eZ,
      _hepsilon, _hperiod, _hanisotropic, _hcocycleLeft, _hcocycleRight,
      _hcocycleDiag, _htripleMem, _htripleOne, _htripleSurj,
      _htripleInj, _htripleMul, hquotientCoordinates, _hcenterCoordinates⟩
  let F := BinaryGaloisField n
  let hcenterInvariant : IsInvariant K P (Subgroup.center P) :=
    ⟨isXInvariantSubgroup_center K P⟩
  letI : MulAction.QuotientAction K (Subgroup.center P) :=
    quotientAction_of_isInvariant (Subgroup.center P) hcenterInvariant
  let quotientAction : MulDistribMulAction K (P ⧸ Subgroup.center P) :=
    quotientMulDistribMulAction (Subgroup.center P) hcenterInvariant
  letI : MulDistribMulAction K (P ⧸ Subgroup.center P) := quotientAction
  have hquotientAction_mk (k : K) (p : P) :
      k • QuotientGroup.mk' (Subgroup.center P) p =
        QuotientGroup.mk' (Subgroup.center P) (k • p) :=
    MulAction.Quotient.smul_mk (Subgroup.center P) k p
  have heQ_action (k : K) (q : P ⧸ Subgroup.center P) :
      (eQ (k • q)).toAdd =
        ((eK k : F) * (eQ q).toAdd.1,
          (eK k : F) * (eQ q).toAdd.2) := by
    obtain ⟨p, rfl⟩ :=
      QuotientGroup.mk'_surjective (Subgroup.center P) q
    rw [hquotientAction_mk]
    exact hquotientCoordinates k p
  let U : Subgroup (P ⧸ Subgroup.center P) :=
    { carrier := {q | (eQ q).toAdd.2 = 0}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change (eQ a).toAdd.2 = 0 at ha
        change (eQ b).toAdd.2 = 0 at hb
        simp [map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        simpa [map_inv, ha] }
  let V : Subgroup (P ⧸ Subgroup.center P) :=
    { carrier := {q | (eQ q).toAdd.1 = 0}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        change (eQ a).toAdd.1 = 0 at ha
        change (eQ b).toAdd.1 = 0 at hb
        simp [map_mul, ha, hb]
      inv_mem' := by
        intro a ha
        simpa [map_inv, ha] }
  have hUforward (k : K) (q : P ⧸ Subgroup.center P)
      (hq : q ∈ U) : k • q ∈ U := by
    change (eQ (k • q)).toAdd.2 = 0
    rw [heQ_action]
    change (eK k : F) * (eQ q).toAdd.2 = 0
    rw [show (eQ q).toAdd.2 = 0 from hq, mul_zero]
  have hVforward (k : K) (q : P ⧸ Subgroup.center P)
      (hq : q ∈ V) : k • q ∈ V := by
    change (eQ (k • q)).toAdd.1 = 0
    rw [heQ_action]
    change (eK k : F) * (eQ q).toAdd.1 = 0
    rw [show (eQ q).toAdd.1 = 0 from hq, mul_zero]
  have hU : IsXInvariantSubgroup K U := by
    intro k q
    constructor
    · exact hUforward k q
    · intro hq
      have hback := hUforward k⁻¹ (k • q) hq
      simpa [smul_smul] using hback
  have hV : IsXInvariantSubgroup K V := by
    intro k q
    constructor
    · exact hVforward k q
    · intro hq
      have hback := hVforward k⁻¹ (k • q) hq
      simpa [smul_smul] using hback
  let swapMul : Multiplicative (F × F) ≃* Multiplicative (F × F) :=
    (AddEquiv.prodComm : F × F ≃+ F × F).toMultiplicative
  let swapQ : (P ⧸ Subgroup.center P) ≃*
      (P ⧸ Subgroup.center P) :=
    eQ.trans (swapMul.trans eQ.symm)
  have hswapU (q : P ⧸ Subgroup.center P) (hq : q ∈ U) :
      swapQ q ∈ V := by
    change (eQ q).toAdd.2 = 0 at hq
    change (eQ (swapQ q)).toAdd.1 = 0
    simpa [swapQ, swapMul] using hq
  have hswapV (q : P ⧸ Subgroup.center P) (hq : q ∈ V) :
      swapQ q ∈ U := by
    change (eQ q).toAdd.1 = 0 at hq
    change (eQ (swapQ q)).toAdd.2 = 0
    simpa [swapQ, swapMul] using hq
  let eUV : U ≃* V :=
    { toFun := fun u => ⟨swapQ u, hswapU u u.property⟩
      invFun := fun v => ⟨swapQ v, hswapV v v.property⟩
      left_inv := by
        intro u
        apply Subtype.ext
        simp [swapQ, swapMul]
      right_inv := by
        intro v
        apply Subtype.ext
        simp [swapQ, swapMul]
      map_mul' := by
        intro u v
        apply Subtype.ext
        exact swapQ.map_mul (u : P ⧸ Subgroup.center P) v }
  let axisU : Multiplicative F ≃ U :=
    { toFun := fun a =>
        ⟨eQ.symm (Multiplicative.ofAdd (a.toAdd, 0)), by
          change (eQ (eQ.symm (Multiplicative.ofAdd (a.toAdd, 0)))).toAdd.2 = 0
          simp⟩
      invFun := fun u => Multiplicative.ofAdd (eQ u).toAdd.1
      left_inv := by
        intro a
        simp
      right_inv := by
        intro u
        apply Subtype.ext
        apply eQ.injective
        simp only [eQ.apply_symm_apply]
        apply Multiplicative.ofAdd.injective
        exact Prod.ext rfl u.property.symm }
  let axisV : Multiplicative F ≃ V :=
    { toFun := fun a =>
        ⟨eQ.symm (Multiplicative.ofAdd (0, a.toAdd)), by
          change (eQ (eQ.symm (Multiplicative.ofAdd (0, a.toAdd)))).toAdd.1 = 0
          simp⟩
      invFun := fun v => Multiplicative.ofAdd (eQ v).toAdd.2
      left_inv := by
        intro a
        simp
      right_inv := by
        intro v
        apply Subtype.ext
        apply eQ.injective
        simp only [eQ.apply_symm_apply]
        apply Multiplicative.ofAdd.injective
        exact Prod.ext v.property.symm rfl }
  have hcenterCard :
      Nat.card (Subgroup.center P) = Nat.card (Multiplicative F) :=
    Nat.card_congr eZ.toEquiv
  have hUcard : Nat.card U = Nat.card (Subgroup.center P) :=
    (Nat.card_congr axisU).symm.trans hcenterCard.symm
  have hVcard : Nat.card V = Nat.card (Subgroup.center P) :=
    (Nat.card_congr axisV).symm.trans hcenterCard.symm
  have hUVinf : U ⊓ V = ⊥ := by
    apply le_antisymm
    · intro q hq
      rw [Subgroup.mem_bot]
      have hqU := hq.1
      have hqV := hq.2
      change (eQ q).toAdd.2 = 0 at hqU
      change (eQ q).toAdd.1 = 0 at hqV
      apply eQ.injective
      apply Multiplicative.toAdd.injective
      apply Prod.ext
      · simpa using hqV
      · simpa using hqU
    · exact bot_le
  have hUVsup : U ⊔ V = ⊤ := by
    apply top_unique
    intro q _hq
    let u : P ⧸ Subgroup.center P :=
      eQ.symm (Multiplicative.ofAdd ((eQ q).toAdd.1, 0))
    let v : P ⧸ Subgroup.center P :=
      eQ.symm (Multiplicative.ofAdd (0, (eQ q).toAdd.2))
    have hu : u ∈ U := by
      change (eQ u).toAdd.2 = 0
      simp [u]
    have hv : v ∈ V := by
      change (eQ v).toAdd.1 = 0
      simp [v]
    have huv : u * v = q := by
      apply eQ.injective
      rw [map_mul]
      rw [show eQ u = Multiplicative.ofAdd ((eQ q).toAdd.1, 0) by simp [u],
        show eQ v = Multiplicative.ofAdd (0, (eQ q).toAdd.2) by simp [v],
        ← ofAdd_toAdd (eQ q)]
      apply congrArg Multiplicative.ofAdd
      apply Prod.ext <;> simp
    rw [← huv]
    exact Subgroup.mul_mem_sup hu hv
  have heUV (k : K) (u : U) :
      ((eUV ⟨k • (u : P ⧸ Subgroup.center P),
          (hU k (u : P ⧸ Subgroup.center P)).mp u.property⟩ : V) :
          P ⧸ Subgroup.center P) =
        k • ((eUV u : V) : P ⧸ Subgroup.center P) := by
    apply eQ.injective
    apply Multiplicative.ofAdd.injective
    change (eQ (swapQ (k • (u : P ⧸ Subgroup.center P)))).toAdd =
      (eQ (k • swapQ (u : P ⧸ Subgroup.center P))).toAdd
    simp [swapQ, swapMul, heQ_action]
  exact ⟨quotientAction, U, V, hU, hV, eUV,
    hquotientAction_mk, hUcard, hVcard, hUVinf, hUVsup, heUV⟩

/-- Higman's isomorphic-summand criterion with the acting Type-B branch kept
explicit.  No group-only Type-B equivalence is asserted. -/
public theorem theorem1_typeB_actor_iff_isomorphic_summands
    {K P : Type u} [Group K] [Group P] [MulDistribMulAction K P]
    (hP : IsSuzukiTwoGroup P)
    (hKcyclic : IsCyclic K) (hKfaithful : FaithfulSMul K P)
    (hKregular : ActionRegularOn K P (involutions P)) :
    (∃ (B : Subgroup P) (actor : K),
      Lemma12TypeBActorBranchData K P actor B) ↔
      Theorem1IsomorphicSummands K P :=
  ⟨theorem1_isomorphic_summands_of_typeB_actor
      hP hKcyclic hKfaithful hKregular,
    theorem1_typeB_actor_of_isomorphic_summands
      hP hKcyclic hKfaithful hKregular⟩
end Higman
end External
end BenderSuzuki
