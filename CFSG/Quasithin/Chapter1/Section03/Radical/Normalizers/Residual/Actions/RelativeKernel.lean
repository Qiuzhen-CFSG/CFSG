module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Residual.Actions.Transfer
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.Actions.Nilpotent.Quotient
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Comparing the relative kernels of two radical actions

For two distinct odd Fitting primes, the nonsimple A.3.6 component is in
its nilpotent alternative. Its order is 120 times its odd Fitting order.
The quaternion subgroup in an omega Frattini action image forces that action's
normal kernel to have odd order, hence to lie in the Fitting subgroup.
The Fitting subgroup fixes every relevant omega Frattini quotient: distinct
prime cores commute, and a core's own action is trivial when that core is
abelian or has exponent equal to its prime. This retains the omega subgroup
for homocyclic cores of higher exponent.

The actual radical quotient and component equivalences transport the kernel
comparison to L. The section centralizer inside L kills the defining prime's
action, so it also kills the other prime's action. No claim about the entire
section centralizer in LT, residual irreducibility, or containment in the
normalizer residual is needed.

The universal quaternion-image theorem is an explicit earlier model input;
the residual-actions assembly owns its discharge. The full A.3.6 implication
is used with the genuine local component and quotient hypotheses.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6,
printed pp.43–45, and the proof of Proposition 1.3.8, pp.512–513.
-/

open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.Section02.LocalModels
open CFSG.Quasithin.Chapter1.RadicalActions
open CFSG.Quasithin.ChapterA.Section04

namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.RelativeKernel

private theorem card_eq_of_nilpotent
    {K : Type*} [Group K] [Finite K] (hn : A36Nilpotent K) :
    Nat.card K = 120 * Nat.card (fittingSubgroup K) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hn.2.2.1
  have hquot : Nat.card (K ⧸ generalizedFitting K) = 120 := by
    rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two, hF]
    norm_num
  rw [card_eq_card_quotient_mul_card_subgroup (generalizedFitting K), hquot, hn.1]

/-- A quaternion subgroup of an action image exhausts the two-part of the
nilpotent A.3.6 component. Its normal kernel therefore lies in the odd core. -/
private theorem ker_le_fitting_of_quaternion_image
    {K A : Type*} [Group K] [Finite K] [Group A]
    (hn : A36Nilpotent K) (hc : A36Common K) (f : K →* A)
    (hQ : ∃ e : QuaternionGroup 2 →* f.range, Function.Injective e) :
    f.ker ≤ fittingSubgroup K := by
  have h8 : 8 ∣ Nat.card f.range := by
    obtain ⟨e, he⟩ := hQ
    simpa only [Nat.card_eq_fintype_card, QuaternionGroup.card] using
      card_dvd_of_injective e he
  have hcard := card_eq_of_nilpotent hn
  have hmul : Nat.card f.range * Nat.card f.ker = Nat.card K := by
    rw [← index_ker]
    exact f.ker.index_mul_card
  have hcop : Nat.Coprime 2 (Nat.card (fittingSubgroup K)) := by
    rw [hc.1]
    exact pPrimeCore_coprime_card
  have hk : Nat.Coprime 2 (Nat.card f.ker) := by
    apply Nat.prime_two.coprime_iff_not_dvd.mpr
    intro hd
    have h16 : 8 * 2 ∣ 8 * (15 * Nat.card (fittingSubgroup K)) := by
      have hh := Nat.mul_dvd_mul h8 hd
      rw [hmul, hcard] at hh
      convert hh using 1
      ring
    have h2 := (Nat.mul_dvd_mul_iff_left (by decide : 0 < 8)).mp h16
    exact (Nat.prime_two.coprime_iff_not_dvd.mp
      ((by decide : Nat.Coprime 2 15).mul_right hcop)) h2
  rw [hc.1]
  exact le_sSup ⟨inferInstance, hk⟩

private theorem fitting_card_dvd_of_equiv
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B] (e : A ≃* B) :
    Nat.card (fittingSubgroup A) ∣ Nat.card (fittingSubgroup B) := by
  have hle : (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    rintro N ⟨hN, hnil⟩
    apply map_le_iff_le_comap.mp
    let := hnil
    exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩
  rw [Nat.card_congr (e.subgroupMap (fittingSubgroup A)).toEquiv]
  exact card_dvd_of_le hle

private theorem nilpotent_of_distinct_fitting_primes
    {E : Type*} [Group E] [Finite E] {C : Subgroup E}
    (h : A36Conclusion C) (hn : ¬ IsQuasisimple C)
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hne : p ≠ q)
    (hp : p ∣ Nat.card (fittingSubgroup C))
    (hq : q ∣ Nat.card (fittingSubgroup C)) : A36Nilpotent C := by
  rcases RadicalStructure.nonsimple_radical h hn with hnat | hnil
  · obtain ⟨hfit, r, hr, _, ha⟩ := hnat
    obtain ⟨_, hc⟩ := RadicalStructure.natural_elementary ha
    have hpr : p = r := (Nat.prime_dvd_prime_iff_eq Fact.out hr).mp
      ((Fact.out : p.Prime).dvd_of_dvd_pow (show p ∣ r ^ 2 by
        simpa only [← hfit, hc] using hp))
    have hqr : q = r := (Nat.prime_dvd_prime_iff_eq Fact.out hr).mp
      ((Fact.out : q.Prime).dvd_of_dvd_pow (show q ∣ r ^ 2 by
        simpa only [← hfit, hc] using hq))
    exact (hne (hpr.trans hqr.symm)).elim
  · exact hnil

private theorem quaternion_image_of_restriction
    {K A : Type*} [Group K] [Group A] (f : K →* A) (S : Subgroup K)
    (hQ : ∃ e : QuaternionGroup 2 →* (f.comp S.subtype).range, Function.Injective e) :
    ∃ e : QuaternionGroup 2 →* f.range, Function.Injective e := by
  obtain ⟨e, he⟩ := hQ
  have hle : (f.comp S.subtype).range ≤ f.range := by
    rintro a ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  exact ⟨(inclusion hle).comp e, (inclusion_injective hle).comp he⟩

private theorem xiAction_ker_iff_omegaAction_ker
    {G C : Type*} [Group G] [Finite G] [Group C]
    (L : Subgroup G) (e : XiQuotient L ≃* C)
    {r : ℕ} [Fact r.Prime] (ho : Odd r) (l : L) :
    l ∈ (xiFrattiniAction L (XiP r L) (XiP_invariant r L.le_normalizer)).ker ↔
      e (QuotientGroup.mk' _ l) ∈ (omegaFrattiniAction r C).ker := by
  let a := (xiPFrattiniEquivCore ho L).trans (omegaFrattiniEquiv r e)
  have he (x : XiFrattiniQuotient (XiP r L)) :
      a (xiFrattiniAction L (XiP r L) (XiP_invariant r L.le_normalizer) l x) =
        omegaFrattiniAction r C (e (QuotientGroup.mk' _ l)) (a x) := by
    change omegaFrattiniEquiv r e (xiPFrattiniEquivCore ho L
      (xiFrattiniAction L (XiP r L) (XiP_invariant r L.le_normalizer) l x)) = _
    rw [xiPFrattiniEquivCore_equivariant, omegaFrattiniEquiv_equivariant]
    rfl
  change _ = 1 ↔ _ = 1
  constructor
  · intro h
    apply MulEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := a.surjective x
    rw [← he, h]
    rfl
  · intro h
    apply MulEquiv.ext
    intro x
    apply a.injective
    rw [he, h]
    rfl

end CFSG.Quasithin.Chapter1.RadicalNormalizers.RelativeKernel

namespace CFSG.Quasithin.Chapter1.RadicalNormalizers
open RelativeKernel
universe u

/-- The section centralizer inside L kills every other odd radical Frattini
action. The sole additional model input is the nilpotent quaternion-image
theorem; no action kernel, residual action, or radical containment is assumed. -/
public theorem sectionCentralizer_le_cross_frattiniAction_ker_of_A36
    {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Conclusion C)
    (hQuaternion : ∀ (E : Type u) [Group E] [Finite E],
      IsSQTK 𝒦 E → pCore 2 E = ⊥ → ∀ C : Subgroup E,
      C.IsCComponent → A36Nilpotent C → A36Common C →
      ∀ (r : ℕ) [Fact r.Prime], Odd r → r ∣ Nat.card (fittingSubgroup C) →
      ∀ S : Sylow 2 C, ∃ e : QuaternionGroup 2 →*
        ((omegaFrattiniAction r C).comp (S : Subgroup C).subtype).range,
        Function.Injective e)
    {L T : Subgroup G} (hL : L ∈ CFSG.Quasithin.Chapter1.L G T)
    (hQ : IsSQTK 𝒦 ((L ⊔ T : Subgroup G) ⧸ pCore 2 (L ⊔ T : Subgroup G)))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (hT : T ≤ normalizer (L : Set G))
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hp : Odd p) (hq : Odd q)
    (hne : p ≠ q)
    (hdp : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (hdq : q ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    (twoSectionCentralizer (XiP p L) (L ⊔ T)).subgroupOf L ≤
      (xiFrattiniAction L (XiP q L) (XiP_invariant q L.le_normalizer)).ker := by
  let C := radicalLocalImage T L
  let e : XiQuotient L ≃* C := radicalLocalQuotientEquiv hL
  have ha : A36Conclusion C := proposition_1_2_1_four_earlier_conclusion hA36 hQ hL.1
  have hnC : ¬ IsQuasisimple C := by
    intro hc
    let := hc
    exact hn (IsQuasisimple.of_mulEquiv e.symm)
  have hpC : p ∣ Nat.card (fittingSubgroup C) :=
    hdp.trans (fitting_card_dvd_of_equiv e)
  have hqC : q ∣ Nat.card (fittingSubgroup C) :=
    hdq.trans (fitting_card_dvd_of_equiv e)
  have hnil : A36Nilpotent C := nilpotent_of_distinct_fitting_primes ha hnC hne hpC hqC
  have hC : C.IsCComponent := by
    let := pCore_isNilpotent (p := 2) (G := (L ⊔ T : Subgroup G))
    exact hL.1.map_quotient _
  let S : Sylow 2 C := Classical.arbitrary _
  have hi := hQuaternion _ hQ (pCore_quotient_pCore_eq_bot 2) C hC hnil ha.2 p hp hpC S
  have hker : (omegaFrattiniAction p C).ker ≤ (omegaFrattiniAction q C).ker :=
    (ker_le_fitting_of_quaternion_image hnil ha.2 _
      (quaternion_image_of_restriction _ _ hi)).trans
        (RadicalActions.Nilpotent.fitting_le_action_ker hnil hqC)
  intro l hl
  apply (xiAction_ker_iff_omegaAction_ker L e hq l).mpr
  apply hker
  apply (xiAction_ker_iff_omegaAction_ker L e hp l).mp
  exact sectionCentralizer_le_L_frattiniAction_ker p L T hT hl

end CFSG.Quasithin.Chapter1.RadicalNormalizers
