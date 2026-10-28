module

public import Stellmacher.Recognition.LargeTerminalResidualNormal
public import Stellmacher.Recognition.Parrott.CentralizerStructure
public import Theory.GroupAction.NormalFiveTwentyBound
public import Theory.GroupTheory.FrobeniusTwentyRecognition
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.GroupTheory.ClassThreeNoFifteen

/-!
# Parrott's actual centralizer hypotheses in the Sylow-2048 branch

A retained large terminal context whose prescribed ambient Sylow has order
2048 supplies an involution generating its omega-center and satisfying
ParrottCentralizerHypotheses. In particular, the quotient of the full
involution centralizer by its two-core is an actual faithful C5 semidirect
C4 model. The original Sylow-five subgroup has central fixed subgroup in
that same full two-core.

The established core/Sylow-five packet gives core order512, class at least
three, and an actual order-five action. Its intrinsic structure gives
class3, center2 and derived=Frattini of order32. The first residual's normal
image gives a five-core of order5 in the full centralizer quotient.
Characteristic two identifies the kernel of the canonical Frattini action
with the two-core, so this quotient acts faithfully on sixteen elements.
The nonzero invariant third commutator excludes order15 in that action.
The normal-five action bound then makes the quotient order divide20.

The actual ambient Sylow lies in the involution centralizer, and its order
2048 divided by the core order512 forces four-divisibility of the quotient.
Its odd core therefore has order5. Solvability, the trivial quotient
two-core, and the existing Frobenius-twenty recognition theorem give the
required concrete model. The final record retains the original involution
and genuine Sylow-five subgroup; no equality with a local vertex is used.

Source: Stellmacher (10.1)(18)--(20), retaining the rich Section Ten context,
and D. Parrott, A characterization of the Tits' simple group (1972),
original involution-centralizer hypotheses and Lemma1, printed p.672.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix Subgroup
universe u

/-- The prescribed Sylow-2048 context supplies the original full-centralizer
hypotheses of Parrott, with its involution in the prescribed omega-center. -/
public theorem LargeTerminalContext.parrott_hypotheses_of_sylow_card
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) (hS : Nat.card S0 = 2048) :
    ∃ z : G, zpowers z = omegaOneCenter (S0 : Subgroup G) ∧
      ParrottCentralizerHypotheses z := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨z, hz, hgen, _, hJcard, hclass, hVcard, P, hPcard, hPfixed⟩ :=
    ctx.exists_sylow_five_fixed_center_of_card hS
  let C := centralizer ({z} : Set G)
  let J := pCore 2 C
  let Q := C ⧸ J
  let V := J ⧸ frattini J
  have hC : C = centralizer (omegaOneCenter (S0 : Subgroup G) : Set G) := by
    change centralizer ({z} : Set G) = _
    rw [← centralizer_closure, ← zpowers_eq_closure, hgen]
  have hQfive : Nat.card (pCore 5 Q) = 5 := by
    obtain ⟨w, _, hw, _, _, hc⟩ := ctx.first_residual_normal_of_card hS
    rw [← centralizer_closure, ← zpowers_eq_closure, hw, ← hC] at hc
    exact hc
  obtain ⟨hsolv, hchar⟩ := ctx.localStructure C
    (Theory.GroupTheory.isTwoLocal_involution_centralizer hz)
  let _ : Group.IsSolvable C := hsolv
  let _ : MulDistribMulAction P J :=
    conjMulDistribMulActionOfLeNormalizer (P : Subgroup C) J
      (le_normalizer_of_normal (H := J))
  have hfixed : FixedPoints.subgroup P J ≤ center J := by
    intro j hj
    apply hPfixed
    change (j : C) ∈ centralizer (P : Set C)
    rw [mem_centralizer_iff]
    intro p hp
    have h := congrArg Subtype.val (hj ⟨p, hp⟩)
    change p * (j : C) * p⁻¹ = (j : C) at h
    exact mul_inv_eq_iff_eq_mul.mp h
  obtain ⟨hclass3, hZ, hPhi, _, _, hD⟩ := Theory.GroupAction.parrott_twoGroup_structure
    (pCore_isPGroup (p := 2) (G := C)) hJcard hclass hPcard hfixed
  let action : C →* MulAut V := (quotientAut (frattini J)).comp
    (MulAut.conjNormal : C →* MulAut J)
  have hker : action.ker = J := pCore_frattini_action_kernel 2 hchar
  let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange action)
  let ρ : Q →* MulAut V := action.range.subtype.comp e.toMonoidHom
  have hρ : Function.Injective ρ := action.range.subtype_injective.comp e.injective
  have hρmk (c : C) : ρ (QuotientGroup.mk' J c) = action c := rfl
  have hno : ∀ q : Q, orderOf q ≠ 15 := by
    intro q hq
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective J q
    have ho := orderOf_injective ρ hρ (QuotientGroup.mk' J c)
    rw [hρmk, hq] at ho
    exact ThirdCommutator.frattini_action_order_ne_fifteen
      (pCore_isPGroup (p := 2) (G := C)) hJcard hclass3 hZ hPhi hD
      (MulAut.conjNormal c) ho
  have hbound : Nat.card Q ∣ 20 :=
    (normal_five_centralizer_and_card_bound ρ hρ (pCore 5 Q) hQfive hVcard hno).2
  have hSC : (S0 : Subgroup G) ≤ C := by
    rw [hC]
    exact le_centralizer_iff.mpr ((omegaOneCenter_le_centerAmbient _).trans
      (centerAmbient_le_centralizer _))
  have hSdiv : 2048 ∣ Nat.card C := by
    have h := ((S0 : Subgroup G).subgroupOf C).card_subgroup_dvd_card
    rwa [Nat.card_congr (subgroupOfEquivOfLe hSC).toEquiv, hS] at h
  have hfour : 4 ∣ Nat.card Q := by
    have hcount := J.card_mul_index
    rw [hJcard] at hcount
    change 512 * Nat.card Q = Nat.card C at hcount
    rw [← hcount] at hSdiv
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 512) hSdiv
  have hcoreQ : pCore 2 Q = ⊥ := by
    have h := pCore_map_mk'_eq_of_normal_isPGroup (G := C) (p := 2) J pCore_isPGroup
    have hbot : J.map (QuotientGroup.mk' J) = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [QuotientGroup.ker_mk']
    exact h.symm.trans hbot
  have hfiveOdd : pCore 5 Q ≤ pPrimeCore 2 Q :=
    le_sSup ⟨inferInstance, by rw [hQfive]; decide⟩
  have hodddiv : Nat.card (pPrimeCore 2 Q) ∣ 20 :=
    (pPrimeCore 2 Q).card_subgroup_dvd_card.trans hbound
  have hodd5 : Nat.card (pPrimeCore 2 Q) ∣ 5 :=
    ((pPrimeCore_coprime_card (p := 2) (G := Q)).symm.pow_right 2).dvd_of_dvd_mul_left hodddiv
  have hoddcard : Nat.card (pPrimeCore 2 Q) = 5 := by
    have hlo := card_le_of_le hfiveOdd
    rw [hQfive] at hlo
    exact le_antisymm (Nat.le_of_dvd (by decide) hodd5) hlo
  have hQsolv : Group.IsSolvable Q :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective J)
  have hmodel := exists_faithful_c5_semidirect_c4_of_odd_core_card_five
    hQsolv hcoreQ hoddcard hfour
  exact ⟨z, hgen, hz, hJcard, hclass, hmodel, P, hPfixed⟩

end Stellmacher.Recognition
