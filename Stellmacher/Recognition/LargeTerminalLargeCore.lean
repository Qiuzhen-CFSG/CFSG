module

public import Stellmacher.Recognition.LargeTerminalResidualNormal
public import Stellmacher.Recognition.LargeTerminalLocalCharacterData
public import Theory.GroupAction.NormalFiveTwentyBound
public import Theory.GroupTheory.ClassThreeNoFifteen
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# The full involution-centralizer core at the upper large terminal endpoint

At Sylow order 4096, the full centralizer of the omega-central involution
has the second local core, of order 1024, as its two-core. The existing
containments leave only the residual of order 512 or that larger core.

The smaller possibility would give the same faithful four-dimensional
Frattini action and normal subgroup of order five as in the order 2048
branch. Its quotient order then divides 20. But the ambient Sylow order 4096
and core order 512 force that quotient order to be divisible by 8, a
contradiction. This removes the smaller-core alternative without assuming
ambient fusion or a recognition theorem.

Source: Stellmacher (10.1)(18)--(20), the intrinsic two-group calculation
of Parrott, A characterization of the Tits' simple group (1972), Lemma 1,
and the existing normal-five action bound.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven CosetGraphContext SevenSix Subgroup

universe u

private theorem residual_core_impossible
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) (hS : Nat.card S0 = 4096)
    (hcore : ∃ z : G, orderOf z = 2 ∧ zpowers z = omegaOneCenter (S0 : Subgroup G) ∧
      twoCoreIn (centralizer ({z} : Set G)) = ctx.firstResidual) : False := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨z, hz, hgen, _, hJcard, hclass, hVcard, P, hPcard, hPfixed⟩ :=
    ctx.exists_sylow_five_fixed_center_of_core_eq hcore
  let C := centralizer ({z} : Set G)
  let J := pCore 2 C
  let Q := C ⧸ J
  let V := J ⧸ frattini J
  have hC : C = centralizer (omegaOneCenter (S0 : Subgroup G) : Set G) := by
    change centralizer ({z} : Set G) = _
    rw [← centralizer_closure, ← zpowers_eq_closure, hgen]
  have hQfive : Nat.card (pCore 5 Q) = 5 := by
    obtain ⟨w, _, hw, _, _, hc⟩ := ctx.first_residual_normal_of_core_eq hcore
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
  have hSdiv : 4096 ∣ Nat.card C := by
    have h := ((S0 : Subgroup G).subgroupOf C).card_subgroup_dvd_card
    rwa [Nat.card_congr (subgroupOfEquivOfLe hSC).toEquiv, hS] at h
  have height : 8 ∣ Nat.card Q := by
    have hcount := J.card_mul_index
    rw [hJcard] at hcount
    change 512 * Nat.card Q = Nat.card C at hcount
    rw [← hcount] at hSdiv
    exact Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 512) hSdiv
  have hbad : 8 ∣ 20 := height.trans hbound
  norm_num at hbad

/-- At Sylow order 4096 the full centralizer core is the larger local core;
it cannot be the order 512 first residual. -/
public theorem LargeTerminalContext.involution_centralizer_core_eq_of_large_card
    {G : Type u} [Group G] [Finite G] {S0 : Sylow 2 G}
    (ctx : LargeTerminalContext S0) (hS : Nat.card S0 = 4096) :
    ∃ z : G, orderOf z = 2 ∧ zpowers z = omegaOneCenter (S0 : Subgroup G) ∧
      twoCoreIn (centralizer ({z} : Set G)) = twoCoreIn ctx.second ∧
      Nat.card (pCore 2 (centralizer ({z} : Set G))) = 1024 := by
  obtain ⟨z, hz, hgen, hlow, hhigh, _⟩ := ctx.involution_centralizer_core
  let J := twoCoreIn (centralizer ({z} : Set G))
  let Q := twoCoreIn ctx.second
  have hSP : (S0 : Subgroup G) ≤ ctx.second :=
    ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
  have hQS : Q ≤ (S0 : Subgroup G) := by
    rintro x ⟨q, hq, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
      (S0.subtype hSP) hq
  have hQcard : Nat.card Q = 1024 := by
    have h := ctx.local_character_core_card hS
    rw [Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv] at h
    exact h
  have hJlow : 512 ≤ Nat.card J := by
    have h := card_le_of_le hlow
    rwa [ctx.first_residual_structure.1] at h
  have hJdiv : Nat.card J ∣ 1024 := hQcard ▸ card_dvd_of_le hhigh
  obtain ⟨k, hk⟩ := hJdiv
  have hkpos : 0 < k := by nlinarith
  have hkle : k ≤ 2 := by nlinarith
  have hcard : Nat.card J = 512 ∨ Nat.card J = 1024 := by
    interval_cases k <;> omega
  have hJcard : Nat.card J = 1024 := by
    rcases hcard with hJ | hJ
    · have heq : J = ctx.firstResidual :=
        (eq_of_le_of_card_ge hlow
          (by rw [ctx.first_residual_structure.1]; exact hJ.le)).symm
      exact (residual_core_impossible ctx hS ⟨z, hz, hgen, heq⟩).elim
    · exact hJ
  have hJQ : J = Q := eq_of_le_of_card_ge hhigh (by rw [hQcard, hJcard])
  refine ⟨z, hz, hgen, hJQ, ?_⟩
  exact (card_map_of_injective
    (centralizer ({z} : Set G)).subtype_injective).symm.trans hJcard

end Stellmacher.Recognition
