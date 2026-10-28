module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelOrbit.Orbit
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction.ModelResidual
public import Theory.GroupTheory.NoncentralChiefRefinement.CentralQuotient
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Chief factors of the native HS centralizer residual

The alternating preimage in the actual centralizer `(D₈ * D₈ * 4).S₅`
is its two-residual. Its pair kernel has cyclic center, fixed pointwise by
the residual. Multiplication by that center turns every noncentral element
into one of order four. The proved conjugation orbit on those elements
therefore makes the kernel modulo its center a chief factor.

Refine the central part, append this single chief factor, and refine the
terminal A₅ quotient. The first and last parts contribute zero noncentral
two-chief factors. Equivariant Jordan–Hölder gives the bound for every
complete series of the actual residual.

Source: Aschbacher–Smith 14.7.68(2), printed p.1071 / PDF p.1088;
1.1.5(3)(f), printed pp.502–503; GLS3 Table 5.3m. The concrete orbit
calculation is the one used for Aschbacher–Smith I.2.2(5).
-/

public section
noncomputable section
open Subgroup NoncentralChiefRefinement
open scoped commutatorElement
open Sporadic.LeechRelated.HS Sporadic.LeechRelated.HS.EvenLocalCandidates
open Sporadic.LeechRelated.HS.EvenLocalCandidates.CentralInvolutionCore
open CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.HSInner.CoreStructure
open CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.HSLocal.CentralizerRestriction
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.SporadicSieve.HSNative

private def coreInclusion : core →* modelResidual := inclusion model_core_le_residual

private def coreCenter : Subgroup modelResidual := (center core).map coreInclusion

private theorem coreCenter_le_center : coreCenter ≤ center modelResidual := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_center_iff]
  intro g
  apply Subtype.ext
  exact mul_inv_eq_iff_eq_mul.mp (modelResidual_fixes_center g z hz)

private instance : coreCenter.Normal where
  conj_mem x hx g := by
    have h := mem_center_iff.mp (coreCenter_le_center hx) g
    simpa only [h, mul_inv_cancel_right] using hx

private def Z : NormalNode modelResidual := ⟨coreCenter, inferInstanceAs coreCenter.Normal⟩
private def Q : NormalNode modelResidual := ⟨core.subgroupOf modelResidual, inferInstanceAs (core.subgroupOf modelResidual).Normal⟩

private theorem coreCenter_le_core : Z ≤ Q := by
  rintro _ ⟨z, _, rfl⟩
  exact z.property

private theorem mem_coreCenter (x : core) : coreInclusion x ∈ coreCenter ↔ x ∈ center core :=
  mem_map_iff_mem (inclusion_injective model_core_le_residual)

private theorem orderFour_translate (x : core) :
    ∃ z : core, z ∈ center core ∧ orderOf (x * z) = 4 := by
  rcases model_core_square x with hx | hx
  · refine ⟨cyclicGenerator, cyclicGenerator_mem_center, (model_core_order_four_iff _).mpr ?_⟩
    rw [(show Commute x cyclicGenerator from
      mem_center_iff.mp cyclicGenerator_mem_center x).mul_pow, hx, one_mul,
      cyclicGenerator_square]
  · exact ⟨1, one_mem _, by simpa using (model_core_order_four_iff x).mpr hx⟩

private theorem core_chief : Z ⋖ Q := by
  apply (covBy_iff_isChief Z Q).mpr
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · refine lt_of_le_of_ne coreCenter_le_core ?_
    intro he
    apply model_leftI_noncentral
    apply (mem_coreCenter leftI).mp
    rw [show coreCenter = core.subgroupOf modelResidual from he]
    exact leftI.property
  · intro N hN hZN hNQ
    let : N.Normal := hN
    by_cases hNZ : N ≤ coreCenter
    · exact Or.inl (le_antisymm hNZ hZN)
    · right
      obtain ⟨a, ha, haZ⟩ := SetLike.not_le_iff_exists.mp hNZ
      let x : core := ⟨a.val, hNQ ha⟩
      have hx : coreInclusion x = a := rfl
      have hxZ : x ∉ center core := fun h => haZ (hx ▸ (mem_coreCenter x).mpr h)
      obtain ⟨z, hz, hx4⟩ := orderFour_translate x
      have hxzZ : x * z ∉ center core := by
        intro h
        exact hxZ ((mul_mem_cancel_right hz).mp h)
      have hxzN : coreInclusion (x * z) ∈ N := by
        rw [map_mul, hx]
        exact N.mul_mem ha (hZN ((mem_coreCenter z).mpr hz))
      apply le_antisymm hNQ
      intro b hb
      let y : core := ⟨b.val, hb⟩
      have hy : coreInclusion y = b := rfl
      by_cases hyZ : y ∈ center core
      · exact hy ▸ hZN ((mem_coreCenter y).mpr hyZ)
      · obtain ⟨w, hw, hy4⟩ := orderFour_translate y
        have hywZ : y * w ∉ center core := by
          intro h
          exact hyZ ((mul_mem_cancel_right hw).mp h)
        obtain ⟨g, hg⟩ := modelResidual_orderFour_transitive (x * z) (y * w)
          hxzZ hywZ hx4 hy4
        have hywN : coreInclusion (y * w) ∈ N := by
          have hh := hN.conj_mem (coreInclusion (x * z)) hxzN g
          have he : g * coreInclusion (x * z) * g⁻¹ = coreInclusion (y * w) :=
            Subtype.ext hg
          exact he ▸ hh
        rw [map_mul] at hywN
        exact hy ▸ (mul_mem_cancel_right (hZN ((mem_coreCenter w).mpr hw))).mp hywN
private theorem noTwoChief_of_simple_perfect (H : Type*) [Group H] [Finite H]
    [IsSimpleGroup H] [Group.IsPerfect H] : HasNoTwoChiefFactors H := by
  intro A B hAB hp
  rcases B.property.eq_bot_or_eq_top with hB | hB
  · have hB' : B = ⊥ := Subtype.ext hB
    exact hAB.lt.not_ge (by rw [hB']; exact bot_le)
  · have : Group.IsPerfect B.val := by rw [hB]; infer_instance
    let : Nontrivial (Section A B) := (covBy_iff_isChief A B).mp hAB |>.quotient_nontrivial _ _
    let : Group.IsNilpotent (Section A B) := hp.isNilpotent
    exact Group.IsPerfect.not_isSolvable (Section A B) inferInstance

private theorem terminal_noTwo : HasNoTwoChiefFactors (modelResidual ⧸ Q.val) := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (modelResidual ⧸ Q.val) := modelResidualQuotient.isSimpleGroup
  exact noTwoChief_of_simple_perfect _

/-- The actual alternating preimage has at most one noncentral two-chief factor
in every complete chief series. Its core modulo its center is chief by the
literal conjugation orbit; its terminal quotient is the actual A₅ quotient. -/
theorem modelResidual_noncentralTwoCount_le (s : ChiefSeries modelResidual)
    (hs0 : s.head = ⊥) (hs1 : s.last = ⊤) : s.noncentralTwoCount ≤ 1 := by
  obtain ⟨a, ha0, ha1⟩ := exists_chiefSeries (⊥ : NormalNode modelResidual) Z bot_le
  let b : ChiefSeries modelResidual := (RelSeries.singleton _ Z).snoc Q core_chief
  obtain ⟨c, hc0, hc1⟩ := exists_chiefSeries Q (⊤ : NormalNode modelResidual) le_top
  have hab : a.last = b.head := ha1
  have hbc : (a.smash b hab).last = c.head :=
    (RelSeries.last_smash hab).trans
      ((RelSeries.last_snoc (RelSeries.singleton _ Z) Q core_chief).trans hc0.symm)
  have ha : a.noncentralTwoCount = 0 := by
    apply a.noncentralTwoCount_eq_zero_of_central
    rw [ha0, ha1, isCentral_iff_commutator_le, commutator_le]
    intro x _ y hy
    change ⁅x, y⁆ = 1
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact mem_center_iff.mp (coreCenter_le_center hy) x
  have hb : b.noncentralTwoCount ≤ 1 := by
    change Nat.card {i : Fin 1 // IsNoncentralTwo (b i.castSucc) (b i.succ)} ≤ 1
    simpa using Nat.card_le_card_of_injective
      (fun i : {i : Fin 1 // IsNoncentralTwo (b i.castSucc) (b i.succ)} => i.val)
      Subtype.val_injective
  have hc : c.noncentralTwoCount = 0 :=
    c.noncentralTwoCount_eq_zero_of_quotient Q hc0.ge terminal_noTwo
  have he := s.noncentralTwoCount_eq ((a.smash b hab).smash c hbc)
    (by simpa only [RelSeries.head_smash] using hs0.trans ha0.symm)
    (by simpa only [RelSeries.last_smash] using hs1.trans hc1.symm)
  rw [he, ChiefSeries.noncentralTwoCount_smash, ChiefSeries.noncentralTwoCount_smash,
    ha, hc, zero_add, add_zero]
  exact hb

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.SporadicSieve.HSNative
