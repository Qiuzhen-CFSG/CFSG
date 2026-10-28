module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.Source
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.SpecificGroups.Alternating.TwoThreeCycles

/-!
# The A₆ component normality reduction

An ordinary nonnormal component has central quotient of three-rank at most
one. The actual A₆ quotient (including its possible central three-cover)
has three-rank at least two, so it cannot be nonnormal. This preserves the
literal quotient and works before choosing a representation module.

Source: Aschbacher--Smith A.3.8(3), pp.45--46, together with the
A₆ three-rank obstruction used in 13.3.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource.FourModels
open CFSG.Quasithin.Chapter1.Section02.LocalModels
universe u
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

private theorem a6_quasisimple : IsQuasisimple (alternatingGroup (Fin 6)) where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

omit [Finite Q] in
theorem alternatingSix_or_cover_structure
    (hm : IsAlternating Q 6 ∨ IsAlternatingCover Q 6) :
    IsQuasisimple Q ∧ Nat.card (center Q) ≤ 3 ∧
      Nonempty ((Q ⧸ center Q) ≃* alternatingGroup (Fin 6)) := by
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    let : IsQuasisimple (alternatingGroup (Fin 6)) := a6_quasisimple
    have hz : center Q = ⊥ := by
      apply eq_bot_iff.mpr
      intro z hz
      have he := (centerCongr e ⟨z,hz⟩).property
      change e z ∈ center (alternatingGroup (Fin 6)) at he
      rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
      exact e.map_eq_one_iff.mp he
    exact ⟨IsQuasisimple.of_mulEquiv e.symm,by simp [hz],
      ⟨(QuotientGroup.quotientMulEquivOfEq hz).trans
        (QuotientGroup.quotientBot.trans e)⟩⟩
  · obtain ⟨hq,⟨ez⟩,he⟩ := hm
    exact ⟨hq,by rw [Nat.card_congr ez.toEquiv]; norm_num,he⟩

theorem component_normal_of_six_core_quotient {K : Subgroup G}
    (hK : K.IsCComponent) (hr : primeRank 3 G ≤ 2)
    (hm : IsAlternating (K ⧸ pCore 2 K) 6 ∨ IsAlternatingCover (K ⧸ pCore 2 K) 6) :
    K.Normal := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  let D := K.map (QuotientGroup.mk' (pCore 2 G))
  let e : D ≃* K ⧸ pCore 2 K := (cComponentTwoCoreQuotientEquiv hK).symm
  obtain ⟨hq,hz,⟨eq⟩⟩ := alternatingSix_or_cover_structure hm
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
  have hD : IsComponent (G ⧸ pCore 2 G) D :=
    ⟨hK.subnormal.quotient,inferInstance⟩
  have hzD : Nat.card (center D) ≤ 3 := by
    rw [Nat.card_congr (centerCongr e).toEquiv]
    exact hz
  let ec : (D ⧸ center D) ≃* ((K ⧸ pCore 2 K) ⧸ center (K ⧸ pCore 2 K)) :=
    QuotientGroup.congr _ _ e (by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        exact (centerCongr e ⟨x,hx⟩).property
      · intro x hx
        exact ⟨e.symm x,(centerCongr e).symm ⟨x,hx⟩ |>.property,e.apply_symm_apply x⟩)
  have hrQ : primeRank 3 (G ⧸ pCore 2 G) ≤ 2 := by
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 G) pCore_isPGroup]
    exact hr
  have hn : D.Normal := by
    by_contra hn
    have hlow := (nonnormal_component_three_rank hrQ hD hzD hn).2
    rw [primeRank_congr 3 (ec.trans eq)] at hlow
    have hh := alternatingGroup.TwoThreeCycles.two_le_primeRank (n := 6) (by decide)
    omega
  exact cComponent_normal_of_quotient_normal hK (pCore 2 G) hn

end CFSG.Quasithin.ChapterA.SQTKStructure.NonnormalOuterSource.FourModels
