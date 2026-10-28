module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NormalizedResidualF11

/-!
# Whole-residual F.1.1 from an actual rank-one residual quotient

The original A5 Context fixes the left factor and constructs its compatible
Cartans. On the normalized branch, any literal rank-one model for the full
residual quotient selects that whole residual as right factor. Its source
completion is normal in L H, so uniqueness over L T kills the two-core.

This exposes the single-Bender case without an A5 marking on the residual.
The selected proper exchanged/diagram factors still require a separate
generated-core argument.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- The whole original residual supplies F.1.1 from its exact rank-one
quotient witness and the actual full relative-normalizer branch. -/
theorem original_normalized_rankOne_hypothesisF11
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hrank : ChapterF.Source.IsRankOneModel
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)))
    (hN : (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer (residual H : Set G)) :
    ∃ A B : Subgroup G, CartanPair T L H A B ∧
      Global.RightFactor T L H A B (residual H) ∧
      ChapterF.Source.HypothesisF11 ![L,residual H] (Global.sourceS L H) ∧
      ChapterF.Source.borel (residual H) (Global.sourceS L H) ≤
        normalizer (Global.sourceS L H : Set G) := by
  have h := Section03.A5Setup.OriginalMaximality.hypothesis1221 d.hypothesis d.quotient
  have hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^2) := by
    refine ⟨GaloisField 2 2,inferInstance,inferInstance,
      GaloisField.card 2 2 (by decide),?_⟩
    obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
    exact ⟨d.quotient.trans f.symm⟩
  obtain ⟨hM,hTM,_⟩ := RankOneModule.normalizer_configuration d.chosen h
  have hi : Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) 2 := by
    refine ⟨h.simpleQTKE,RankOneModule.faithfulMaximalFamily_of_hypothesis h,
      by decide,hpsl,hM,hTM,RankOneModule.wholeReduced_mem,
      d.chosen.rankOne_commutatorLayer_ne_bot,?_⟩
    have hc : pCore 2 H ≠ ⊥ := by
      intro hb
      apply hH.1.1.1
      simp only [Subgroup.pCoreIn,hb,Subgroup.map_bot]
    obtain ⟨X,hX,hHX⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H hc
    exact Chapter3.hasMaximalOutside_of_two_distinct hM hX hTM
      (hH.1.1.2.trans hHX) (fun hx => hH.1.2 (hx ▸ hHX))
  have hBorel : localBorel T L ≤ normalizer (residual H : Set G) := by
    simpa only [localBorel_eq_map] using hN
  obtain ⟨A,B,c⟩ := d.chosen.rankOne_exists_cartanPair h (by decide : 1 < 2)
    hpsl hH hgen
  have geom := Global.rankOne_residual_geometry d.normalizes_L hH hrank
  have r := geom.rightFactor c d.normalizes_L hH hBorel (Set.mem_singleton _)
  obtain ⟨hleft,hSylow⟩ := d.chosen.rankOne_sourceS_intersection_left h hpsl hH
  have hSL : Global.sourceS L H ≤ normalizer (L : Set G) :=
    (Global.sourceS_le_sylow d.normalizes_L hH.1.1.2).trans d.normalizes_L
  have hb : ChapterF.Source.borel L (Global.sourceS L H) = localBorel T L := by
    unfold ChapterF.Source.borel localBorel
    rw [hleft]
  refine ⟨A,B,c,r,?_,?_⟩
  · refine ⟨inferInstance,pCore_isPGroup.map _,?_,?_,?_,?_,
      original_residual_generated_core_eq_bot d hH,
      r.characteristic_two hi hH c hleft hBorel⟩
    · intro i
      fin_cases i
      · exact hSL
      · exact r.S_normalizes
    · intro i
      fin_cases i
      · exact hSylow
      · exact r.sylow
    · intro i
      fin_cases i
      · exact .linear 2 (by decide) hpsl
      · exact r.quotient
    · intro i
      fin_cases i
      · change ChapterF.Source.borel (residual H) (Global.sourceS L H) ≤ _
        rw [r.borel]
        exact sup_le (inf_le_left.trans hSL)
          (inf_le_left.trans (c.right_le.trans inf_le_left))
      · change ChapterF.Source.borel L (Global.sourceS L H) ≤ _
        rw [hb]
        exact hBorel
  · rw [r.borel]
    exact sup_le (inf_le_left.trans (Global.sourceS L H).le_normalizer)
      (inf_le_left.trans (c.right_le.trans (Global.intersection_normalizes_sourceS L H)))

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
