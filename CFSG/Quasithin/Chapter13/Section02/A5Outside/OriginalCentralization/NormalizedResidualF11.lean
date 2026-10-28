module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalUniqueness
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericGlobalLocalCartan
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeRankOneSelection
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalCompletion
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# The normalized whole-residual pair in the original A5 context

The actual rank-one quotient of O²(H) selects the whole residual as the right
factor. Its source completion is normal in L H because T normalizes L,
O²(H), and S = O₂(N_G(L) ∩ H). Uniqueness over L T kills the two-core of
L H, hence also the two-core of this normal source completion.

The compatible Cartans and literal right-factor geometry therefore supply
all F.1.1 clauses without uniqueness over bare L or a prepared-pair input.
The right Borel normalizes the same S. The original groups and full Borel
remain unchanged; no amalgam comparison or ambient recognition is assumed.
Source: Aschbacher--Smith 1.2.7, 5.1.9--11 and 5.2.4--5,
printed pp.506--507,634--635,649--650.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source Chapter6.Source.RankOneGeneric
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- Normality under the original T transfers the whole-pair core obstruction
to the source completion with S = O₂(N_G(L) ∩ H). -/
theorem original_residual_generated_core_eq_bot
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    pCore 2 (ChapterF.Source.generated ![L,residual H] (Global.sourceS L H)) = ⊥ := by
  let M := L ⊔ H
  let N := ChapterF.Source.generated ![L,residual H] (Global.sourceS L H)
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hM : pCore 2 M = ⊥ := by
    by_contra hc
    obtain ⟨X,hX,hMX⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot M hc
    have hLM : L ⊔ (T : Subgroup G) ≤ M :=
      sup_le le_sup_left (hTH.trans le_sup_right)
    have he := d.unique_maximal_overgroup X hX (hLM.trans hMX)
    exact hH.1.2 (he ▸ le_sup_right.trans hMX)
  have hNM : N ≤ M :=
    le_sup_left.trans (Global.residual_completion_sup_sylow d.normalizes_L hH.1.1.2).le
  have hMN : M ≤ normalizer (N : Set G) := by
    change L ⊔ H ≤ normalizer (N : Set G)
    rw [←Global.residual_completion_sup_sylow d.normalizes_L hH.1.1.2]
    exact sup_le N.le_normalizer
      (Global.residual_completion_sylow_normalizes d.normalizes_L hH.1.1.2)
  have hcore : N.pCoreIn 2 = ⊥ := by
    apply bot_unique
    have hm : M.pCoreIn 2 = ⊥ := by
      simp only [Subgroup.pCoreIn,hM,Subgroup.map_bot]
    exact (pCoreIn_mono_of_normalizes hNM hMN).trans_eq hm
  exact ((pCore 2 N).map_eq_bot_iff_of_injective N.subtype_injective).mp hcore

private theorem linear_quotient_of_a5 {X : Type*} [Group X]
    (e : X ≃* alternatingGroup (Fin 5)) : ClassicalGroup.IsPSL X 2 (2^2) := by
  refine ⟨GaloisField 2 2,inferInstance,inferInstance,
    GaloisField.card 2 2 (by decide),?_⟩
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
    (K := GaloisField 2 2) (by rw [GaloisField.card 2 2 (by decide)]; norm_num)
  exact ⟨e.trans f.symm⟩

private theorem input_of_hstar
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Input KnownSimple.IsKnownSimple T L (RankOneModule.wholeReduced T L) 2 := by
  have h := Section03.A5Setup.OriginalMaximality.hypothesis1221 d.hypothesis d.quotient
  obtain ⟨hM,hTM,_⟩ := RankOneModule.normalizer_configuration d.chosen h
  refine ⟨h.simpleQTKE,RankOneModule.faithfulMaximalFamily_of_hypothesis h,
    by decide,linear_quotient_of_a5 d.quotient,hM,hTM,RankOneModule.wholeReduced_mem,
    d.chosen.rankOne_commutatorLayer_ne_bot,?_⟩
  have hc : pCore 2 H ≠ ⊥ := by
    intro hb
    apply hH.1.1.1
    simp only [Subgroup.pCoreIn,hb,Subgroup.map_bot]
  obtain ⟨X,hX,hHX⟩ := exists_maximalTwoLocal_overgroup_of_twoCore_ne_bot H hc
  exact Chapter3.hasMaximalOutside_of_two_distinct hM hX hTM (hH.1.1.2.trans hHX)
    (fun hx => hH.1.2 (hx ▸ hHX))

/-- The original normalized A5 residual supplies its compatible Cartans,
whole right factor, genuine F.1.1 pair, and full normalized right Borel.
No uniqueness over L, preparation record, or model comparison is an input. -/
theorem original_normalized_residual_hypothesisF11
    (d : Context T L V V₁ V₂ V₃)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hm : Nonempty (((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) ≃*
      alternatingGroup (Fin 5)))
    (hN : (normalizer (((T : Subgroup G).subgroupOf L) : Set L)).map L.subtype ≤
      normalizer (residual H : Set G)) :
    ∃ A B : Subgroup G, CartanPair T L H A B ∧
      Global.RightFactor T L H A B (residual H) ∧
      ChapterF.Source.HypothesisF11 ![L,residual H] (Global.sourceS L H) ∧
      ChapterF.Source.borel (residual H) (Global.sourceS L H) ≤
        normalizer (Global.sourceS L H : Set G) := by
  have h := Section03.A5Setup.OriginalMaximality.hypothesis1221 d.hypothesis d.quotient
  have hpsl := linear_quotient_of_a5 d.quotient
  have hi := input_of_hstar d hH
  have hBorel : localBorel T L ≤ normalizer (residual H : Set G) := by
    simpa only [localBorel_eq_map] using hN
  obtain ⟨A,B,c⟩ := d.chosen.rankOne_exists_cartanPair h (by decide : 1 < 2) hpsl hH hgen
  have hrank : ChapterF.Source.IsRankOneModel
      ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) :=
    .linear 2 (by decide) (linear_quotient_of_a5 hm.some)
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
