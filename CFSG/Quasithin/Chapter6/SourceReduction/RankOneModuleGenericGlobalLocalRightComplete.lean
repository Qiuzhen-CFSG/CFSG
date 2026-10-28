module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightDiagram
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeLinearFour

/-!
# Complete normalized right-factor selection

The source's exclusion of the intrinsic PSL₃(4) residual forces a nontrivial
scalar center in the field-four linear diagram row. The proved two-core
normalization theorem therefore applies to the same canonical factors used
by the Cartan and Borel calculations. It completes the full right-factor
contract at field four without removing the covering center.

Together with the exchanged, single-Bender, symplectic and higher-field
linear cases, this constructs a perfect right factor in every original
source row. Its independent field degree is retained; the factor is not
identified with all of O²(H). The Chapter 12 extension uses this selection
to construct preparation, with the original uniqueness-over-L implication
still supplied by qt-d-1222-rankone-global-uniqueness.

Source: Aschbacher–Smith E.2.2, 5.1.10–11 and 5.2.1–5,
printed pp.215–216,634–635,646–650 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- The full right-factor contract on each canonical linear factor, including
field four with its original scalar cover and projective exclusion. -/
theorem linear_source_rightFactor_of_nonprojective_four
    {T : Sylow 2 G} {L H A B : Subgroup G} {f : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e (pointParabolic F) (lineParabolic F)) (i : Bool) :
    RightFactor T L H A B ((Prime.linearSourceFactor
      ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype) := by
  by_cases hf2 : f = 2
  · subst f
    let M := (normalizer (L : Set G)).subgroupOf H
    let U := T.subtype hH.1.1.2
    let : C.Normal := DiagramHall.single_component_normal U hC hc
    have hCeq : C = pResidual 2 H :=
      (DiagramHall.single_component_eq_twoResidual U hC hc).symm
    have hnot : ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 4 := hCeq.symm ▸ hthree
    have hO : pCore 2 H ≤ sourceKernel M := normal_le_normalCore.mpr
      ((pCore_isPGroup.le_sylow_of_normal U).trans (comap_mono hTL))
    apply linear_source_rightFactor_of_sourceS hTL hH hpar c hN hC hqs hc hf hF e he hmove i
    have hSm : (M.pCoreIn 2).map H.subtype = sourceS L H := by
      rw [map_pCoreIn_of_injective 2 M H.subtype H.subtype_injective,subgroupOf_map_subtype]
      rfl
    rw [←hSm]
    exact (map_mono (Prime.linearSourceFactor.twoCore_normalizes_four hC hqs hO hc hnot
      (by simpa using hF) e he i)).trans (le_normalizer_map H.subtype)
  · exact linear_source_rightFactor hTL hH hpar c hN hC hqs hc hf hf2 hF e he hmove i

/-- Every original source row constructs a perfect normalized right factor.
Perfectness is retained for identifying the two parabolic residuals. -/
theorem source_rightFactor_perfect
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G)) :
    ∃ R : Subgroup G, RightFactor T L H A B R ∧ Group.IsPerfect R := by
  rcases right_source_cases h.qtke h.sylow_normalizes hH hpar with hs | hs
  · obtain ⟨C,f,hC,hqs,hgen,_,hc | hc⟩ := hs
    · let := hC.perfect
      exact ⟨C.map H.subtype,
        exchanged_source_rightFactor h hH hpar c hN hC hgen hc.1 hc.2,
        Group.IsPerfect.map H.subtype⟩
    · have hCeq : C = pResidual 2 H :=
        BenderHall.SingleClauses.component_eq_residual (S := T.subtype hH.1.1.2) hc.1 hC
      have hp : Group.IsPerfect (residual H) := by
        let : Group.IsPerfect (pResidual 2 H) := hCeq ▸ hC.perfect
        exact Group.IsPerfect.map H.subtype
      exact ⟨residual H,
        (single_bender_source_geometry h.sylow_normalizes hH hC hqs hc.1 hc.2).rightFactor
          c h.sylow_normalizes hH hN (Set.mem_singleton _),hp⟩
  · obtain ⟨C,f,hC,hqs,_,hf,hc,hm⟩ := hs
    rcases hm with ⟨F,_,_,_,_,hF,e,he,hmove⟩ | ⟨F,_,_,_,_,hF,e,he,hmove⟩
    · refine ⟨_,linear_source_rightFactor_of_nonprojective_four h.sylow_normalizes hH hpar
        hthree c hN hC hqs hc hf hF e he hmove true,?_⟩
      let M := (normalizer (L : Set G)).subgroupOf H
      let : Group.IsPerfect (CoveredLocals.factor (Prime.linearComponentProjection M C e) true) :=
        Group.IsPerfect.map _
      let : Group.IsPerfect (Prime.linearSourceFactor M C e true) := Group.IsPerfect.map _
      exact Group.IsPerfect.map H.subtype
    · obtain ⟨eF,_,hr⟩ := symplectic_source_rightFactors h.sylow_normalizes hH hpar c hN
        hC hqs hc hf hF e he hmove
      refine ⟨_,(hr true).1,?_⟩
      let : Group.IsPerfect (Prime.symplecticSourceFactor
          ((normalizer (L : Set G)).subgroupOf H) C eF true) := by
        unfold Prime.symplecticSourceFactor
        exact Group.IsPerfect.map _
      exact Group.IsPerfect.map H.subtype

/-- Complete right-factor selection, with no Bender or diagram callback. -/
theorem source_rightFactor
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G)) :
    ∃ R : Subgroup G, RightFactor T L H A B R := by
  obtain ⟨R,hr,_⟩ := source_rightFactor_perfect h hH hpar hthree c hN
  exact ⟨R,hr⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
