module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightSymplectic
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightLinear
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLocalRightBender
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeLinearGeometry

/-!
# Right-factor selection outside the linear field-four row

The original overlap two-core normalizes both higher-field linear factors.
Together with their proved left-Cartan action and exact Borel product, this
completes their right-factor contracts. The source E.2.2 case split now
constructs a normalized right factor in every Bender, exchanged, symplectic
and higher-field linear row. Only the marked linear field-four row remains;
its possible scalar cover is retained explicitly.

The Chapter 12 extension consumes this reduction in the original local
preparation. The independent uniqueness-over-L implication and subsequent
completion recognition remain with their original source owners.
Source: Aschbacher--Smith 5.1.10--11 and 5.2.1,4, pp.634--635,646,649--650.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.LinearThree
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {G : Type*} [Group G] [Finite G]

/-- Source S-normalization removes the final linear right-factor premise
outside field four, on each of the same two canonical factors. -/
theorem linear_source_rightFactor
    {T : Sylow 2 G} {L H A B : Subgroup G} {f : ℕ}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G))
    {C : Subgroup H} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C))
    (hc : SingleClauses ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H)) (hf : 1 < f) (hf2 : f ≠ 2)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 2 ^ f)
    (e : sourceImage ((normalizer (L : Set G)).subgroupOf H) C ≃* PSL(3,F))
    (he : (componentOverlap ((normalizer (L : Set G)).subgroupOf H) C).map
      e.toMonoidHom = borel F)
    (hmove : MovesDiagram ((normalizer (L : Set G)).subgroupOf H) C
      ((T : Subgroup G).subgroupOf H) e (pointParabolic F) (lineParabolic F)) (i : Bool) :
    RightFactor T L H A B ((Prime.linearSourceFactor
      ((normalizer (L : Set G)).subgroupOf H) C e i).map H.subtype) := by
  let M := (normalizer (L : Set G)).subgroupOf H
  let : C.Normal := DiagramHall.single_component_normal (T.subtype hH.1.1.2) hC hc
  apply linear_source_rightFactor_of_sourceS hTL hH hpar c hN hC hqs hc hf hF e he hmove i
  have hSm : (M.pCoreIn 2).map H.subtype = sourceS L H := by
    rw [map_pCoreIn_of_injective 2 M H.subtype H.subtype_injective,subgroupOf_map_subtype]
    rfl
  rw [←hSm]
  exact (map_mono (Prime.linearSourceFactor.twoCore_normalizes hf hf2 hF e he i)).trans
    (le_normalizer_map H.subtype)

/-- The source case split constructs the right factor except in the genuine
field-four linear diagram row. No quotient is identified with its central cover. -/
theorem source_rightFactor_or_four_linear_diagram
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hpar : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hN : localBorel T L ≤ normalizer (residual H : Set G)) :
    (∃ R : Subgroup G, RightFactor T L H A B R) ∨ RightLinearFourDiagramSource T L H := by
  rcases right_source_cases h.qtke h.sylow_normalizes hH hpar with hs | hs
  · exact Or.inl (rankOne_source_rightFactor h hH hpar c hN hs)
  obtain ⟨C,f,hC,hqs,hgen,hf,hc,hm⟩ := hs
  rcases hm with ⟨F,_,_,_,_,hF,e,he,hmove⟩ | ⟨F,_,_,_,_,hF,e,he,hmove⟩
  · by_cases hf2 : f = 2
    · subst f
      exact Or.inr ⟨C,hC,hqs,hgen,hc,F,inferInstance,inferInstance,inferInstance,
        by simpa using hF,e,he,hmove⟩
    · exact Or.inl ⟨_,linear_source_rightFactor h.sylow_normalizes hH hpar c hN
        hC hqs hc hf hf2 hF e he hmove true⟩
  · obtain ⟨eF,_,hr⟩ := symplectic_source_rightFactors h.sylow_normalizes hH hpar c hN
      hC hqs hc hf hF e he hmove
    exact Or.inl ⟨_,(hr true).1⟩

/-- Under the original PSL₃(4) exclusion, the remaining marked field-four
row has the genuine special-linear quotient. Its scalar center is retained. -/
theorem four_linear_diagram_residual_isSL
    {T : Sylow 2 G} {L H : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hTH : (T : Subgroup G) ≤ H)
    (hnot : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hs : RightLinearFourDiagramSource T L H) :
    Chapter1.Section02.LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4 := by
  obtain ⟨C,hC,hqs,_,hc,F,_,_,_,hF,e,_,_⟩ := hs
  have hO : pCore 2 H ≤ sourceKernel ((normalizer (L : Set G)).subgroupOf H) :=
    normal_le_normalCore.mpr ((pCore_isPGroup.le_sylow_of_normal (T.subtype hTH)).trans (comap_mono hTL))
  have hm := Prime.linear_diagram_component_quotient hC hqs hO (by decide : 1 < 2)
    (show Nat.card F = 2 ^ 2 by simpa using hF) e
  have hCK := DiagramHall.single_component_eq_twoResidual (T.subtype hTH) hC hc
  rw [←hCK] at hm
  exact hm.resolve_left hnot

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
