module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.CommutingTrivialChapterEightSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.CommutingTrivialBinaryConsumers
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.TheoremBFullCatalogue

/-!
# Original consumers after full Chapter 8 discharge

The proved 8.6 theorem and the full retained catalogue now give source 9.10
without supplied reverse recognition or binary-model witnesses. Its actual
markings identify the original starred quotients and full parabolics in
13.1(b). The original index-five condition and the selected generic perfect
endpoint exclude this commuting-trivial branch in their quasithin consumers.

All original quotient representatives, selected subgroups and ambient
hypotheses are retained. Source: DGS, *Groups and Graphs* (1985), 8.6,
9.10 and 13.1, pp.139,147–150,191; Aschbacher–Smith F.1.9–12 and 12.2.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Representation.RankOne.QuadraticRecognition
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups IsMulCommutative
universe u

namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial
open Reduction
section Reduced
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "Γ" => Reduction.reducedFamily L S


/-- Source 9.10 marks both original starred quotients over the binary field. -/
theorem reduced_critical_binary_starred_quotients_from_chapterEight
    (h : HypothesisF11 L S)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ}
    (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ)
    (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (htriv : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥) :
    b Γ = 3 ∧ ∀ i : Bool,
      Nonempty ((CommutingThreeProfile.ReducedLayer.star L S i ⧸
        pCore 2 (CommutingThreeProfile.ReducedLayer.star L S i)) ≃* SL(2,ZMod 2)) := by
  obtain ⟨hb3,F,instF,finF,charF,K,instK,finK,charK,hF,hK,⟨eb⟩,⟨ea⟩⟩ :=
    reduced_critical_fields_two_from_chapterEight (L := L) (S₀ := S)
      (a := a) (beta := beta) (a' := a') h models hc hab hd hb hcomm htriv
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  exact ⟨hb3,adjacent_field_two_starred_quotients h hab ea eb (hK.trans hF.symm) hF⟩

/-- The full original 13.1(b) conclusion, with source 9.10's field orders discharged. -/
theorem reduced_critical_binary_full_parabolics_from_chapterEight
    (h : HypothesisF11 L S)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ}
    (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ)
    (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (htriv : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥) :
    b Γ = 3 ∧
      ∃ e : ∀ i : Bool, (CommutingThreeProfile.ReducedLayer.star L S i ⧸
          pCore 2 (CommutingThreeProfile.ReducedLayer.star L S i)) ≃* SL(2,ZMod 2),
        commonBorel L S = S ∧ G₀ L S = generated L S ∧
        (∀ i : Bool, ∃ f : (parabolic L S (if i then 1 else 0) ⧸
            pCore 2 (parabolic L S (if i then 1 else 0))) ≃* SL(2,ZMod 2),
          (∀ x : L (if i then 1 else 0),
            f (QuotientGroup.mk (inclusion (show L (if i then 1 else 0) ≤
              parabolic L S (if i then 1 else 0) from le_sup_left.trans le_sup_left) x)) =
              e i (QuotientGroup.mk (CommutingThreeProfile.ReducedLayer.originalActor
                (L := L) (S := S) i x))) ∧
          starredParabolic L S (if i then 1 else 0) = parabolic L S (if i then 1 else 0) ∧
          Group.IsSolvable (parabolic L S (if i then 1 else 0))) ∧
        ∀ v : Vertex Γ,
          graphLocalGroup Γ v = stabilizer Γ v ∧
          Nonempty ((stabilizer Γ v ⧸ pCore 2 (stabilizer Γ v)) ≃* SL(2,ZMod 2)) := by
  obtain ⟨hb3,F,instF,finF,charF,K,instK,finK,charK,hF,hK,⟨eb⟩,⟨ea⟩⟩ :=
    reduced_critical_fields_two_from_chapterEight (L := L) (S₀ := S)
      (a := a) (beta := beta) (a' := a') h models hc hab hd hb hcomm htriv
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  exact ⟨hb3,adjacent_field_two_full_parabolics h hab ea eb (hK.trans hF.symm) hF⟩

end Reduced

section Quintic
variable {G : Type u} [Group G] {P R S : Subgroup G}
local notation "Γ" => Reduction.reducedFamily ![P,R] S

/-- The actual original index five excludes the commuting-trivial source branch. -/
theorem no_reduced_critical_commuting_trivial_of_quintic_source
    (h : HypothesisF11 ![P,R] S) (hfive : S.relIndex P = 5)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ}
    (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ)
    (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (htriv : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥) : False := by
  obtain ⟨hb3,F,instF,finF,charF,K,instK,finK,charK,hF,hK,⟨eb⟩,⟨ea⟩⟩ :=
    reduced_critical_fields_two_from_chapterEight h models hc hab hd hb hcomm htriv
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  exact no_adjacent_field_two_of_local_quintic h hfive hab ea eb (hK.trans hF.symm) hF

end Quintic
end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingTrivial

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type u} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
local notation "Γ" => Reduction.reducedFamily ![L,R] (sourceS L H)

/-- The same selected generic pair excludes the original commuting-trivial branch. -/
theorem no_commuting_trivial_source_from_chapterEight
    (d : Preparation T L H A B R) (h : Input κ T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ}
    (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ)
    (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (htriv : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = ⊥) : False := by
  obtain ⟨hb3,F,instF,finF,charF,K,instK,finK,charK,hF,hK,⟨eb⟩,⟨ea⟩⟩ :=
    reduced_critical_fields_two_from_chapterEight (d.hypothesisF11 h hTH) models hc hab hd hb hcomm htriv
  let := instF
  let := finF
  let := charF
  let := instK
  let := finK
  let := charK
  exact d.no_commuting_trivial_binary_fields h hTH hp hab ea eb (hK.trans hF.symm) hF

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
open ChapterF.Source ChapterF.Source.DGS85 ChapterF.Source.DGS85.CommutingTrivial
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B R : Subgroup G}
local notation "Γ" => Reduction.reducedFamily ![L,R] (Global.sourceS L H)

/-- The chosen-module application keeps its selected perfect R and derives
both binary field orders from the original source hypotheses. -/
theorem rankOne_no_commuting_trivial_source_from_chapterEight
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (d : Global.Preparation T L H A B R) (hp : Group.IsPerfect R)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ}
    (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ)
    (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (htriv : ⁅ChapterF.Source.DGS85.V Γ beta 1 ⊓ Q Γ a',ChapterF.Source.DGS85.V Γ a' 1⁆ = ⊥) : False := by
  exact d.no_commuting_trivial_source_from_chapterEight
    (D.rankOne_generic_input_of_many h hmany hn hpsl) hH.1.1.2 hp
    models hc hab hd hb hcomm htriv

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
