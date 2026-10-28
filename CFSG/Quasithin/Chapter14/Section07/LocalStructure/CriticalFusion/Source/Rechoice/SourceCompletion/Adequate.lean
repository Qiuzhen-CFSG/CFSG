module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.SourceCompletion.Adequate

/-!
# Source 14.7.70 with adequate F.6 recognition

The original permitted rechoice and rank-four contradiction now consume
only the ambient dihedral PSL₂ data actually used in the Goldschmidt step.
All subgroup choices, source actions and conclusions are retained.

Source: Aschbacher–Smith, 14.7.70, printed pp.1074–1075.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion.Adequate
open Subgroup Representation Chapter12.Section08 LocalGeometry LocalGeometry.Preparation
open Goldschmidt Goldschmidt.QuotientComparison
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W) (c : CriticalPath (L := L) F)
  (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
  (uniqueness : Uniqueness127 KnownSimple.IsKnownSimple.{u})
  (thompson : ThompsonWitness.EarlierThompsonNormality.{u})
  (faithful : EarlierFaithfulClassification G (T : Subgroup G))
  (b5 : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} KnownSimple.IsKnownSimple)
  (amalgams : ∀ (H : Type u) [Group H] [Finite H] (A B : Subgroup H),
    ChapterF.IsGoldschmidtTriple A B → pCore 2 H = ⊥ → Nat.card A ≤ 384)
  (sourceF : FSource.AdequateClassificationInput KnownSimple.IsKnownSimple.{u})
include structural uniqueness thompson faithful b5 amalgams sourceF

/-- All four clauses of the original14.7.70 for one permitted rechoice. -/
theorem source_rechoice_with_point
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2) (separation : d.ModuleSeparation)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (earlier_conjugacy : ∀ c' : CriticalPath (L := L) F, c'.Zα ≤ V →
      c'.b = 3 ∧ ∃ l ∈ L, c'.Uα = conjugate F.U l) :
    ∃ n : group F L, (n : G) ∈ F.Li L 1 ∧ F.Vi 1 ≤ Fcomm (c.reselect n) ∧
      (c.reselect n).Zα ≤ F.Vi 2 ∧ primeRank 2 d.U₀ ≤ 2 ∧
      F.U ⊓ (c.reselect n).Uα = d.U₀ ⊔ V ∧
      F.U ⊓ (c.reselect n).Uα = ⁅F.U, (c.reselect n).Uα⁆ ⊔ V ∧
      F.U ⊓ (c.reselect n).Uα = ⁅F.U, (c.reselect n).Uα⁆ ⊔ d.U₀ ∧
      c.b = 3 ∧ ∃ l ∈ L, (c.reselect n).Uα = conjugate F.U l := by
  let d' := LeftChiefFactors.BorelRefinements.upperRemark d structural
  have mark : UpperMarking d' :=
    LeftChiefFactors.BorelRefinements.upperRemark_upperMarking d structural
  have actors : MarkedSpans.LocalActors d' := localActors_of_source d structural
  have sep : d'.ModuleSeparation := separation
  have h68' : {x : G | IsConj d'.z x} ∩ (d'.U₀ : Set G) = {d'.z} := h68
  have heven' : (F.U.subgroupOf (conjugate F.H c.conjugator)).map
      (reciprocalQuotient d' c) ≤ alternatingGroup (Fin 5) := heven
  obtain ⟨n, hn, p⟩ := exists_prepared_of_commutator d' c earlier selection h69 sep
    hcomm h68' mark actors hUH heven'
  have hrank : primeRank 2 d'.U₀ ≤ 2 := by
    by_contra hn
    have h3 : primeRank 2 d'.U₀ = 3 := by have := p.rank_bound; omega
    have geometry := SourceActors.source_rank_three_geometry_reselect d' c n earlier
      (p.rank_three h3) (core_action_of_commutator_le d' hcomm.le)
      mark sep actors hcomm hUH selection heven'
    have hVI := Goldschmidt.SourceCompletion.Adequate.primeRank_VI d' (c.reselect n)
      structural uniqueness thompson faithful b5 amalgams sourceF geometry.toGeometry mark hcomm
    have hle := primeRank_mono 2 (span_Zα_le_VI (c.reselect n) geometry.span.le)
    rw [geometry.orbit_rank, hVI] at hle
    omega
  obtain ⟨hZ, h₁, h₂, h₃, hb, hc⟩ := p.low_rank sep hrank earlier_conjugacy
  exact ⟨n, hn, p.point_le, hZ, hrank, h₁, h₂, h₃, hb, hc⟩

/-- The original public statement, forgetting only the retained point-commutator witness. -/
theorem source_rechoice
    (earlier : c.EarlierImages) (selection : c.RankSelection)
    (h69 : Nat.card (star F c.Uα) = 2) (separation : d.ModuleSeparation)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (h68 : {x : G | IsConj d.z x} ∩ (d.U₀ : Set G) = {d.z})
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (heven : (F.U.subgroupOf (conjugate F.H c.conjugator)).map (reciprocalQuotient d c) ≤
      alternatingGroup (Fin 5))
    (earlier_conjugacy : ∀ c' : CriticalPath (L := L) F, c'.Zα ≤ V →
      c'.b = 3 ∧ ∃ l ∈ L, c'.Uα = conjugate F.U l) : Statement c d := by
  obtain ⟨n, _, _, hZ, hrank, h₁, h₂, h₃, hb, hc⟩ :=
    source_rechoice_with_point d c structural uniqueness thompson faithful b5 amalgams sourceF
      earlier selection h69 separation hcomm h68 hUH heven earlier_conjugacy
  exact ⟨n, hZ, hrank, h₁, h₂, h₃, hb, hc⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.SourceCompletion.Adequate
