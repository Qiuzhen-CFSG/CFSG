module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.UnitaryMovingCentral
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralEquivalencesSource
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.AdjacentParameterEquality

/-!
# The source conclusions of DGS 8.7 at a proper unitary edge

A moving unitary neighbor of field order at least four with proper adjacent
core product gives centrality of the original displacement commutator. The
proved equivalences of 8.6 then identify it with the terminal center and make
the starting center natural. The natural-start parameter theorem identifies
the omega orders of the actual alpha and beta quotient Sylows.

Source: DGS, *Groups and Graphs* (1985), 8.6--8.7, pp.139--140.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "Γ" => Reduction.reducedFamily L S₀

/-- All original 8.7 conclusions in the proper large-unitary moving branch.
No centrality, naturality or terminal-perfectness premise is retained. -/
theorem reduced_unitary_proper_source_conclusions
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ}
    (hc : IsCriticalPair Γ a a') (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    {n : ℕ} (hn : 2 ≤ n)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 (2^n) ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 (2^n))
    (hproper : ¬ (stabilizer Γ w.val ⊓ stabilizer Γ a').pCoreIn 2 ≤
      Q Γ w.val ⊔ Q Γ a') :
    b Γ = 3 ∧ ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = Z Γ a' ∧
      Noncommuting.HasNaturalCenter (graphLocalGroup Γ a) (Z Γ a) (Q Γ a) ∧
      ∀ (Rα : Sylow 2 (graphLocalGroup Γ a)) (Rβ : Sylow 2 (graphLocalGroup Γ beta)),
        Nat.card (omegaCenterIn ((Rα : Subgroup (graphLocalGroup Γ a)).map
          (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ a))))) =
        Nat.card (omegaCenterIn ((Rβ : Subgroup (graphLocalGroup Γ beta)).map
          (QuotientGroup.mk' (pCore 2 (graphLocalGroup Γ beta))))) := by
  have hne : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ ≠ ⊥ := by
    intro hz
    exact hm (bot_unique
      ((commutator_mono le_rfl (Z_neighbor_le_V Γ w.property)).trans hz.le))
  have hcentral := reduced_unitary_proper_moving_commutator_central
    h models hc hab hd hb hcomm w hm hn hu hproper
  obtain ⟨hb3,_,_,_,hAD,hDI,hIN,hNE⟩ :=
    reduced_critical_central_equivalences h models hc hab hd hb hcomm hne
  have hnat := hIN.mp (hDI.mp (hAD.mp hcentral))
  exact ⟨hb3,hNE.mp hnat,hnat,
    reduced_natural_start_adjacent_parameter_equality h models hc hab hd hb hcomm hne hnat⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
