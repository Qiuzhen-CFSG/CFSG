module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.CentralIntersectionLinear
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.PathIntervals
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ResidualNaturalityExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.RankOneCentralEquivalences

/-!
# Source 8.6 for an arbitrary linear opposite quotient

The source path theorem supplies the full opposite Sylow image. For fields
larger than two, the proved 8.5 exclusion and the residual square comparison
force the starting center to be natural. At field order two, the independent
two-rank-one argument gives the same conclusion. Both branches identify the
literal commutator H with the terminal center.

Only the original commuting-intersection hypothesis 8.6(c), full local
catalogue and a linear beta marking remain. The result supplies Chapter 9's
reverse natural-center recognition without an earlier-source callback.
Source: DGS, *Groups and Graphs* (1985), 8.6, printed pp.139–140.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open CommutingTrivial
universe u
variable {G : Type u} [Group G] {L : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "Γ" => Reduction.reducedFamily L S₀

theorem reduced_linear_terminal_intersection_natural
    (h : HypothesisF11 L S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ}
    (hc : IsCriticalPair Γ a a') (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (hne : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ ≠ ⊥)
    (hinter : ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1 ⊓ Q Γ beta⁆ = ⊥)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (e : (graphLocalGroup Γ beta ⧸ pCore 2 (graphLocalGroup Γ beta)) ≃* SL(2,F)) :
    b Γ = 3 ∧ ⁅V Γ beta 1 ⊓ Q Γ a',V Γ a' 1⁆ = Z Γ a' ∧
      Noncommuting.HasNaturalCenter (graphLocalGroup Γ a) (Z Γ a) (Q Γ a) := by
  let := Fintype.ofFinite F
  obtain ⟨n,_,hFn⟩ := FiniteField.card F 2
  have hn : 0 < (n : ℕ) := n.property
  have hF : Nat.card F = 2^(n : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hFn
  by_cases hlarge : 1 < (n : ℕ)
  · obtain ⟨hb3,hactor,_⟩ := reduced_critical_linear_paired_intervals h models hc hab hd hb hcomm hne e
    obtain ⟨w,hm,_⟩ := exists_moving_neighbor Γ (fun v => (source_Z_Q_U (Reduction.reduced_triple h) v).1)
      beta a' hne
    have hnot : ¬ NaturalResidualSection h beta e n :=
      reduced_natural_residual_exclusion h (Reduction.reduced_graph_core_obstruction h)
        models hc hab hd hb3 hcomm hne hn hF e
    obtain ⟨_,hnat,hH⟩ := reduced_linear_terminal_commuting_intersection_natural h models hc hab hd hb
      hcomm w hm hinter hlarge hF e hactor hnot
    exact ⟨hb3,hH,hnat⟩
  · have hn1 : (n : ℕ) = 1 := by omega
    have hFtwo : Nat.card F = 2 := by simpa only [hn1,pow_one] using hF
    obtain ⟨_,_,f,_,_,_,_⟩ := reduced_critical_parameter_transport h hc hab hd hb hcomm
    let : Finite (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')) :=
      Finite.of_equiv SL(2,F) (f.trans e).toEquiv.symm
    have hr : primeRank 2 (graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')) ≤ 1 := by
      rw [primeRank_congr 2 (f.trans e)]
      let T : Sylow 2 SL(2,F) := default
      have hT : Nat.card T = 2 :=
        (Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 T).symm.toEquiv).trans hFtwo
      exact T.primeRank_le_one_of_isCyclic (isCyclic_of_prime_card hT)
    exact reduced_rank_one_terminal_intersection_natural h models hc hab hd hb hcomm hne hr hinter

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
