module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.BinaryUnitaryCentrality.SourceReductions

/-!
# Remaining terminal models for a binary unitary moving neighbor

Apply the original-graph field-square exclusions to the complete retained
terminal catalogue. A moving SU₃(2) or PSU₃(2) neighbor leaves only linear
terminal quotients and the small dihedral, Suzuki and unitary rows. The
nonzero moving commutator and its precise graph placement remain in the
hypotheses. This reduction does not yet prove the centrality conclusion of
DGS 8.7 in the surviving rows.

Source: DGS, *Groups and Graphs* (1985), 5.10 and 8.7,
printed pp.111--112,140.
-/

public noncomputable section
open Subgroup
open Subgroup.CosetGeometry.RankTwo Theory.GroupTheory.AmalgamGraph
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial.BinaryUnitaryCentrality
variable {G : Type*} [Group G] {J : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "Γ" => Reduction.reducedFamily J S₀

/-- Exhaustive remaining terminal rows, obtained from the two source
comparison exclusions while retaining both binary moving covers. -/
theorem reduced_terminal_catalogue
    (h : HypothesisF11 J S₀)
    (models : ∀ v : Vertex Γ,
      IsRankOneModel (graphLocalGroup Γ v ⧸ pCore 2 (graphLocalGroup Γ v)))
    {a beta a' : Vertex Γ} (hc : IsCriticalPair Γ a a')
    (hab : (graph Γ).Adj a beta)
    (hd : (graph Γ).dist beta a' + 1 = b Γ) (hb : 1 < b Γ)
    (hcomm : ⁅Z Γ a,Z Γ a'⁆ = ⊥)
    (w : (graph Γ).neighborSet a')
    (hm : ⁅V Γ beta 1 ⊓ Q Γ a',Z Γ w.val⁆ ≠ ⊥)
    (hu : ClassicalGroup.IsPSU (graphLocalGroup Γ w.val ⧸
      pCore 2 (graphLocalGroup Γ w.val)) 3 2 ∨
      IsSU (graphLocalGroup Γ w.val ⧸ pCore 2 (graphLocalGroup Γ w.val)) 3 2)
    : let D := graphLocalGroup Γ a' ⧸ pCore 2 (graphLocalGroup Γ a')
      (∃ n : ℕ, 0 < n ∧ ClassicalGroup.IsPSL D 2 (2^n)) ∨
        Nonempty (D ≃* DihedralGroup 5) ∨
        Nonempty (D ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) ∨
        ClassicalGroup.IsPSU D 3 2 ∨ IsSU D 3 2 := by
  cases models a' with
  | linear n hn hi => exact Or.inl ⟨n,hn,hi⟩
  | dihedral hi => exact Or.inr (Or.inl hi)
  | suzuki m hi =>
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · exact Or.inr (Or.inr (Or.inl hi))
      · exact (reduced_suzuki_terminal_impossible h models hc hab hd hb hcomm w hm hu hmpos hi.some).elim
  | projective_unitary k hk hi =>
      by_cases hk2 : 2 ≤ k
      · exact (reduced_large_unitary_terminal_impossible h models hc hab hd hb hcomm w hm hu hk2
          (Or.inl hi)).elim
      · have hk1 : k = 1 := by omega
        exact Or.inr (Or.inr (Or.inr (Or.inl (by simpa only [hk1,pow_one] using hi))))
  | special_unitary k hk hi =>
      by_cases hk2 : 2 ≤ k
      · exact (reduced_large_unitary_terminal_impossible h models hc hab hd hb hcomm w hm hu hk2
          (Or.inr hi)).elim
      · have hk1 : k = 1 := by omega
        exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [hk1,pow_one] using hi))))

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial.BinaryUnitaryCentrality
