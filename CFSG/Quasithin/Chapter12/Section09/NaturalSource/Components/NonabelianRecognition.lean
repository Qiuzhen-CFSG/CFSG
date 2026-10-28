module
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianLowRank
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianBinaryAmalgam
public import CFSG.Quasithin.ChapterG.Section11.CorrectedReduction

/-!
# Remaining recognition on the original nonabelian natural flag

The original flag supplies the complete G.11 input. If its center is larger
than the point, the returning center supplies a low-rank element even when
the common fixed space is a line. The checked corrected reduction then
applies. The existing original point-component comparisons and CaseFive
contradiction remove every recognized output, including the exceptional
full-linear-four action; the perfect point residual removes the solvable
remainder.

What remains is either the extraspecial-center fixed-line branch, with its
actual point-centralizer three-rank bound, or a nonsolvable whole/exchanged
component recognition on the same representation. This is a source
reduction, not catalogue exhaustion. The earlier universal module theorem
and the independent NaturalReduction 4 remain explicit.
Source: Aschbacher--Smith 12.8.12,12.9.4 and G.11.1--7,
printed pp.855,859--860,364--367.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}
  {L V : Subgroup G} {n : ℕ}

/-- The original natural source has only the indicated unresolved recognition
branches. Every G.10 hypothesis and both extra G.11 clauses are constructed;
no catalogue, irreducibility or nonsolvability premise is added. -/
theorem nonabelian_remaining_recognition
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V n)
    (hn : n = 4 ∨ n = 5) (preferred : PreferredDimension KnownSimple.IsKnownSimple T n)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (four : NaturalReduction KnownSimple.IsKnownSimple.{u} 4)
    (F : InvariantFlag T V n) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ hX : IsElementaryAbelian 2 (F.terminalDot (F.X g)),
      let := hX
      ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
        ChapterG.Section10.Hypothesis F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
        hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
        ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
        ¬ Group.IsSolvable F.TerminalHdot ∧
        IsIrreducible F.terminalRepresentation ∧
        2 * (n-1) ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        ((F.ZU = F.Vi 1 ∧
            fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
              Submodule.span (ZMod 2) {v} ∧
            primeRank 3 (F.terminalPointCentralizer v) ≤ 1) ∨
          (ChapterG.Section11.LowRankWitness F.terminalRepresentation v
              (F.terminalDot (F.X g)) ∧
            ChapterG.Section11.ExchangedRecognition.RemainingComponentModels
              F.terminalRepresentation B v (hatSpace F (F.E g)) (F.terminalDot (F.X g)))) := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  obtain ⟨hX,B,v,hg10,hline,cover,hS,hfixed⟩ :=
    nonabelian_g11_inputs h earlier F hne g hgP hgH
  let := hX
  have hns := nonabelian_hat_not_solvable h hn F hne
  have hd := nonabelian_hat_rank h earlier F hne
  have hi : IsIrreducible F.terminalRepresentation := by
    by_contra hni
    have hb := (hg10.reducible_degree_and_solvable hni).1
    omega
  refine ⟨hX,B,v,hg10,hline,hS,hns,hi,hd,?_⟩
  have step (hw : ChapterG.Section11.LowRankWitness F.terminalRepresentation v
      (F.terminalDot (F.X g))) :
      ChapterG.Section11.ExchangedRecognition.RemainingComponentModels
        F.terminalRepresentation B v (hatSpace F (F.E g)) (F.terminalDot (F.X g)) := by
    rcases ChapterG.Section11.ExchangedRecognition.corrected_conclusion_or_remaining
      hg10 cover hw hS with hc | ⟨_,_,hs | ⟨_,hm⟩⟩
    · obtain ⟨rfl,h5⟩ := nonabelian_corrected_catalogue_orthogonal h hn earlier F hne
        g hgP hgH B v (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) hc
      exact (nonabelian_caseFive_impossible modules h preferred earlier four F hne
        g hgP hgH B h5).elim
    · exact (hns hs.1).elim
    · exact hm
  rcases hfixed with hf | hw
  · by_cases hZ : F.ZU = F.Vi 1
    · exact .inl ⟨hZ,hf,nonabelian_point_three_rank_of_center_eq
        h earlier F hne g hgP hgH v hline hZ⟩
    · have hlt : F.Vi 1 < F.ZU := by
        apply lt_of_le_of_ne ?_ (Ne.symm hZ)
        rw [← F.seed_inf_center_eq_point_of_ambient_natural h.naturalMarking h.rank.1 hne]
        exact inf_le_right
      have hw := nonabelian_lowRank_of_larger_center h hn earlier F hne g hgP hgH hlt v hline
      exact .inr ⟨hw,step hw⟩
  · exact .inr ⟨hw,step hw⟩

open ChapterG.Section11

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
