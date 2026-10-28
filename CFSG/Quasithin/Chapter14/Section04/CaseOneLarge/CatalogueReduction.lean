module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLine
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Nonsolvable
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.FullLinearExclusion

/-!
# Both source branches before large-action recognition

Apply the corrected low-rank G.11 reduction to the original terminal action.
The ambient seed excludes its exceptional full-linear S₈ row, and the large
extraspecial order excludes the solvable remainder. The other clause of
G.11.1(3) supplies a fixed line, the exact half-dimension rank equalities and
faithful action of the original actor on E.

The final reduction constructs the marked G.10 data and relative Sylow
normality from the original hypotheses. Fixed-line recognition, the remaining
low-rank component recognition, and conversion of the G.11 rows into the
marked 14.4.2 catalogue remain open. No catalogue or recognition premise is
introduced here.

Source: Aschbacher--Smith, G.11.1--7, 14.3.13 and 14.4.1--2,
printed pp.364--367,993--994,1006--1007; the G.10.15 correction is recorded in
`docs/quasithin-proof-basis.md`.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The corrected low-rank reduction on the original large extraspecial
flag has neither a solvable remainder nor the exceptional S₈ row. The
remaining component recognitions are explicit outputs, not hypotheses. -/
theorem source_large_lowRank_reduction (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat)
    (hyp : ChapterG.Section10.Hypothesis F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g))
      ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))))
    (hfix : ∀ t ∈ F.terminalDot (T : Subgroup G), F.terminalRepresentation t v = v)
    (hw : ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))) :
    ChapterG.Section11.Conclusion F.terminalRepresentation B (F.terminalDot (F.X g)) ∨
      (IsIrreducible F.terminalRepresentation ∧
        6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        ChapterG.Section11.ExchangedRecognition.RemainingComponentModels F.terminalRepresentation B v
          (hatSpace F (F.E g)) (F.terminalDot (F.X g))) := by
  have hS : ChapterG.Section11.NormalSylow F.terminalRepresentation v
      (F.terminalDot (F.X g)) :=
    ⟨_,hfix,source_terminal_actor_normal_in_sylow d earlier hq chosen structural alternatives
      F hne g hgP hgH⟩
  rcases ChapterG.Section11.ExchangedRecognition.corrected_conclusion_or_remaining hyp
    (source_terminal_cover F d chosen) hw hS with (hc | hex) | ⟨hi,hd,hs | hn⟩
  · exact Or.inl hc
  · exact (CaseOneHS.source_no_full_linear_alternative d earlier hq chosen structural alternatives
      F hne B v _ _ _ hex).elim
  · exact (source_large_terminal_not_solvable d earlier hq chosen structural alternatives
      F hne hZ hlarge hs.1).elim
  · exact Or.inr ⟨hi,hd,hn.2⟩

/-- A source reduction covering both clauses of G.11.1(3). The fixed-line
branch carries its derived half-dimension and faithful actor action; the
other branch uses the corrected reduction with its exceptional row excluded.
Neither branch assumes recognition or catalogue exhaustiveness. -/
theorem source_large_catalogue_reduction (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (hZ : F.ZU = F.Vi 1) (hlarge : 64 < Nat.card F.U)
    (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    ∃ heU : IsElementaryAbelian 2 F.Uhat, letI := heU
    ∃ heX : IsElementaryAbelian 2 (F.terminalDot (F.X g)), letI := heX
    ∃ (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)) (v : Additive F.Uhat),
      ChapterG.Section10.Hypothesis F.terminalRepresentation B v
        (hatSpace F (F.E g)) (F.terminalDot (F.X g))
        ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g))) ∧
      Submodule.span (ZMod 2) {v} = hatSpace F (F.Vi 2) ∧
      ChapterG.Section11.NormalSylow F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
      ((¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
          fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) = hatSpace F (F.Vi 2) ∧
          2 * finrank (ZMod 2) (hatSpace F (F.E g)) = finrank (ZMod 2) (Additive F.Uhat) ∧
          Group.rank (F.terminalDot (F.X g)) + 1 = finrank (ZMod 2) (hatSpace F (F.E g)) ∧
          ∀ a b : F.terminalDot (F.X g),
            (∀ w : hatSpace F (F.E g),
              F.terminalRepresentation a w = F.terminalRepresentation b w) → a = b) ∨
        ChapterG.Section11.Conclusion F.terminalRepresentation B (F.terminalDot (F.X g)) ∨
        (IsIrreducible F.terminalRepresentation ∧
          6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
          ChapterG.Section11.ExchangedRecognition.RemainingComponentModels
            F.terminalRepresentation B v (hatSpace F (F.E g)) (F.terminalDot (F.X g)))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hfix⟩ :=
    source_terminal_marked_hypothesis F d earlier hq chosen structural alternatives hne g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,?_,?_⟩
  · exact ⟨_,hfix,source_terminal_actor_normal_in_sylow d earlier hq chosen structural alternatives
      F hne g hgP hgH⟩
  by_cases hw : ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g))
  · exact Or.inr (source_large_lowRank_reduction d earlier hq chosen structural alternatives
      F hne hZ hlarge g hgP hgH B v hyp hfix hw)
  · exact Or.inl ⟨hw,source_terminal_ranks_of_no_lowRank d earlier hq chosen structural alternatives
      F hne hZ g hgP hgH v hline hw⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
