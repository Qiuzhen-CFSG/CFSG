module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.FixedLineActions
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.ExchangedNatural

/-!
# Selecting actual constituent actions on the original large flag

Construct the original marked terminal action and apply both G.11 fixed-point
clauses. The low-rank clause already supplies the G.11 catalogue. In the
fixed-line clause, select a moved component and its original homogeneous
constituent. A constituent containing the marked point has one of the three
proved concrete doubled actions, and the two permutation rows have faithful
whole-group tensor embeddings. Otherwise the selected constituent retains its
literal exchange, half-point and full-center geometry.

The remaining exchanged recognition, identification of the whole ambient
images and conversion to the marked 14.4.2 catalogue are still required.
This reduction adds no classification premise to the original source inputs.
Source: Aschbacher--Smith G.11.6--8 and 14.4.2, printed pp.365--369,1006--1007.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Both fixed-point clauses on the original large extraspecial flag, now
with selected constituents and actual marked-branch action coordinates. -/
theorem source_large_catalogue_or_fixed_line_actions (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
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
      (ChapterG.Section11.Conclusion F.terminalRepresentation B (F.terminalDot (F.X g)) ∨
        (¬ ChapterG.Section11.LowRankWitness F.terminalRepresentation v (F.terminalDot (F.X g)) ∧
          FixedLineModuleData F.terminalRepresentation B v (F.terminalDot (F.X g)) ∧
          FixedLineActions.ConstituentReduction F.terminalRepresentation B v
            (hatSpace F (F.E g)) (F.terminalDot (F.X g)))) := by
  obtain ⟨heU,heX,B,v,hyp,hline,hS,hcases⟩ := source_large_catalogue_or_fixed_line d earlier hq
    chosen structural alternatives classification F hne hZ hlarge g hgP hgH
  let := heU
  let := heX
  refine ⟨heU,heX,B,v,hyp,hline,hS,?_⟩
  rcases hcases with ⟨hn,_,_,_,_,hmodule⟩ | hcatalogue
  · exact Or.inr ⟨hn,hmodule,source_large_fixed_line_constituent_reduction d earlier hq chosen
      structural alternatives classification F hne hZ hlarge g hgP hgH hyp hline hn⟩
  · exact Or.inl hcatalogue

end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge
