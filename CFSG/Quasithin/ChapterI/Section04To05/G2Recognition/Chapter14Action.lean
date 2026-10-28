module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneDimensionFour.LocalReduction
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.LocalStructure

/-!
# Full action on the actual Chapter 14 elementary seed

The genuine selected-counterexample setup supplies the natural L-action
and its centralizer. The remaining source equality V = O₂(L) then identifies
that seed with the literal core, including its conjugation action. Applying
the elementary-eight generalized-Fitting calculation proves surjectivity
onto Aut(O₂(L)) and order 192 for every nonidentity core-point centralizer.

This discharges the local full-action calculation on the actual Chapter 14
subgroup; it does not discharge the I.4.5 recognition callback. That theorem
remains with `qt-i45-g2-recognition`. The explicit `SourceLocalData` premise
is owned by `qt-d-14414-g2-source`, which absorbed the former local-source
task and retains final assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
14.4.3–5, printed pp.1007–1008, and §I.4(G2), printed p.417.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource Chapter14.Section04.CaseOneGeometry
open Chapter14.Section04.CaseOneDimensionFour
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

theorem source_seed_full_action (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (F : InvariantFlag T V 3) (localData : SourceLocalData L F) :
    Function.Surjective (MulAut.conjNormal : L →* MulAut (pCore 2 L)) ∧
    ∀ x : pCore 2 L, x ≠ 1 →
      Nat.card (centralizer ({(x : L)} : Set L)) = 192 := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  have hVL : V ≤ L := localData.seed_core.le.trans (L.pCoreIn_le 2)
  have hVcore : V.subgroupOf L = pCore 2 L := by
    apply (map_injective L.subtype_injective)
    rw [map_subgroupOf_eq_of_le hVL]
    exact localData.seed_core
  let eV : pCore 2 L ≃* V :=
    (MulEquiv.subgroupCongr hVcore.symm).trans (subgroupOfEquivOfLe hVL)
  let : IsElementaryAbelian 2 (pCore 2 L) :=
    IsElementaryAbelian.of_injective eV.toMonoidHom eV.injective
  have hcard : Nat.card (pCore 2 L) = 8 := by
    rw [Nat.card_congr eV.toEquiv]
    simpa [F.last] using F.card 3 (by decide)
  have hcentral : centralizer (pCore 2 L : Set L) ≤ pCore 2 L := by
    intro x hx
    rw [← hVcore]
    change (x : G) ∈ V
    rw [localData.seed_core, ← h.centralizer_L]
    refine ⟨x.property, ?_⟩
    intro v hv
    have hv' : (⟨v, hVL hv⟩ : L) ∈ pCore 2 L := by rw [← hVcore]; exact hv
    exact congrArg L.subtype (hx ⟨v, hVL hv⟩ hv')
  have hfit : pCore 2 L = generalizedFitting L :=
    (generalizedFitting_eq_pCore_of_selfCentralizing 2 hcentral).symm
  let e : (L ⧸ pCore 2 L) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) :=
    h.naturalMarking.quotientEquiv.trans
      (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)).symm
  have hquot : Nat.card (L ⧸ pCore 2 L) = 168 :=
    (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  exact ⟨GeneralizedFittingEight.conjugation_surjective (pCore 2 L) hfit hcard hquot,
    GeneralizedFittingEight.point_centralizer_card (pCore 2 L) hfit hcard hquot⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
