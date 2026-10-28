module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.CounterexampleC28
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.SectionKernel
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.ClosureSylow
import Mathlib.Tactic
/-!
# The characteristic-two section kernel in the original C.2.12 reduction

The actual C.2.8 data restricts to the normalizer of M0. Its section
centralizer has no odd core and no ordinary component. The C.1.29 source
then excludes any chi-block outside M; perfect-action transport supplies the
needed commutator vanishing without assuming a new block classifier.

Source: Aschbacher–Smith, C.2.10–12, printed pp.147–149.
-/
public section
namespace CFSG.Quasithin.Chapter4.Section02.Unitary
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The original odd-actor counterexample supplies the actual radical and
characteristic-two section centralizer required by C.2.12. -/
theorem chosen_oddActorResidual_section_kernel {K : GroupClass} {T : Sylow 2 G}
    {L V : Subgroup G}
    (h : Chapter12.Section02.Hypothesis1221 K T L)
    (D : Chapter12.Section02.ChosenModule T L V)
    (B : Subgroup G) (hBN : B ≤ normalizer (L : Set G))
    (hcomm : ⁅B,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card B))
    (hBV : B ≤ centralizer (V : Set G))
    (hM : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)))
    (hnot : ¬ UniqueMaximalOvergroup (Section04.oddActorResidual L B)
      (normalizer (L : Set G))) :
    ∃ J H W : Subgroup G,
      IsMaximalTwoLocal H ∧ H ⊓ normalizer (L : Set G) < H ∧
      let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let MH := H ⊓ normalizer (L : Set G)
      let X := ChapterA.Section04.twoSectionCentralizer (conjugateSpanBy LH MH) H
      ChapterC.HypothesisC28 K H MH LH (J.pCoreIn 2) W ∧
      pPrimeCore 2 H = ⊥ ∧ IsPRadical 2 ((J.pCoreIn 2).subgroupOf H) ∧
      ChapterC.IsSylowInNormalClosure (J.pCoreIn 2) MH ∧
      generalizedFitting X = pCore 2 X ∧
      (∃ S : Sylow 2 X, (S : Subgroup X).map X.subtype = J.pCoreIn 2) ∧
      ∃ c : sectionCentralizerIn (normalizer (L : Set G)) L,
        V.map (MulAut.conj (c : G)).toMonoidHom ≤ W := by
  obtain ⟨J,H,S,_,hH,_,hlt,hC,c,_,hV⟩ :=
    chosen_oddActorResidual_C28 h D B hBN hcomm hodd hBV hM hnot
  exact ⟨J,H,_,hH,hlt,hC,hC.oddCore_eq_bot,hC.isRadical,hC.sylow_in_normalClosure,
    hC.section_fitting_eq_core,hC.section_sylow_in_H,c,hV⟩
end CFSG.Quasithin.Chapter4.Section02.Unitary
