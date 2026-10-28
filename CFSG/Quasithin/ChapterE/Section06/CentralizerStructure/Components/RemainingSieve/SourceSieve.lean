module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Adequate
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Assembly
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.AlternatingActions
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.OddActions
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SporadicLocals
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.SourceOvergroups
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.SourceLocal
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.Source115
/-!
# The full five-way E.6.8 dispatcher with earlier sources discharged

The original 1.1.5 model/action theorem is applied to the actual centralizer
component. Complete E.6.7 and 1.2.1(3) supply the Lie sieve; the alternating
and odd-action calculations supply their exact source alternatives. The full
Borel, symplectic and alternating records are retained, with the adequate
linear-four and odd tuples used by the later E.6 consumers.

The only remaining family is the nine sporadic exclusions, retaining the
actual two-core quotient, original marked action and source subgroup. Its
owner constructs the invariant local subgroups and proves their contradiction;
no arbitrary quotient model, block-placement or final sieve conclusion is
assumed in their place. Source: Aschbacher–Smith E.6.8, pp.247–248.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
open Chapter1.Section02.LocalModels
open Chapter15.Section03.Candidates.ComponentStructure
open InvariantSubspaces.BlockSelection
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V U L : Subgroup G}

theorem adequateComponentAlternatives_of_sporadic_exclusion
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hsporadic : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G,
      ComponentIn (centralizer (A : Set G)) X → ¬ LieTypeComponent X →
      ∀ z ∈ sylowFixedSpace (T : Subgroup G) V, z ≠ 1 →
      ∀ α : MulAut X, (∀ x : X, (α x : G) = z * (x : G) * z⁻¹) →
      ∀ name : ClassificationModels.SporadicName, name ≠ .j3 →
      Nonempty ((X ⧸ pCore 2 X) ≃* name.Carrier) → TwoCentralInner α →
      IsExcludedSporadic name → False)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    AdequateComponentAlternatives M V U (sylowCentralizer (T : Subgroup G) V) L := by
  classical
  have he := source_earlierLocalFacts h
  by_cases hl : LieTypeComponent L
  · rcases LieSieve.adequate_alternatives h he (e67Input_knownSimple h)
      (fun _ hH _ hB => source_cComponent_orbits_and_models h hH hB) hU rfl hL hl with
      hb | hs | h4 | ho
    · exact Or.inl hb
    · exact Or.inr (Or.inl hs)
    · exact Or.inr (Or.inr (Or.inl h4))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ho)))
  obtain ⟨z,hz,hne,_,_,α,hconj,hm⟩ := exists_source_model_action h he source_earlier115Three hU hL
  cases hm with
  | lie hs hm hi =>
      apply (hl ?_).elim
      rcases hm with hb | hr | ⟨n,hn,hlin⟩
      · exact Or.inl hb
      · exact Or.inr (Or.inl hr)
      · rcases hn with rfl | rfl
        · exact Or.inr (Or.inr (Or.inl hlin))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hlin)))
  | two_cover hn hc hm hi =>
      apply (hl ?_).elim
      refine Or.inr (Or.inr (Or.inr (Or.inr ⟨?_,?_⟩)))
      · rw [hc]; exact pCore_isPGroup
      · let e := QuotientGroup.quotientMulEquivOfEq hc
        exact hm.elim (fun hq => Or.inl (hq.of_mulEquiv e))
          (fun hq => Or.inr (hq.of_mulEquiv e))
  | six σ hs ha =>
      exact Or.inr (Or.inr (Or.inr (Or.inl
        (AlternatingActions.alternating_of_six_action h he hU hL hl hz hconj hs ha))))
  | seven σ hs ha =>
      exact Or.inr (Or.inr (Or.inr (Or.inl
        (AlternatingActions.alternating_of_seven_action h he hU hL hz hconj hs ha))))
  | odd hm hi =>
      exact Or.inr (Or.inr (Or.inr (Or.inr
        (OddActions.adequate_of_odd_action h he hU hL hl hz hconj hm hi))))
  | sporadic name hnj hm ha =>
      by_cases hn : name = .m11
      · subst name
        exact Or.inr (Or.inr (Or.inr (Or.inr
          (OddActions.adequate_of_m11_action h he hU hL hz hconj hm ha))))
      · have hx : IsExcludedSporadic name := by
          cases name <;> first | exact (hn rfl).elim | exact (hnj rfl).elim | trivial
        exact (hsporadic U hU L hL hl z hz hne α hconj name hnj hm ha hx).elim
end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
