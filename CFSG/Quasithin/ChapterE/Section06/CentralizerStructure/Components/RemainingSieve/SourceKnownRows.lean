module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceSieve
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.Sporadic.M12
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.Sporadic.HigmanSims
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.Sporadic.JankoFour
/-!
# E.6.8 with the completed M₁₂, HS and J₄ exclusions applied

The invariant local seed and original action theorems eliminate M₁₂, HS and
J₄ in the literal model/action branches of the complete E.6.8 dispatcher.
The characteristic-two, alternating, odd-linear and M₁₁ rows remain supplied
by SourceSieve. Only the six listed original sporadic source exclusions await
their producer; no block placement or residual-fixer conclusion is assumed
for any completed row.
Source: Aschbacher–Smith E.6.8, pp.247–248.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
open Chapter15.Section03.Candidates.ComponentStructure
open InvariantSubspaces.BlockSelection
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V U L : Subgroup G}

theorem adequateComponentAlternatives_of_six_sporadic_exclusions
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hsporadic : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G,
      ComponentIn (centralizer (A : Set G)) X → ¬ LieTypeComponent X →
      ∀ z ∈ sylowFixedSpace (T : Subgroup G) V, z ≠ 1 →
      ∀ α : MulAut X, (∀ x : X, (α x : G) = z * (x : G) * z⁻¹) →
      ∀ name : ClassificationModels.SporadicName,
      Nonempty ((X ⧸ pCore 2 X) ≃* name.Carrier) → TwoCentralInner α →
      (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .j2 ∨ name = .he ∨ name = .ru) → False)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    AdequateComponentAlternatives M V U (sylowCentralizer (T : Subgroup G) V) L := by
  apply adequateComponentAlternatives_of_sporadic_exclusion h ?_ hU hL
  intro A hA X hX hn z hz hne α hα name hnj hm ha hx
  have he := source_earlierLocalFacts h
  have h67 := e67Input_knownSimple h
  rcases (isExcludedSporadic_iff name).mp hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Sporadic.m12_excluded h he h67 hA hX hm.some
  · exact hsporadic A hA X hX hn z hz hne α hα .m22 hm ha (Or.inl rfl)
  · exact hsporadic A hA X hX hn z hz hne α hα .m23 hm ha (Or.inr (Or.inl rfl))
  · exact hsporadic A hA X hX hn z hz hne α hα .m24 hm ha (Or.inr (Or.inr (Or.inl rfl)))
  · exact hsporadic A hA X hX hn z hz hne α hα .j2 hm ha (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Sporadic.jankoFour_excluded h h67 hA hX hz α hα ha hm.some
  · exact Sporadic.higmanSims_excluded h h67 hA hX hz α hα ha hm.some
  · exact hsporadic A hA X hX hn z hz hne α hα .he hm ha
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact hsporadic A hA X hX hn z hz hne α hα .ru hm ha
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
