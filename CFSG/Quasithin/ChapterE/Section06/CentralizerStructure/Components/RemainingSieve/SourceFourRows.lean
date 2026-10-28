module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceFiveRows
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.Sporadic.Held
/-!
# The original E.6.8 dispatcher after the Held exclusion

The actual Held component and marked involution now contradict the completed
E.6.7 source theorem through the native invariant local seed. This supplies
the Held branch of the original action dispatcher. Only M₂₂, M₂₃, M₂₄
and Rudvalis remain as explicit source-row inputs; the nonsporadic, M₁₂,
J₂, HS and J₄ branches are already proved on the same original component.
Source: Aschbacher–Smith E.6.8, printed pp.247–248.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
open Chapter15.Section03.Candidates.ComponentStructure
open InvariantSubspaces.BlockSelection
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V U L : Subgroup G}

theorem adequateComponentAlternatives_of_four_sporadic_exclusions
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hsporadic : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G,
      ComponentIn (centralizer (A : Set G)) X → ¬ LieTypeComponent X →
      ∀ z ∈ sylowFixedSpace (T : Subgroup G) V, z ≠ 1 →
      ∀ α : MulAut X, (∀ x : X, (α x : G) = z * (x : G) * z⁻¹) →
      ∀ name : ClassificationModels.SporadicName,
      Nonempty ((X ⧸ pCore 2 X) ≃* name.Carrier) → TwoCentralInner α →
      (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .ru) → False)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    AdequateComponentAlternatives M V U (sylowCentralizer (T : Subgroup G) V) L := by
  apply adequateComponentAlternatives_of_five_sporadic_exclusions h ?_ hU hL
  intro A hA X hX hn z hz hne α hα name hm ha hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact hsporadic A hA X hX hn z hz hne α hα .m22 hm ha (Or.inl rfl)
  · exact hsporadic A hA X hX hn z hz hne α hα .m23 hm ha (Or.inr (Or.inl rfl))
  · exact hsporadic A hA X hX hn z hz hne α hα .m24 hm ha (Or.inr (Or.inr (Or.inl rfl)))
  · exact Sporadic.held_excluded h (e67Input_knownSimple h) hA hX hz α hα ha hm.some
  · exact hsporadic A hA X hX hn z hz hne α hα .ru hm ha
      (Or.inr (Or.inr (Or.inr rfl)))
end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
