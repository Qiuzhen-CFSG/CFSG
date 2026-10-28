module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceMathieuRows
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.Sporadic.M24
/-!
# The original E.6.8 dispatcher after the M₂₄ exclusion

The actual M₂₄ component contradicts the completed E.6.7 source theorem
through its native invariant octad and sextet subgroups. This supplies
the M₂₄ branch of the original action dispatcher. Only M₂₂ and M₂₃ remain as explicit source-row inputs; the nonsporadic, M₁₂,
J₂, HS, J₄, Held and Rudvalis branches are already proved on the same original component.
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

theorem adequateComponentAlternatives_of_two_mathieu_exclusions
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hsporadic : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G,
      ComponentIn (centralizer (A : Set G)) X → ¬ LieTypeComponent X →
      ∀ z ∈ sylowFixedSpace (T : Subgroup G) V, z ≠ 1 →
      ∀ α : MulAut X, (∀ x : X, (α x : G) = z * (x : G) * z⁻¹) →
      ∀ name : ClassificationModels.SporadicName,
      Nonempty ((X ⧸ pCore 2 X) ≃* name.Carrier) → TwoCentralInner α →
      (name = .m22 ∨ name = .m23) → False)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    AdequateComponentAlternatives M V U (sylowCentralizer (T : Subgroup G) V) L := by
  apply adequateComponentAlternatives_of_mathieu_exclusions h ?_ hU hL
  intro A hA X hX hn z hz hne α hα name hm ha hx
  rcases hx with rfl | rfl | rfl
  · exact hsporadic A hA X hX hn z hz hne α hα .m22 hm ha (Or.inl rfl)
  · exact hsporadic A hA X hX hn z hz hne α hα .m23 hm ha (Or.inr rfl)
  · exact Sporadic.m24_excluded h (source_earlierLocalFacts h) (e67Input_knownSimple h) hA hX hm.some
end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
