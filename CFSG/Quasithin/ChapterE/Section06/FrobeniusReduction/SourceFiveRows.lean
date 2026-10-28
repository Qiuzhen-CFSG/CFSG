module
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceCommonBound
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.RemainingSieve.SourceFiveRows
/-!
# E.6.3 with the proved E.6.8 source rows supplied

The full original minimum and common-normal source route use the adequate
E.6.8 dispatcher on the actual centralizer component. Its Lie, alternating,
odd-linear, M₁₁, M₁₂, J₂, HS and J₄ branches are proved. The five remaining
sporadic source exclusions are kept with their original marked actor and
two-core quotient. E.6.18 and recognition of the further E.6.23 component
remain the other two independent source inputs.
Source: Aschbacher–Smith E.6.3 and E.6.8, printed pp.245,247–248.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
open Components Components.RemainingSieve Hyperplanes Hyperplanes.Enlargement
open Chapter15.Section03.Candidates.ComponentStructure
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V : Subgroup G}

theorem lower_bound_knownSimple_of_five_sporadic_exclusions [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (hm : 2 < localM V)
    (h18 : SevenExcluded M V)
    (hquot : SixAutomorphisms.ModelIdentification.QuotientRecognition T M V)
    (hsporadic : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G,
      ComponentIn (centralizer (A : Set G)) X → ¬ LieTypeComponent X →
      ∀ z ∈ sylowFixedSpace (T : Subgroup G) V, z ≠ 1 →
      ∀ α : MulAut X, (∀ x : X, (α x : G) = z * (x : G) * z⁻¹) →
      ∀ name : ClassificationModels.SporadicName,
      Nonempty ((X ⧸ pCore 2 X) ≃* name.Carrier) → TwoCentralInner α →
      (name = .m22 ∨ name = .m23 ∨ name = .m24 ∨ name = .he ∨ name = .ru) → False)
    : (localM V : ℕ∞) ≤ globalR V ∧
      globalS V = (localM V : ℕ∞) ∧ 2 < globalS V := by
  exact lower_bound_knownSimple_of_remaining_models h hm h18
    (fun A hA X hX => adequateComponentAlternatives_of_five_sporadic_exclusions
      h hsporadic hA hX) hquot
end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
