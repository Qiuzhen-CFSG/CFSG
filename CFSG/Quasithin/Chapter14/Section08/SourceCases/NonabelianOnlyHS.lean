module

public import CFSG.Quasithin.Chapter14.Section08.SourceCases.NonabelianLocalTypes
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.StrongThreeExclusion.Recognition

/-!
# Only the original HS local type remains in the nonabelian source branch

The original invariant flag constructs either its marked G₂(3)-configuration
or its original HS type. Unconditional recognition of the original G₂
configuration now removes the strongly-three-embedded alternative. The HS
case retains the literal original seed and marked flag involution.

Source: Aschbacher--Smith 14.4.14 and I.4.5. The independent I.4.8 endpoint
construction is still required for the remaining HS local type.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases
open Subgroup Theory.GroupTheory ClassificationModels
open scoped IsMulCommutative
open Chapter12.Section02 Chapter12.Section08
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Section04 Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (earlier : Earlier1332CaseOneAt T)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d h earlier structural alternatives classification hne

/-- On the original nonabelian invariant flag, G₂(3) is recognized and
only the literal original HS local type remains. -/
theorem nonabelian_recognition_or_original_hs_at :
    IsG2At G 3 ∨ ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V := by
  rcases nonabelian_local_types_at d h earlier structural alternatives classification F hne with
    ⟨c, _, _⟩ | hs
  · exact Or.inl ⟨ZMod 3, inferInstance, inferInstance, Nat.card_zmod 3,
      ChapterI.Section04To05.G2Recognition.nonempty_mulEquiv_of_original_configuration c⟩
  · exact Or.inr hs

end CFSG.Quasithin.Chapter14.Section08.SourceCases
