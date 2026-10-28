module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives.Transport
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection.PointGeometry.InverseSimilarity

/-!
# The actual outer action excludes repeated natural modules

The faithful plus actor is S₈, by the marked A₈ component, its trivial
centralizer, and the given nontrivial outer Tᵥ action. Every permutation is
conjugate to its inverse, so each operator on an invariant space or quotient
is similar to its inverse. The concrete SL₄(2) polynomial obstruction from
InverseSimilarity rules this out on the natural module and every positive
number of repeated natural copies.

The imported obstruction is an intrinsic two-matrix calculation, independent
of any Chapter 15 source conclusion. Both the original moved central quotient
and B.5.1's iterated quotient are retained, without splitting fixed kernels.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), the paragraph
following 13.6.23, printed p.933/PDF p.950; B.5.1(1i,1iv), pp.99–103.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives
open ComponentSelection
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.MiddleEight.Selection.PointGeometry
variable {G : Type*} [Group G] [Finite G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 8))
    (hT : IsPGroup 2 (Tv T v)) (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K))

include hK hLK e hT hcore hout

omit [Finite G] in
/-- The quotient's full plus action excludes the binary four-dimensional natural row. -/
theorem component_not_linearNatural :
    ¬ IsLinearNatural (s.action.comp (plusImage K L T z v hL hz K).subtype) BinaryField.two 4 := by
  obtain ⟨E, _, _⟩ := exists_marked_symmetricEquiv K L T z v hL hz hK hLK e hT hcore hout
  rintro ⟨f⟩
  exact natural_not_inverseSimilar (inverseSimilar_transport f
    (inverseSimilar_of_symmetric_extension s.action (plusImage K L T z v hL hz K).subtype E))

omit [Finite G] in
/-- The same outer action excludes every positive multiplicity on the actual upper space. -/
theorem component_not_repeatedNatural_upper (r : ℕ) (hr : 0 < r) :
    ¬ IsRepeatedLinearNatural
      (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype) BinaryField.two 4 r := by
  obtain ⟨E, _, _⟩ := exists_marked_symmetricEquiv K L T z v hL hz hK hLK e hT hcore hout
  rintro ⟨f⟩
  exact repeated_not_inverseSimilar r hr (inverseSimilar_transport f
    (inverseSimilar_of_symmetric_extension s.space.toRepresentation
      (plusImage K L T z v hL hz K).subtype E))

/-- The B.5.1 natural quotient is excluded after identifying its complete fixed kernel. -/
theorem classified_not_linearNatural (hY : K ∈ Yz L T z v)
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype) ⊤) :
    ¬ IsLinearNatural
      (c.sectionData.action.comp (⊤ : Subgroup (plusImage K L T z v hL hz K)).subtype)
      BinaryField.two 4 := by
  rintro ⟨f⟩
  let : IsQuasisimple (plusImage K L T z v hL hz K) :=
    plusImage_K_quasisimple K L T z v hL hz hY hcore
  exact component_not_linearNatural K L T z v hL hz hK hLK e hT hcore hout s
    ⟨quotientCoordinates_of_iterated _ _ s c.sectionData f⟩

/-- The B.5.1 repeated-natural upper space is excluded with its actual ambient extension. -/
theorem classified_not_repeatedNatural (hY : K ∈ Yz L T z v)
    (c : ProjectiveLine.QuasisimpleSourceConclusion
      (s.space.toRepresentation.comp (plusImage K L T z v hL hz K).subtype) ⊤)
    (r : ℕ) (hr : 0 < r) :
    ¬ IsRepeatedLinearNatural
      (show Representation (ZMod 2)
        (⊤ : Subgroup (plusImage K L T z v hL hz K)) c.sectionData.space.toSubmodule from
        c.sectionData.space.toRepresentation.comp (⊤ : Subgroup (plusImage K L T z v hL hz K)).subtype)
      BinaryField.two 4 r := by
  rintro ⟨f⟩
  let : IsQuasisimple (plusImage K L T z v hL hz K) :=
    plusImage_K_quasisimple K L T z v hL hz hY hcore
  exact component_not_repeatedNatural_upper K L T z v hL hz hK hLK e hT hcore hout s r hr
    ⟨upperCoordinates_of_iterated _ _ s c.sectionData f⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Alternatives
