module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.ExchangedModel.Interchange
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.ExchangedModel.OriginalCubic

/-!
# Component interchange and the exchanged lift

The original marked A₅ action gives at least sixteen fixed elements of D
for each cubic actor in K₀. The literal residual matrix image has two-group
kernel, so the cubic witness in the factor-preserving alternative lifts to
such an actor. The joint-core bound forces at least four fixed elements in
Uˣ, contradicting the factor-preserving witness's fixed subgroup of order
at most two. Thus z interchanges the two actual matrix-factor images.

The final theorem includes the commutator image of order sixteen, its
invariant interval for the original K₀, and the application of
`symmetric_lift_of_exchanged_moved_section` to the common D. Only earlier
case-(3) and selection coordinates, the common-core identity, and |D|=64
remain explicit. In particular no cubic count, interchange, exchanged
moved-section conclusion, normalization, or fixed-line conclusion is assumed.
The selection producer owns the two action markings; the SymmetricLocal
source assembly owns the earlier common-core premises and the rest of the
source lemma.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ExchangedModel
open ClassicalOrthogonal.FourPlusMatrix
variable {G : Type*} [Group G] [Finite G]

/-- The original marked action discharges the cubic fixed-point premise of
the component-interchange argument. -/
theorem swaps_of_marked_actions
    (U : Subgroup G) [IsExtraspecial 2 U] (z x : G)
    (hz : orderOf z = 2) (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U) (hUcard : Nat.card U = 512)
    (hiz : conjugateElement z x ∈ centralizer ({z} : Set G))
    (hDcard : Nat.card (centralizerLift U z (conjugateElement z x)) = 64)
    (hDcore : (centralizer ({z} : Set G) ⊓
      centralizer ({conjugateElement z x} : Set G)).pCoreIn 2 =
        centralizerLift U z (conjugateElement z x))
    (m : CaseThreeAction (centralizer ({conjugateElement z x} : Set G)) (conjugateCore U x))
    (d : OriginalMovedAction U z (conjugateElement z x)) :
    Binary.InvolutionResidual.SwapsFactors (m.action
      ⟨z, mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hiz).symm⟩) := by
  apply swaps_of_original_cubic_bound U z x hz hZ hUcore hUcard hiz hDcard hDcore m d
  exact d.sixteen_le_fixed_card hz
    (common_lift_elementary U z x hz hZ hUcore hUcard hiz hDcard hDcore m d) hDcard

/-- The exchanged component calculation and its actual symmetric-lift
application, with the original residual, literal quotient map, and x⁻¹zx
convention. These are the local symmetry conclusions on printed p.1010. -/
theorem exchanged_components_and_symmetric_lift
    (U : Subgroup G) [IsExtraspecial 2 U] (z x : G)
    (hz : orderOf z = 2) (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U) (hUcard : Nat.card U = 512)
    (hiz : conjugateElement z x ∈ centralizer ({z} : Set G))
    (hDcard : Nat.card (centralizerLift U z (conjugateElement z x)) = 64)
    (hDcore : (centralizer ({z} : Set G) ⊓
      centralizer ({conjugateElement z x} : Set G)).pCoreIn 2 =
        centralizerLift U z (conjugateElement z x))
    (m : CaseThreeAction (centralizer ({conjugateElement z x} : Set G)) (conjugateCore U x))
    (d : OriginalMovedAction U z (conjugateElement z x)) :
    Binary.InvolutionResidual.SwapsFactors (m.action
      ⟨z, mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hiz).symm⟩) ∧
    Nat.card (((⁅conjugateCore U x, zpowers z⁆).subgroupOf (conjugateCore U x)).map
      (QuotientGroup.mk' (center (conjugateCore U x)))) = 16 ∧
    (∀ E : Subgroup G, zpowers (conjugateElement z x) ≤ E →
      E ≤ liftBase (conjugateCore U x) (conjugateElement z x) z →
      diagonalResidual (centralizer ({z} : Set G)) (conjugateElement z x) ≤
        normalizer (E : Set G) →
      E = zpowers (conjugateElement z x) ∨
        E = liftBase (conjugateCore U x) (conjugateElement z x) z) ∧
    centralizerLift (conjugateCore U x) (conjugateElement z x) z =
      centralizerLift U z (conjugateElement z x) ∧
    conjugateCore U x ≤ normalizer (centralizerLift U z (conjugateElement z x) : Set G) ∧
    centralizerLift U z (conjugateElement z x) ⊓ centralizer (conjugateCore U x : Set G) =
      zpowers (conjugateElement z x) := by
  obtain ⟨hmoved, hirr⟩ :=
    exchanged_moved_section U z x hz hZ hUcore hUcard hiz hDcard hDcore m d.nonsolvable
  exact ⟨swaps_of_marked_actions U z x hz hZ hUcore hUcard hiz hDcard hDcore m d,
    hmoved, hirr,
    symmetric_lift_of_exchanged_moved_section U z x hz hZ hUcore hiz hDcard hDcore
      hmoved hirr⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ExchangedModel
