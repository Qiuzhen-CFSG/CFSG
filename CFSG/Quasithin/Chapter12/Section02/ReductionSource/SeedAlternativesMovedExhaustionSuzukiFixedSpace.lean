module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedExhaustionComplementaryDisplacement
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionSuzukiFixedSpace

/-!
# The literal Suzuki pair after removing its actor centralizer

The original normalizer action has trivial two-core. Thompson A×B therefore
keeps the exchanged support faithful on the fixed space of its actual
centralizer in the starred actor. The reduced actor has that exact kernel,
rank at most 2r+2, and fixed codimension at most 2(2r+2).

All premises come from the original odd-degree natural chosen seed and its
strict normalizer enlargement. No ambient irreducibility or full component
movement is assumed. The remaining small-action Suzuki exclusion, FF
branches, U = W and original Source325 assembly remain with qt-baumann-fsu.
Source: Aschbacher--Smith D.3.9(2), pp.200--201, and3.2.5, p.580.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Every original starred actor has a faithful exchanged Suzuki support on
its literal centralizer fixed space, with the exact reduced kernel and budget. -/
theorem normalizer_suzuki_fixedSpace_budget_of_odd_linearThree
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G))
    (hne : componentOrbit V (normalizer (L : Set G)) ≠ componentOrbit V (T : Subgroup G))
    (F : BinaryField) (ho : Odd F.degree)
    (e : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype) (linearNatural F 3)) :
    let := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      ∃ (J : Subgroup (internalActionImage M U hn)) (r : ℕ),
        IsComponent (internalActionImage M U hn) J ∧ 0 < r ∧
        Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup r) ∧
        ∃ a ∈ A, a ∉ normalizer (J : Set (internalActionImage M U hn)) ∧
          (normalizer (J : Set (internalActionImage M U hn))).index = 2 ∧
          componentOrbit J A = J ⊔ J.map (MulAut.conj a).toMonoidHom ∧
          (let X := componentOrbit J A
           let B := A ⊓ centralizer (X : Set (internalActionImage M U hn))
           let W := fixedSpace ρ B
           X.Normal ∧ subspaceKernel ρ W X = ⊥ ∧
             (∃ hXW : X ≤ subspaceStabilizer ρ W,
               Function.Injective (subgroupActionHom ρ W X hXW)) ∧
             subspaceKernel ρ W A = B ∧
             rank (restrictedSubgroup ρ W A) ≤ 2*r+2 ∧
             restrictedSubgroup ρ W A ∈ Qhat (subspaceImageRepresentation ρ W) ∧
             fixedCodim (subspaceImageRepresentation ρ W) (restrictedSubgroup ρ W A) ≤ 2*(2*r+2) ∧
             (B ≠ ⊥ → actionRatio (subspaceImageRepresentation ρ W)
               (restrictedSubgroup ρ W A) < cubicRatio ρ)) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  intro hU M U hn ρ A hAS hA
  obtain ⟨J,hJ,_,r,hr,⟨eJ⟩,a,ha,han,hi,horbit⟩ :=
    D.normalizer_starred_support_suzuki_pair_of_odd_linearThree h hmany hc hm hne F ho e A hAS hA
  exact ⟨J,r,hJ,hr,⟨eJ⟩,a,ha,han,hi,horbit,
    exchanged_support_fixedSpace_reduction ρ (UniqueFactor.imageRepresentation_injective M U hn)
      (D.normalizerActor_twoCore_eq_bot h.toHypothesis1221) J A hi a ha han horbit hA r hr eJ⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
