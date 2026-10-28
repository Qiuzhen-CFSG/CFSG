module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Setup

/-!
# Elementwise conjugate tests for the upper interval bound

Every element of a normal elementary subgroup is an involution and its
identity and generator conjugates commute pairwise. A pointwise exclusion
placing each such element in the literal kernel or envelope therefore puts
any whole subgroup outside the kernel in the envelope. The elementwise
exclusion itself remains an independent presentation calculation.

Source: elementary normal-subgroup theory applied to the fixed presentation;
Aschbacher–Smith A.3.12, pp.47–48. See `source/README.md` for the distinction
between pairwise commutation and the insufficient single-conjugate test.
-/

@[expose] public section
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
open Janko4.LocalStructure.SylowNormalEights Presentation

/-- The identity and the twenty-one actual generator conjugates. -/
def conjugateTest (x : Carrier) : Option (Fin 21) → Carrier
  | none => x
  | some i => (generator i)⁻¹ * x * generator i

/-- All pairs of these conjugates commute, in the actual presented group. -/
def PairwiseConjugateCommutation (x : Carrier) : Prop :=
  ∀ i j : Option (Fin 21), Commute (conjugateTest x i) (conjugateTest x j)

/-- The finite, elementwise exclusion needed for the upper interval bound. -/
def PointwiseExclusion : Prop :=
  ∀ x : Carrier, x ^ 2 = 1 → PairwiseConjugateCommutation x →
    x ∈ abstractKernel ∨ x ∈ envelope

/-- Normal elementary subgroups satisfy every test, including pairs of conjugates. -/
theorem conjugateTests_commute_of_normal_elementary (A : Subgroup Carrier)
    (hn : A.Normal) (he : IsElementaryAbelian 2 A) {x : Carrier} (hx : x ∈ A) :
    PairwiseConjugateCommutation x := by
  let _ := he
  have hm : ∀ i, conjugateTest x i ∈ A := by
    intro i
    cases i with
    | none => exact hx
    | some i => exact hn.conj_mem' x hx (generator i)
  intro i j
  exact congrArg Subtype.val
    (mul_comm (⟨conjugateTest x i, hm i⟩ : A) (⟨conjugateTest x j, hm j⟩ : A))

/-- A subgroup contained in a union of two subgroups is contained in one of them. -/
theorem envelope_bound_of_pointwise (hp : PointwiseExclusion)
    (A : Subgroup Carrier) (hn : A.Normal) (he : IsElementaryAbelian 2 A)
    (hout : ¬ A ≤ abstractKernel) : A ≤ envelope := by
  let _ := he
  have h : (A : Set Carrier) ⊆ (abstractKernel : Set Carrier) ∪ (envelope : Set Carrier) := by
    intro x hx
    exact hp x (elemPow_eq_one_of_isElementaryAbelian x hx)
      (conjugateTests_commute_of_normal_elementary A hn he hx)
  exact (SubgroupClass.subset_union.mp h).resolve_left hout

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
