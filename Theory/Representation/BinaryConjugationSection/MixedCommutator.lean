module
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryConjugationSection.FixedImage
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan

/-!
# Mixed commutators in a literal binary section

Cross-factor fixation in the coordinate action places the original mixed
group commutator in the exact coordinate kernel. Applying this to an invariant
subspace and its quotient preserves both layers of a group filtration.
Source application: Aschbacher--Smith 12.6.33(a), printed pp.837--838.
-/

public section
open Subgroup Representation.BinaryOffender
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H U Z : Subgroup G}
  {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) H V}

/-- Crossed movement in the actual coordinates kills the original mixed
commutator modulo the prescribed denominator. -/
theorem mixed_commutator_le_kernel (c : BinaryConjugationSection H U Z ρ)
    (A B : Subgroup G) (hAH : A ≤ H) (hBH : B ≤ H)
    (hcross : subspaceCommutator ρ ⊤ (A.subgroupOf H) ≤
      fixedSpace ρ (B.subgroupOf H)) : ⁅⁅U,A⁆,B⁆ ≤ Z := by
  rw [commutator_comm _ B]
  apply c.commutator_le_of_imageSpace_fixed B ⁅U,A⁆ hBH
    (le_normalizer_iff_commutator_le_left.mp (hAH.trans c.normalized))
  rw [commutator_comm U A,c.imageSpace_commutator A U hAH le_rfl,c.imageSpace_self]
  exact hcross
end Representation.BinaryConjugationSection
