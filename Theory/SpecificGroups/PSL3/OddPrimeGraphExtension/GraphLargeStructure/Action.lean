module

public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension.GraphLargeStructure
public import Theory.GroupAction.AutomorphismFixedTransport
import all Theory.SpecificGroups.PSL3.OddPrimeGraphExtension.GraphLargeStructure

/-!
# The marked inner subgroup and the literal graph-extension action

Conjugation on the marked inner subgroup transports to the original action on
PSL₃. Hence its intrinsic centralizer of an ambient element is isomorphic to
the fixed subgroup of that element's literal projective automorphism.

The internal import is an intentional extension of `GraphLargeStructure`:
only the formula for its non-exposed chosen equivalence is used. The public
equations let consumers keep that implementation behind its existing boundary.
This supplies the action comparison used for the odd-prime graph branch of
Aschbacher--Smith E.1.14(7), printed p.214.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
variable (F : Type*) [Field F] [IsSimpleGroup PSL(3,F)]

/-- The marked equivalence sends a projective matrix to its actual inner automorphism. -/
theorem innerPartEquiv_apply_coe (x : PSL(3,F)) :
    ((innerPartEquiv F x : innerPart F) : graphExtension F).val = MulAut.conj x := by rfl

/-- The inverse equivalence recovers the projective matrix inducing the given inner action. -/
theorem innerPartEquiv_symm_conj (x : innerPart F) :
    MulAut.conj ((innerPartEquiv F).symm x) = (x : graphExtension F).val := by
  rw [← innerPartEquiv_apply_coe, MulEquiv.apply_symm_apply]

/-- Conjugation on the inner subgroup is the original projective action. -/
theorem innerPart_conj_action (t : graphExtension F) :
    MulAut.congr (innerPartEquiv F).symm (MulAut.conjNormal t) = (t : MulAut PSL(3,F)) := by
  ext x
  apply MulAut.conj_injective_of_center_eq_bot (center_PSL_eq_bot F)
  change MulAut.conj ((innerPartEquiv F).symm (MulAut.conjNormal t (innerPartEquiv F x))) = _
  rw [innerPartEquiv_symm_conj]
  change (t : MulAut PSL(3,F)) * (innerPartEquiv F x : graphExtension F).val *
    (t : MulAut PSL(3,F))⁻¹ = MulAut.conj ((t : MulAut PSL(3,F)) x)
  rw [innerPartEquiv_apply_coe]
  ext y
  simp

/-- The full intrinsic inner centralizer is the literal projective fixed subgroup. -/
noncomputable def innerCentralizerEquivFixed (t : graphExtension F) :
    (centralizer ({t} : Set (graphExtension F))).subgroupOf (innerPart F) ≃*
      (t : MulAut PSL(3,F)).fixedSubgroup := by
  let a : MulAut (innerPart F) := MulAut.conjNormal t
  have hfix : a.fixedSubgroup = (centralizer ({t} : Set (graphExtension F))).subgroupOf
      (innerPart F) := by
    ext x
    rw [MulAut.mem_fixedSubgroup, mem_subgroupOf, mem_centralizer_singleton_iff,
      Subtype.ext_iff]
    change t * (x : graphExtension F) * t⁻¹ = x ↔ (x : graphExtension F) * t = t * x
    rw [mul_inv_eq_iff_eq_mul, eq_comm]
  exact (MulEquiv.subgroupCongr hfix.symm).trans
    ((MulAut.fixedSubgroupCongr (innerPartEquiv F).symm a).trans
      (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup (innerPart_conj_action F t))))

end Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
