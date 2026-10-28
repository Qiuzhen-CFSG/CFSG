module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.A5Residual
import all Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.A5Factor
public import Theory.GroupTheory.GeneralizedFitting.NilpotentComponentPreimage
public import Theory.GroupTheory.CComponent.RadicalFree

/-!
# The genuine A₅ residual in the marked J₄ max4

The alternating factor is a normal simple subgroup of the literal quotient
S₅ × SL₃(2). Its preimage's solvable residual is a C-component, with normal
ambient image and intrinsic two-core quotient A₅. These are properties of
the residual itself; the full preimage may have extra fixed two-factors.

The internal import exposes the marked factor bodies only to this extension.
Source: Aschbacher--Smith A.3.14(10) and 5.1.13, printed pp.49--50,637.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.SymmetricLinear
attribute [local irreducible] modelGroup matrixA matrixB max4Subgroup

/-- The concrete alternating factor, with its second coordinate trivial. -/
def a5FactorEquiv : a5Factor ≃* alternatingGroup (Fin 5) :=
  (Subgroup.prodEquiv _ _).trans MulEquiv.prodUnique

/-- The perfect residual of the literal marked preimage. -/
def a5Residual : Subgroup max4Subgroup :=
  (solvableResidual a5Preimage).map a5Preimage.subtype

instance : a5Residual.Normal := inferInstanceAs
  ((solvableResidual a5Preimage).map a5Preimage.subtype).Normal

/-- The actual preimage residual is a C-component and maps onto A₅ × 1. -/
theorem a5Residual_component_and_image :
    a5Residual.IsCComponent ∧ a5Residual.map max4Projection = a5Factor := by
  let : Group.IsNilpotent max4Projection.ker := max4Projection_kernel_isTwoGroup.isNilpotent
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup a5Factor := a5FactorEquiv.isSimpleGroup
  let : Group.IsPerfect a5Factor := Group.IsPerfect.ofSurjective
    (f := a5FactorEquiv.symm.toMonoidHom) a5FactorEquiv.symm.surjective
  exact cComponent_residual_preimage max4Projection max4Projection_surjective
    (isCComponent_of_isSimpleGroup_of_isPerfect (inferInstance : a5Factor.Normal).isSubnormal)

/-- The residual has the original two-core quotient A₅. -/
def a5ResidualQuotientEquiv :
    (a5Residual ⧸ pCore 2 a5Residual) ≃* alternatingGroup (Fin 5) := by
  let f := max4Projection.subgroupMap a5Residual
  have hk : IsPGroup 2 f.ker := by
    rw [show f.ker = max4Projection.ker.subgroupOf a5Residual from
      ker_subgroupMap a5Residual max4Projection]
    exact max4Projection_kernel_isTwoGroup.comap_subtype
  let d := MulEquiv.subgroupCongr a5Residual_component_and_image.2
  have hc : pCore 2 a5Factor = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : a5Factor.Normal).isSubnormal,
      quotientModel_twoCore,MonoidHom.comap_bot]
    exact a5Factor.subtype.ker_eq_bot a5Factor.subtype_injective
  exact (f.pCoreQuotientEquiv (max4Projection.subgroupMap_surjective a5Residual) hk).trans
    ((QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans
      ((QuotientGroup.quotientMulEquivOfEq hc).trans
        (QuotientGroup.quotientBot.trans a5FactorEquiv)))
end Janko4.LocalStructure.SymmetricLinear
