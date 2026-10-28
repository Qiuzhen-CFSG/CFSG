module
public import Theory.GroupTheory.InvolutionComplementCentralTwist
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.PointInvolution
public import CFSG.Quasithin.ChapterF.Section04.UnitaryTwo.ShortRootFixedFour
/-!
# The marked central twist of the binary point endpoint

The literal unitary point group splits over its two-residual by the middle
shear. Multiplying that shear by the marked central long-root involution
extends to an automorphism fixing the residual pointwise. It preserves the
plane module, root line and flag overlap. Within the module it fixes exactly
the fixed-core hyperplane and multiplies every vector outside that hyperplane
by the same long-root element.

This supplies a concrete point-endpoint automorphism for the overlap
adjustment in Aschbacher--Smith 13.5.17, printed p.922. The comparison of
all overlap automorphisms with the plane restrictions remains a separate
finite-module calculation; nontriviality alone does not prove that comparison.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.UnitaryTwo.PointCentralTwist
open GreenBook.LieModels.UnitaryFour PointInvolution ShortRootFixedFour
local notation "hn" => Nat.le_refl 1
local notation "P" => pointParabolic 1 hn

private theorem core_le_residual : pCore 2 P ≤ pResidual 2 P :=
  PointQuaternion.projectivePointQuaternionData.residual_contains_core _
    PointResidual.projectivePointResidualData

private theorem root_le_core : PointCore.rootSubgroup ≤ pCore 2 P := by
  rintro _ ⟨x,_,rfl⟩
  exact x.property

private theorem long_mem_residual : longPoint∈pResidual 2 P :=
  core_le_residual (root_le_core longPoint_mem_root)

private theorem exists_twist :
    ∃ α : MulAut P, (∀ n : pResidual 2 P, α n=(n:P)) ∧
      α involution=involution*longPoint ∧ Function.Involutive α ∧
      ∀ x : P, x∉pResidual 2 P → α x=x*longPoint := by
  have hv : orderOf involution=2 := orderOf_eq_prime involution_sq
    (fun he => involution_not_mem_core (he ▸ (pCore 2 P).one_mem))
  have hz : longPoint^2=1 := by simpa only [longPoint_order] using pow_orderOf_eq_one longPoint
  exact exists_involution_complement_central_twist (pResidual 2 P)
    involution longPoint hv long_mem_residual
    (PointCore.rootSubgroup_central longPoint_mem_root) hz involution_complement

/-- The point automorphism fixing the residual and twisting its shear by
the literal marked long-root involution. -/
def centralTwist : MulAut P := Classical.choose exists_twist

theorem centralTwist_residual (x : P) (hx : x∈pResidual 2 P) : centralTwist x=x :=
  (Classical.choose_spec exists_twist).1 ⟨x,hx⟩

theorem centralTwist_involution : centralTwist involution=involution*longPoint :=
  (Classical.choose_spec exists_twist).2.1

theorem centralTwist_involutive : Function.Involutive centralTwist :=
  (Classical.choose_spec exists_twist).2.2.1

theorem centralTwist_outside (x : P) (hx : x∉pResidual 2 P) :
    centralTwist x=x*longPoint := (Classical.choose_spec exists_twist).2.2.2 x hx

theorem centralTwist_core (x : P) (hx : x∈pCore 2 P) : centralTwist x=x :=
  centralTwist_residual x (core_le_residual hx)

theorem centralTwist_ne_one : centralTwist≠1 := by
  intro he
  have hh : involution=involution*longPoint := by simpa only [he,MulAut.one_apply] using
    centralTwist_involution
  have hz : longPoint=1 := (mul_eq_left.mp hh.symm)
  have ho := longPoint_order
  rw [hz,orderOf_one] at ho
  contradiction

private theorem long_mem_module : longPoint∈pointModule := by
  rw [pointModule_from_involution]
  apply mem_sup_left
  refine ⟨root_le_core longPoint_mem_root,mem_centralizer_singleton_iff.mpr ?_⟩
  exact (mem_center_iff.mp (PointCore.rootSubgroup_central longPoint_mem_root) involution).symm

/-- The module marking survives the point twist. -/
theorem centralTwist_module : pointModule.map centralTwist.toMonoidHom=pointModule := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,hx,rfl⟩
    by_cases hR : x∈pResidual 2 P
    · change centralTwist x∈pointModule
      rw [centralTwist_residual x hR]
      exact hx
    · change centralTwist x∈pointModule
      rw [centralTwist_outside x hR]
      exact pointModule.mul_mem hx long_mem_module
  · rw [card_map_of_injective centralTwist.injective]

/-- The marked root line is fixed pointwise, hence preserved as a subgroup. -/
theorem centralTwist_root : PointCore.rootSubgroup.map centralTwist.toMonoidHom=
    PointCore.rootSubgroup := by
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    change centralTwist x∈PointCore.rootSubgroup
    rw [centralTwist_core x (root_le_core hx)]
    exact hx
  · intro x hx
    exact ⟨x,hx,centralTwist_core x (root_le_core hx)⟩

/-- The literal flag overlap is preserved inside the point endpoint. -/
theorem centralTwist_overlap : ((overlap 1 hn).subgroupOf P).map centralTwist.toMonoidHom=
    (overlap 1 hn).subgroupOf P := by
  rw [←pointModule_normalizer,map_normalizer_eq_of_bijective _ centralTwist.bijective,
    centralTwist_module]

/-- On the fixed-core hyperplane of the module the twist is the identity. -/
theorem centralTwist_fixed_core (x : P)
    (hx : x∈pCore 2 P ⊓ centralizer ({involution} : Set P)) : centralTwist x=x :=
  centralTwist_core x hx.1

/-- Inside the module, the residual cuts out exactly the fixed core. -/
theorem module_mem_residual_iff (x : P) (hx : x∈pointModule) :
    x∈pResidual 2 P ↔ x∈pCore 2 P ⊓ centralizer ({involution} : Set P) := by
  constructor
  · intro hR
    refine ⟨PointQuaternion.projectivePointQuaternionData.residual_inf_two_subgroup_le _
      PointResidual.projectivePointResidualData pointModule
      (IsElementaryAbelian.isPGroup 2 pointModule) ⟨hR,hx⟩,?_⟩
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg (fun y : pointModule => (y:P))
      (mul_comm (⟨x,hx⟩ : pointModule) ⟨involution,involution_mem_module⟩)
  · intro hF
    exact core_le_residual hF.1

/-- Every module vector outside the fixed-core hyperplane is shifted by
the same nontrivial marked root vector. -/
theorem centralTwist_module_outside (x : P) (hx : x∈pointModule)
    (hF : x∉pCore 2 P ⊓ centralizer ({involution} : Set P)) :
    centralTwist x=x*longPoint :=
  centralTwist_outside x (fun h => hF ((module_mem_residual_iff x hx).mp h))

/-- The module's fixed subgroup under the point twist is precisely the
fixed-core hyperplane used in the original point marking. -/
theorem centralTwist_module_fixed_iff (x : P) (hx : x∈pointModule) :
    centralTwist x=x ↔ x∈pCore 2 P ⊓ centralizer ({involution} : Set P) := by
  constructor
  · intro he
    by_contra hF
    have hh := (centralTwist_module_outside x hx hF).symm.trans he
    have hz : longPoint=1 := mul_eq_left.mp hh
    have ho := longPoint_order
    rw [hz,orderOf_one] at ho
    contradiction
  · exact centralTwist_fixed_core x
end CFSG.Quasithin.ChapterF.UnitaryTwo.PointCentralTwist
