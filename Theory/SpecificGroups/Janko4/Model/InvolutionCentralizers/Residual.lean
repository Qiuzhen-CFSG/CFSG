module

public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.First
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Placement
public import Theory.GroupTheory.CComponent.SolvableSupplement
public import Theory.GroupTheory.CComponent.SimpleImageKernel
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.Mathieu.M22.Properties.FixedHexads
public import Theory.Mathieu.M22.TripleCover.ScalarAutomorphisms
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# The M₂₂ residuals in the native J₄ involution centralizers

The full first centralizer acts onto Aut(M₂₂) through its actual normal
series with factors a two-group and a cyclic group of order three. The
second centralizer has its genuine elementary two-kernel. Both kernels
are solvable. The residual of Aut(M₂₂) is its inner subgroup, identified
with native M₂₂ by conjugation. The solvable-kernel correspondence then
makes the full centralizer residual a C-component and identifies its
quotient by its solvable radical with M₂₂.

The residual itself, including the first row's covering center and two-core,
is retained. This does not identify its quotient by the two-core with M₂₂.
The application in MathieuGeneration uses the actual full covering component
and its specified involution-centralizer quotient.

Source: Aschbacher--Smith 4.4.3, printed p.623; GLS3 Table 5.3i. The native
matrix constructions and ATLAS attribution are retained in the imports.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace Janko4.InvolutionCentralizers

private theorem m22_perfect : Group.IsPerfect M22 :=
  Group.IsPerfect.ofSurjective (f := M22TripleCover.centralQuotientEquiv.toMonoidHom.comp
    (QuotientGroup.mk' (center M22TripleCover)))
    (M22TripleCover.centralQuotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))

private theorem m22Aut_residual :
    solvableResidual (MulAut M22) = MulAut.innerSubgroup M22 := by
  let := m22_perfect
  let : Group.IsPerfect (MulAut.innerSubgroup M22) := Group.IsPerfect.range MulAut.conj
  let : Group.IsNilpotent (MulAut.Outer M22) :=
    (IsPGroup.of_card_dvd_pow (p := 2) (n := 1)
      (by simpa only [pow_one] using
        M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two)).isNilpotent
  exact le_antisymm (solvableResidual_le_of_solvable_quotient _)
    (le_solvableResidual_of_isPerfect _)

private def m22AutResidualEquiv : solvableResidual (MulAut M22) ≃* M22 :=
  (MulEquiv.subgroupCongr m22Aut_residual).trans
    (MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot)).symm

private theorem m22Aut_residual_component : (solvableResidual (MulAut M22)).IsCComponent := by
  let := m22_isSimpleGroup
  let : IsSimpleGroup (solvableResidual (MulAut M22)) := m22AutResidualEquiv.isSimpleGroup
  exact isCComponent_of_isSimpleGroup_of_isPerfect
    (inferInstance : (solvableResidual (MulAut M22)).Normal).isSubnormal

/-- The residual over a genuine solvable-kernel M22 automorphism action is a
C-component with its literal simple radical quotient. -/
theorem residual_of_mathieuAction {C : Type*} [Group C] [Finite C]
    (f : C →* MulAut M22) (hf : Function.Surjective f) [Group.IsSolvable f.ker] :
    (solvableResidual C).IsCComponent ∧
      Nonempty ((solvableResidual C ⧸ solvableRadical (solvableResidual C)) ≃* M22) := by
  have hc := residual_isCComponent_of_surjective f hf m22Aut_residual_component
  let e := MulEquiv.subgroupCongr (map_solvableResidual_eq f hf)
  let q : solvableResidual C →* M22 :=
    (e.trans m22AutResidualEquiv).toMonoidHom.comp (f.subgroupMap (solvableResidual C))
  have hq : Function.Surjective q := (e.trans m22AutResidualEquiv).surjective.comp
    (f.subgroupMap_surjective _)
  let := m22_isSimpleGroup
  have htop : (⊤ : Subgroup (solvableResidual C)).IsCComponent := by
    simpa only [subgroupOf_self] using hc.subgroupOf (le_refl _)
  have hk := kernel_eq_solvableRadical_of_top_isCComponent htop q hq
  exact ⟨hc,⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq)⟩⟩

open First.QuotientExtension in
private theorem first_action_kernel_solvable :
    Group.IsSolvable First.QuotientExtension.centralizerMathieuAction.ker := by
  rw [centralizerMathieuAction_ker]
  let : Group.IsNilpotent (Q.subgroupOf R) :=
    (pCore_isPGroup.comap_subtype (p := 2) (G := First.centralizer)).isNilpotent
  let : Group.IsSolvable (R ⧸ Q.subgroupOf R) :=
    Group.isSolvable_of_isSolvable_injective
      (f := RQuotientEquivC3.toMonoidHom) RQuotientEquivC3.injective
  exact (Group.isSolvable_iff_subgroup_quotient (Q.subgroupOf R)).mpr
    ⟨inferInstance,inferInstance⟩

/-- The first full centralizer has a C-component residual with simple radical quotient M₂₂. -/
theorem first_residual_component :
    (solvableResidual First.centralizer).IsCComponent ∧
      Nonempty ((solvableResidual First.centralizer ⧸
        solvableRadical (solvableResidual First.centralizer)) ≃* M22) := by
  let := first_action_kernel_solvable
  exact residual_of_mathieuAction First.QuotientExtension.centralizerMathieuAction
    (First.QuotientExtension.quotientConjugation_surjective.comp
      First.centralizerExtension.rightHom_surjective)

/-- The second full centralizer has a C-component residual with simple radical quotient M₂₂. -/
theorem second_residual_component :
    (solvableResidual Second.ambientCentralizer).IsCComponent ∧
      Nonempty ((solvableResidual Second.ambientCentralizer ⧸
        solvableRadical (solvableResidual Second.ambientCentralizer)) ≃* M22) := by
  let := Second.ambientKernel_elementary
  let : Group.IsNilpotent Second.ambientExtension.rightHom.ker :=
    (IsElementaryAbelian.isPGroup 2 Second.ambientKernel).isNilpotent
  exact residual_of_mathieuAction Second.ambientExtension.rightHom
    Second.ambientExtension.rightHom_surjective

end Janko4.InvolutionCentralizers
