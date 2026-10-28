module
public import Theory.SpecificGroups.MinusExtraspecial.AlternatingAction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.CoverSquareOrbit
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Algebra.Group.Commute.Hom

/-!
# The actual Hall--Janko minus core and its conjugation image

The two native factor maps from Q₈ and D₈ give a surjection onto the
order-32 radical. A check of their 64 pairs of coordinates identifies its
kernel with that of the explicit minus-extraspecial model. Quotienting
these two product maps gives the core equivalence, retaining both factors.
No permutation group or automorphism group is enumerated here.

The proved perfection of the actual first endpoint and its A₅ quotient
force the core to be self-centralizing. Its literal central quotient is
therefore the fixed subgroup of minus-core automorphisms inducing even
permutations on the five singular points. The conjugation equation is
retained on every representative for source action comparisons.

Source: DGS, Groups and Graphs (1985), (5.14)--(5.16), pp.116--117 and
(10.9), p.163; Aschbacher--Smith F.1.12(I)(10), p.263. The native ATLAS
carrier, generators and attribution are those of the imported radical.
-/

public noncomputable section
open Subgroup
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
open RadicalStructureData

private def modelProduct : QuaternionGroup 2 × DihedralGroup 4 →* MinusExtraspecial.Model :=
  MinusExtraspecial.quaternion.noncommCoprod MinusExtraspecial.dihedral MinusExtraspecial.factors_commute

private def radicalProduct : QuaternionGroup 2 × DihedralGroup 4 →* radical :=
  radicalQuaternionHom.noncommCoprod radicalDihedralHom
    (fun q d => radical_factors_commute _ ⟨q,rfl⟩ _ ⟨d,rfl⟩)

private theorem modelProduct_surjective : Function.Surjective modelProduct := by
  intro x
  obtain ⟨q,d,hd⟩ := MinusExtraspecial.factors_generate x
  exact ⟨(q,d),hd⟩

private theorem radicalProduct_surjective : Function.Surjective radicalProduct := by
  intro x
  obtain ⟨i,rfl⟩ := radicalEnum_surjective x
  exact ⟨(quaternionPart i,dihedralPart i),radicalEnum_factorization i⟩

private theorem factor_kernel_check : ∀ (q : QuaternionGroup 2) (d : DihedralGroup 4),
    MinusExtraspecial.quaternion q * MinusExtraspecial.dihedral d = 1 ↔
      quaternionIndex q = dihedralIndex d⁻¹ := by decide +kernel

private theorem product_ker : modelProduct.ker = radicalProduct.ker := by
  ext x
  change MinusExtraspecial.quaternion x.1 * MinusExtraspecial.dihedral x.2 = 1 ↔
    radicalQuaternionHom x.1 * radicalDihedralHom x.2 = 1
  rw [factor_kernel_check,mul_eq_one_iff_eq_inv,←map_inv]
  exact radicalEnum_injective.eq_iff.symm

/-- The native quaternion--dihedral radical in explicit minus-core coordinates. -/
def radicalModelEquiv : radical ≃* MinusExtraspecial.Model :=
  (QuotientGroup.quotientKerEquivOfSurjective radicalProduct radicalProduct_surjective).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq product_ker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective modelProduct modelProduct_surjective))

/-- The equivalence preserves the actual two factor maps. -/
theorem radicalModelEquiv_product (q : QuaternionGroup 2) (d : DihedralGroup 4) :
    radicalModelEquiv (radicalQuaternionHom q * radicalDihedralHom d) =
      MinusExtraspecial.quaternion q * MinusExtraspecial.dihedral d := by
  let f := QuotientGroup.quotientKerEquivOfSurjective radicalProduct radicalProduct_surjective
  have hh : f (QuotientGroup.mk' radicalProduct.ker (q,d)) = radicalProduct (q,d) := rfl
  change radicalModelEquiv (radicalProduct (q,d)) = _
  rw [←hh]
  change QuotientGroup.quotientKerEquivOfSurjective modelProduct modelProduct_surjective
    (QuotientGroup.quotientMulEquivOfEq product_ker.symm (f.symm (f _))) = _
  rw [f.symm_apply_apply]
  rfl

/-- The same coordinates on the literal intrinsic two-core of J₂'s first endpoint. -/
def coreModelEquiv : pCore 2 Seed.l₁ ≃* MinusExtraspecial.Model :=
  radicalCoreEquiv.symm.trans radicalModelEquiv

/-- Self-centralization of the literal first endpoint core. -/
theorem core_selfCentralizing :
    centralizer (pCore 2 Seed.l₁ : Set Seed.l₁) ≤ pCore 2 Seed.l₁ := by
  let : Group.IsPerfect Seed.l₁ := CoverSquareOrbit.l₁_isPerfect
  exact MinusExtraspecial.AlternatingAction.selfCentralizing_of_perfect
    (pCore 2 Seed.l₁) coreModelEquiv l₁_quotient.some

/-- The central quotient of the actual J₂ endpoint realizes the even core automorphisms. -/
def centralActionEquiv : (Seed.l₁ ⧸ center Seed.l₁) ≃*
    MinusExtraspecial.AlternatingAction.evenAutomorphisms :=
  MinusExtraspecial.AlternatingAction.centralQuotientEquiv
    (pCore 2 Seed.l₁) coreModelEquiv core_selfCentralizing l₁_quotient.some

/-- This identification is the actual conjugation action, on every representative. -/
theorem centralActionEquiv_apply (x : Seed.l₁) :
    (centralActionEquiv (QuotientGroup.mk' (center Seed.l₁) x) :
      MulAut MinusExtraspecial.Model) =
        MinusExtraspecial.AlternatingAction.coreAction (pCore 2 Seed.l₁) coreModelEquiv x :=
  MinusExtraspecial.AlternatingAction.centralQuotientEquiv_apply
    (pCore 2 Seed.l₁) coreModelEquiv core_selfCentralizing l₁_quotient.some x

end Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic
