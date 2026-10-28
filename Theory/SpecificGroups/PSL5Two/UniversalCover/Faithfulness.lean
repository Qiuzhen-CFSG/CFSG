module

public import Theory.SpecificGroups.PSL5Two.UniversalCover.Faithfulness.MatrixSeparation
public import Theory.SpecificGroups.PSL5Two.UniversalCover.Faithfulness.Upper
public import Theory.SpecificGroups.PSL5Two.UniversalCover.Faithfulness.Weyl
public import Theory.SpecificGroups.PSL5Two.UniversalCover.Faithfulness.Bruhat

/-!
# Kernel reduction for the binary degree-five presentation

The matrix and projective maps are compared on their actual generators.
A Bruhat factorization writes a kernel element as `u * w * v`. Matrix
separation forces the Weyl factor's image to be the identity. Faithfulness
on the Weyl subgroup kills that factor, and faithfulness on the upper
subgroup kills the remaining product.

The covering and the two restricted faithfulness proofs are established in the
three subsidiary modules and assembled here into unconditional faithfulness of
the published presentation.

Source: the type A₄ Steinberg/Bruhat argument for the PSL₅(2) calculation
in Aschbacher–Smith I.1.3, printed p.407, citing GLS98 §6.1; the group is
listed in A.2.2(4) and A.2.3(4), printed p.33.
-/

@[expose] public section

namespace Theory.SpecificGroups.PSL5Two.UniversalCover
open Faithfulness

/-- The comparison is on the actual projective quotient and transvections. -/
theorem projectiveEquivSL_comp_projectiveMap :
    projectiveEquivSL.toMonoidHom.comp projectiveMap = matrixMap := by
  apply PresentedGroup.ext
  intro r
  change projectiveEquivSL (projectiveMap (generator r)) = matrixMap (generator r)
  rw [projectiveMap_generator, projectiveEquivSL_root, matrixMap_generator]

@[simp] theorem projectiveEquivSL_projectiveMap (g : SteinbergGroup) :
    projectiveEquivSL (projectiveMap g) = matrixMap g :=
  DFunLike.congr_fun projectiveEquivSL_comp_projectiveMap g

theorem matrixMap_injective_iff_projectiveMap_injective :
    Function.Injective matrixMap ↔ Function.Injective projectiveMap := by
  constructor
  · intro h a b hab
    apply h
    simpa only [projectiveEquivSL_projectiveMap] using congrArg projectiveEquivSL hab
  · intro h a b hab
    apply h
    apply projectiveEquivSL.injective
    simpa only [projectiveEquivSL_projectiveMap] using hab

/-- A Bruhat covering and faithful restrictions to its upper and Weyl factors
force faithfulness on the whole presentation. The matrix separation assertion
is proved in `MatrixSeparation`, not an additional hypothesis. -/
theorem matrixMap_injective_of_bruhat
    (hcover : BruhatCover)
    (hupper : Function.Injective (matrixMap.comp upperSubgroup.subtype))
    (hweyl : Function.Injective (matrixMap.comp weylSubgroup.subtype)) :
    Function.Injective matrixMap := by
  apply (MonoidHom.ker_eq_bot_iff matrixMap).mp
  apply eq_bot_iff.mpr
  intro g hg
  change g = 1
  change matrixMap g = 1 at hg
  obtain ⟨u, w, v, he⟩ := hcover g
  rw [he, map_mul, map_mul] at hg
  have hwimage : matrixMap w.val = matrixMap (u.val⁻¹ * v.val⁻¹) := by
    rw [map_mul, map_inv, map_inv]
    exact eq_inv_mul_iff_mul_eq.mpr (eq_inv_iff_mul_eq_one.mpr hg)
  have hwone : matrixMap w.val = 1 :=
    matrixMap_eq_one_of_upper_of_weyl
      (upperSubgroup.mul_mem (upperSubgroup.inv_mem u.property)
        (upperSubgroup.inv_mem v.property)) w.property hwimage.symm
  have hw : w = 1 := hweyl (by simpa using hwone)
  have huv : u * v = 1 := hupper (by simpa [hw] using hg)
  rw [he, hw]
  simpa only [Subgroup.coe_one, mul_one, Subgroup.coe_mul] using
    congrArg Subtype.val huv

/-- The preceding kernel argument gives faithfulness of the literal PSL₅(2)
map once its three independent normal-form inputs are supplied. -/
theorem projectiveMap_injective_of_bruhat
    (hcover : BruhatCover)
    (hupper : Function.Injective (matrixMap.comp upperSubgroup.subtype))
    (hweyl : Function.Injective (matrixMap.comp weylSubgroup.subtype)) :
    Function.Injective projectiveMap :=
  matrixMap_injective_iff_projectiveMap_injective.mp
    (matrixMap_injective_of_bruhat hcover hupper hweyl)

/-- The published binary degree-five Steinberg presentation is faithful on
the actual projective special-linear group. -/
theorem projectiveMap_injective : Function.Injective projectiveMap :=
  projectiveMap_injective_of_bruhat
    (bruhatCover_of_upperFactorization upperFactorization)
    matrixMap_upper_injective matrixMap_weylSubgroup_injective

end Theory.SpecificGroups.PSL5Two.UniversalCover
