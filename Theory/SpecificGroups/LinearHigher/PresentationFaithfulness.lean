module

public import Theory.SpecificGroups.LinearHigher.PresentationFaithfulness.MatrixSeparation
public import Theory.SpecificGroups.LinearHigher.OddKernelLifts
public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.PresentationFaithfulness.PositiveCollection.Application
public import Theory.SpecificGroups.HigherClassicalCovers.Linear.TwoPrimary.PresentationFaithfulness.WeylKernel

/-!
# The higher linear presentation: normal-form assembly

Bruhat coverage writes an element of the matrix kernel as `u * w * v`.
The upper and monomial matrix images intersect trivially, so the Weyl
factor has trivial matrix image. Faithfulness on the two generated
subgroups then kills the Weyl factor and the remaining positive word.
The resulting injectivity supplies the actual marked SL covering.

The existing degree-four normal forms give unconditional faithfulness in
degree four. Their coordinate transport also supplies finite-field torus
relations in every degree at least three. For larger degrees, the positive,
Weyl and Bruhat normal-form premises below remain explicit.

Source: Steinberg, *Lectures on Chevalley Groups*, §6, Theorems 8–9
and the SL example, printed pp.71–74
(`refs/KGroup/GLS3/Chapter2St1.tex`).
-/

public section

namespace Theory.SpecificGroups.LinearHigher
open PresentationFaithfulness
open scoped MatrixGroups

variable {n : ℕ} {F : Type*} [Field F]

/-- The completed degree-four normal forms give faithfulness over every
finite field, on precisely the presentation used here. -/
theorem matrixMap_four_injective [Finite F] :
    Function.Injective (matrixMap (n := 4) (F := F)) :=
  HigherClassicalCovers.Linear.TwoPrimaryFaithfulness.matrixMap_injective_of_weylKernelInTorus
    HigherClassicalCovers.Linear.TwoPrimaryFaithfulness.weylKernelInTorus

/-- The literal matrix map is faithful once positive and Weyl collection
and Bruhat coverage are proved. Matrix separation is supplied here. -/
theorem matrixMap_injective_of_bruhat
    (hcover : BruhatCover n F) (hupper : UpperFaithful n F) (hweyl : WeylFaithful n F) :
    Function.Injective (matrixMap (n := n) (F := F)) := by
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
      ((upperSubgroup n F).mul_mem ((upperSubgroup n F).inv_mem u.property)
        ((upperSubgroup n F).inv_mem v.property)) w.property hwimage.symm
  have hw : w = 1 := hweyl (by simpa using hwone)
  have huv : u * v = 1 := hupper (by simpa [hw] using hg)
  rw [he, hw]
  simpa only [Subgroup.coe_one, mul_one, Subgroup.coe_mul] using congrArg Subtype.val huv

/-- Application to the existing covering constructor, with the exact
projective marking and odd central kernel. Only the normal-form inputs
remain to be discharged by the presentation-faithfulness assembly. -/
theorem exists_covering_of_bruhat [CharP F 2]
    {E : Type*} [Group E] [Group.IsPerfect E]
    (f : E →* PSL(n, F)) (hf : Function.Surjective f)
    (hcenter : f.ker ≤ Subgroup.center E) (hcop : (Nat.card f.ker).Coprime 2)
    (hn : 2 ≤ n) (hcover : BruhatCover n F)
    (hupper : UpperFaithful n F) (hweyl : WeylFaithful n F) :
    ∃ s : SL(n, F) →* E, Function.Surjective s ∧
      f.comp s = QuotientGroup.mk' (Subgroup.center SL(n, F)) ∧
      s.ker ≤ Subgroup.center SL(n, F) :=
  exists_covering_of_matrixMap_injective f hf hcenter hcop hn
    (matrixMap_injective_of_bruhat hcover hupper hweyl)

/-- The degree-four even-field covering has no remaining presentation
premise, and retains the original map onto the projective quotient. -/
theorem exists_covering_four [Finite F] [CharP F 2]
    {E : Type*} [Group E] [Group.IsPerfect E]
    (f : E →* PSL(4, F)) (hf : Function.Surjective f)
    (hcenter : f.ker ≤ Subgroup.center E) (hcop : (Nat.card f.ker).Coprime 2) :
    ∃ s : SL(4, F) →* E, Function.Surjective s ∧
      f.comp s = QuotientGroup.mk' (Subgroup.center SL(4, F)) ∧
      s.ker ≤ Subgroup.center SL(4, F) :=
  exists_covering_of_matrixMap_injective f hf hcenter hcop (by decide)
    matrixMap_four_injective

end Theory.SpecificGroups.LinearHigher
