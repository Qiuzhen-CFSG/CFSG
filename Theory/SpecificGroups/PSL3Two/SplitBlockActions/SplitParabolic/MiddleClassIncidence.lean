module
public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.SplitParabolic.NaturalIdentification.Cores

/-!
# Matching outside involutions in the natural affine block

The middle radical has linear parts I + a e₂*, with nonzero a in the
standard plane. Three explicit determinant-one basis changes take these
linear parts to the three nonidentity elements of the point radical.
They take the translation plane bijectively to the respective fixed planes.
Thus they give an invertible pairing of outside involutions, with every pair
conjugate in the genuine semidirect product E₈ ⋊ SL₃(2).

The small coordinate identities are checked in the 64-element unitriangular
model by kernel reduction. The published equivalence uses the actual middle
subgroup, intrinsic point two-core, and translation kernel; it is consumed by
`Configuration.OrbitCalculation.ClassMatching` without ambient recognition or
an assumption about fusion in a larger group.

Source: M. Aschbacher, “A 2-local characterization of M12”, Lemma 2.6(3)
and the final paragraph of Lemma 3.1, printed pp.35–37,
https://authors.library.caltech.edu/records/m3wrn-5w840/files/ASCijm03.pdf.
-/

public section
open Subgroup
namespace Matrix.PSL3Two.SplitParabolic.MiddleClassIncidence
open Unitriangular

abbrev outsideInvolutions (B : Subgroup Block) : Set Block :=
  {x | x ∈ B ∧ x ∉ projection.ker ∧ orderOf x = 2}

private def middlePred (x : T) : Prop := x ∈ A ∧ (x.x23 ≠ 0 ∨ x.x24 ≠ 0)
private def corePred (x : T) : Prop :=
  x ∈ U ∧ (x.x24 ≠ 0 ∨ x.x34 ≠ 0) ∧ Square x
private instance (x : T) : Decidable (middlePred x) :=
  inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))
private instance (x : T) : Decidable (corePred x) :=
  inferInstanceAs (Decidable (_ ∧ (_ ∨ _) ∧ _))

private def toCore (x : T) : T :=
  if x.x23 = 0 then ⟨x.x13,0,x.x14,0,0,1⟩
  else if x.x24 = 0 then ⟨0,x.x14,x.x13,0,1,0⟩
  else ⟨x.x14+x.x13,x.x14+x.x13,x.x14,0,1,1⟩

private def toMiddle (x : T) : T :=
  if x.x24 = 0 then ⟨0,x.x12,x.x14,0,1,0⟩
  else if x.x34 = 0 then ⟨0,x.x14,x.x13,1,0,0⟩
  else ⟨0,x.x12+x.x14,x.x14,1,1,0⟩

private theorem toCore_mem : ∀ x : T, middlePred x → corePred (toCore x) := by
  decide +kernel
private theorem toMiddle_mem : ∀ x : T, corePred x → middlePred (toMiddle x) := by
  decide +kernel
private theorem toMiddle_toCore : ∀ x : T, middlePred x → toMiddle (toCore x) = x := by
  decide +kernel
private theorem toCore_toMiddle : ∀ x : T, corePred x → toCore (toMiddle x) = x := by
  decide +kernel

private def coordinateEquiv : {x : T // middlePred x} ≃ {x : T // corePred x} where
  toFun x := ⟨toCore x, toCore_mem x x.property⟩
  invFun x := ⟨toMiddle x, toMiddle_mem x x.property⟩
  left_inv x := Subtype.ext (toMiddle_toCore x x.property)
  right_inv x := Subtype.ext (toCore_toMiddle x x.property)

private def basisChange (x : T) : SL :=
  if x.x23 = 0 then ⟨!![1,0,0;0,0,1;0,1,0],by decide⟩
  else if x.x24 = 0 then ⟨!![0,1,0;1,0,0;0,0,1],by decide⟩
  else ⟨!![1,0,0;1,1,0;1,1,1],by decide⟩

private theorem conjugating_identity (x : T) (hx : middlePred x) :
    (SemidirectProduct.inr (basisChange x) : Block) * sylowMap x =
      sylowMap (toCore x) * SemidirectProduct.inr (basisChange x) := by
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    revert x
    decide +kernel
  · apply Subtype.ext
    change ((SemidirectProduct.inr (basisChange x) : Block) * sylowMap x).right.val =
      (sylowMap (toCore x) * SemidirectProduct.inr (basisChange x)).right.val
    revert x
    decide +kernel

private theorem sylow_kernel (x : T) :
    sylowMap x ∈ projection.ker ↔ x.x23 = 0 ∧ x.x24 = 0 ∧ x.x34 = 0 := by
  have hm : ∀ x : T, ((sylowMap x).right.val =
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2))) ↔
      x.x23 = 0 ∧ x.x24 = 0 ∧ x.x34 = 0 := by decide +kernel
  change (sylowMap x).right = 1 ↔ _
  rw [← hm x]
  exact ⟨fun he => congrArg (fun a : SL => a.val) he, fun he => Subtype.ext he⟩

private theorem middle_pred_iff (x : T) :
    middlePred x ↔ x ∈ A ∧ sylowMap x ∉ projection.ker ∧ orderOf x = 2 := by
  rw [sylow_kernel, orderOf_eq_prime_iff, square_iff]
  revert x
  decide +kernel

private theorem core_pred_iff (x : T) :
    corePred x ↔ x ∈ U ∧ sylowMap x ∉ projection.ker ∧ orderOf x = 2 := by
  rw [sylow_kernel, orderOf_eq_prime_iff, square_iff]
  revert x
  decide +kernel

private noncomputable def imageOutsideEquiv (B : Subgroup T) :
    {x : T // x ∈ B ∧ sylowMap x ∉ projection.ker ∧ orderOf x = 2} ≃
      outsideInvolutions (B.map sylowMap) :=
  Equiv.ofBijective
    (fun x => ⟨sylowMap x, mem_map_of_mem _ x.property.1, x.property.2.1,
      (orderOf_injective sylowMap sylowMap_injective x).trans x.property.2.2⟩)
    ⟨fun _ _ he => Subtype.ext (sylowMap_injective (congrArg Subtype.val he)), by
      rintro ⟨y, ⟨x, hx, rfl⟩, hker, ho⟩
      refine ⟨⟨x, hx, hker, ?_⟩, rfl⟩
      rwa [orderOf_injective sylowMap sylowMap_injective] at ho⟩

private noncomputable def middleEquiv :
    {x : T // middlePred x} ≃ outsideInvolutions middleGroup :=
  (Equiv.subtypeEquivRight middle_pred_iff).trans
    ((imageOutsideEquiv A).trans (Equiv.setCongr (by rw [middle_image])))

private noncomputable def coreEquiv :
    {x : T // corePred x} ≃ outsideInvolutions (pointPreimage.pCoreIn 2) :=
  (Equiv.subtypeEquivRight core_pred_iff).trans
    ((imageOutsideEquiv U).trans (Equiv.setCongr (by rw [U_image])))

/-- The two sets of outside involutions are paired by actual conjugation in the block. -/
noncomputable def matching : outsideInvolutions middleGroup ≃
    outsideInvolutions (pointPreimage.pCoreIn 2) :=
  middleEquiv.symm.trans (coordinateEquiv.trans coreEquiv)

theorem matching_isConj (x : outsideInvolutions middleGroup) :
    IsConj (x : Block) (matching x : Block) := by
  obtain ⟨y, rfl⟩ := middleEquiv.surjective x
  simp only [matching, Equiv.trans_apply, Equiv.symm_apply_apply]
  change IsConj (sylowMap y) (sylowMap (toCore y))
  exact isConj_iff.mpr ⟨SemidirectProduct.inr (basisChange y),
    mul_inv_eq_iff_eq_mul.mpr (conjugating_identity y y.property)⟩

end Matrix.PSL3Two.SplitParabolic.MiddleClassIncidence
end
