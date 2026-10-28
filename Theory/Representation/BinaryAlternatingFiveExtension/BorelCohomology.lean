module
public import Theory.Representation.BinaryAlternatingFiveExtension.BorelModel
public import Theory.Representation.BinaryAlternatingNaturalCohomology

/-!
# Translation correction in the ordinary affine overlap

Restricting the five-point binary augmentation core to its first four
coordinates identifies the actual A₄ point-stabilizer action with the full
four-letter permutation module. The omitted coordinate is the sum of those
four coordinates. The stored marking of A₄ is retained throughout.

Every cocycle is principal by the existing full permutation-module theorem,
so first cohomology of this actual overlap module vanishes. For a literal
`BorelModel` automorphism fixing translations pointwise and the quotient
coordinate identically, its values on the standard A₄ complement give such
a cocycle. The principal vector then expresses the original automorphism as
conjugation by an actual translation, with the orientation retained.

Source: Aschbacher--Smith 13.5.17, printed p.922, ordinary U₄(2) overlap
adjustment. The normalized automorphism is supplied by the quotient and
module corrections; this module proves its remaining translation correction.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.OneCohomology
namespace BinaryPermutation.AlternatingFiveExtension.BorelCohomology
open AlternatingFiveBorel

/-- Restrict the five-point core to the first four coordinates. The omitted
coordinate is their sum, so the result is the full permutation module. -/
def fullCoordinates : core (Fin 5) ≃ₗ[ZMod 2] Full (Fin 4) where
  toFun x i := x.val i.castSucc
  invFun x := ⟨Fin.lastCases (∑ i, x i) x, by
    rw [mem_core, Fin.sum_univ_castSucc]
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
    exact CharTwo.add_self_eq_zero _⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    induction i using Fin.lastCases with
    | last =>
      change (∑ i : Fin 4, x.val i.castSucc) = x.val 4
      have hx := x.property
      rw [mem_core, Fin.sum_univ_castSucc] at hx
      exact (eq_neg_of_add_eq_zero_left hx).trans (CharTwo.neg_eq _)
    | cast i => simp only [Fin.lastCases_castSucc]
  right_inv x := by
    funext i
    change Fin.lastCases (∑ j, x j) x i.castSucc=x i
    exact Fin.lastCases_castSucc i
  map_add' x y := rfl
  map_smul' a x := rfl

@[simp] theorem fullCoordinates_apply (x : core (Fin 5)) (i : Fin 4) :
    fullCoordinates x i = x.val i.castSucc := rfl

theorem fullCoordinates_marking (g : alternatingGroup (Fin 4)) (v : core (Fin 5)) :
    fullCoordinates (action (marking g) v) =
      alternatingRepresentation (Fin 4) g (fullCoordinates v) := by
  funext i
  exact action_marking_cast g v i

theorem fullCoordinates_equivariant (g : B) (v : core (Fin 5)) :
    fullCoordinates (action g v) =
      alternatingRepresentation (Fin 4) (marking.symm g) (fullCoordinates v) := by
  simpa only [marking.apply_symm_apply] using fullCoordinates_marking (marking.symm g) v

/-- Cocycle transport along the original A₄ marking and full-four coordinates. -/
def cocycleCoordinates : cocycles action ≃ₗ[ZMod 2]
    cocycles (alternatingRepresentation (Fin 4)) :=
  cocyclesCongr action (alternatingRepresentation (Fin 4)) marking.symm
    fullCoordinates fullCoordinates_equivariant

/-- Every cocycle for the actual overlap module is principal. -/
theorem principal_surjective : Function.Surjective (principal action) := by
  intro f
  obtain ⟨w,hw⟩ := alternating_principal_surjective (Fin 4)
    (by simp : 3 ≤ Nat.card (Fin 4)) (cocycleCoordinates f)
  refine ⟨fullCoordinates.symm w,?_⟩
  apply cocycleCoordinates.injective
  change cocyclesCongr action (alternatingRepresentation (Fin 4)) marking.symm
    fullCoordinates fullCoordinates_equivariant (principal action (fullCoordinates.symm w)) = _
  rw [cocyclesCongr_principal, fullCoordinates.apply_symm_apply]
  exact hw

/-- The original point-stabilizer action has vanishing first cohomology. -/
theorem subsingleton_H1 : Subsingleton (H1 action) :=
  Submodule.Quotient.subsingleton_iff.mpr
    (LinearMap.range_eq_top.mpr principal_surjective)

/-- Every automorphism fixing the original translations and A₄ quotient
is conjugation by an actual translation. -/
theorem automorphism_translation_correction (α : MulAut BorelModel)
    (hV : ∀ n : V, α (SemidirectProduct.inl n) = SemidirectProduct.inl n)
    (hq : ∀ x : BorelModel, (α x).right = x.right) :
    ∃ n : V, ∀ x : BorelModel,
      α x = SemidirectProduct.inl n * x * (SemidirectProduct.inl n)⁻¹ := by
  let d : cocycles action := ⟨fun b => (α (SemidirectProduct.inr b)).left.toAdd, by
    intro b c
    have h := congrArg (fun x : BorelModel => x.left.toAdd)
      (α.map_mul (SemidirectProduct.inr b) (SemidirectProduct.inr c))
    rw [←map_mul] at h
    change (α (SemidirectProduct.inr (b*c))).left.toAdd =
      (α (SemidirectProduct.inr b)).left.toAdd +
        action (α (SemidirectProduct.inr b)).right (α (SemidirectProduct.inr c)).left.toAdd at h
    rw [hq,SemidirectProduct.right_inr] at h
    exact h.trans (add_comm _ _)⟩
  obtain ⟨w,hw⟩ := principal_surjective d
  have hd (b : B) : (α (SemidirectProduct.inr b)).left.toAdd = action b w-w := by
    exact (congrArg (fun c : cocycles action => c.val b) hw).symm
  refine ⟨Multiplicative.ofAdd (-w),?_⟩
  intro x
  have hx : α x = SemidirectProduct.inl x.left * α (SemidirectProduct.inr x.right) := by
    calc
      α x = α (SemidirectProduct.inl x.left * SemidirectProduct.inr x.right) :=
        congrArg α (SemidirectProduct.inl_left_mul_inr_right x).symm
      _ = _ := by rw [map_mul,hV]
  apply SemidirectProduct.ext
  · rw [hx]
    change x.left.toAdd+(α (SemidirectProduct.inr x.right)).left.toAdd =
      (-w+x.left.toAdd) + action x.right (- -w)
    rw [hd,neg_neg]
    abel
  · simpa only [SemidirectProduct.mul_right,SemidirectProduct.right_inl,
      SemidirectProduct.inv_right,one_mul,mul_one,inv_one] using hq x

end BinaryPermutation.AlternatingFiveExtension.BorelCohomology
