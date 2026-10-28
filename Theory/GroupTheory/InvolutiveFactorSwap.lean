module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.End

/-!
# Fixed subgroups of involutions interchanging two factors

An involutive automorphism of `A × B` that interchanges the two direct factors
has a full diagonal as its fixed subgroup. Projection onto `A` is an isomorphism;
its inverse sends `a` to `(a, (σ (a, 1)).2)`. Splitting `(a, b)` into its two
coordinate factors gives the formula for the action, and involutivity recovers
the inverse coordinate.

This is the diagonal argument used in Aschbacher--Smith, *The Classification of
Quasithin Groups*, combined manuscript (1 March 2004), Lemma I.3.2, printed
page 415. No finiteness or simplicity assumption is needed for this step.
-/

namespace MulAut
variable {A B : Type*} [Group A] [Group B]
variable (σ : MulAut (A × B))
variable (hσ : Function.Involutive σ)
variable (hA : ∀ a : A, (σ (a, 1)).1 = 1)
variable (hB : ∀ b : B, (σ (1, b)).2 = 1)

include hA hB in
private lemma factorSwap_apply (a : A) (b : B) :
    σ (a, b) = ((σ (1, b)).1, (σ (a, 1)).2) := by
  have hab : (a, b) = (a, (1 : B)) * (1, b) := by simp
  rw [hab, map_mul]
  apply Prod.ext
  · simp [hA]
  · simp [hB]

include hσ hA in
private lemma factorSwap_inverse_coordinate (a : A) :
    (σ (1, (σ (a, 1)).2)).1 = a := by
  have ha : σ (a, 1) = (1, (σ (a, 1)).2) := by
    apply Prod.ext
    · exact hA a
    · rfl
  have hi := congrArg Prod.fst (hσ (a, 1))
  rw [ha] at hi
  exact hi

include hσ hA hB in
/-- For an involution swapping the factors, the fixed subgroup is a full diagonal. -/
public theorem apply_eq_self_iff_of_swaps_factors (a : A) (b : B) :
    σ (a, b) = (a, b) ↔ (σ (a, 1)).2 = b := by
  rw [factorSwap_apply σ hA hB]
  constructor
  · exact fun h => congrArg Prod.snd h
  · intro hb
    apply Prod.ext
    · rw [← hb]
      exact factorSwap_inverse_coordinate σ hσ hA a
    · exact hb

/-- Projection onto the first factor identifies the fixed subgroup of a factor-swapping
involution with that factor. The inverse is the full diagonal embedding. -/
public def fixedSubgroupEquivLeftOfSwapsFactors
    : σ.toMonoidHom.eqLocus (MonoidHom.id (A × B)) ≃* A where
  toFun x := x.val.1
  invFun a := ⟨(a, (σ (a, 1)).2), (apply_eq_self_iff_of_swaps_factors σ hσ hA hB _ _).2 rfl⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact (apply_eq_self_iff_of_swaps_factors σ hσ hA hB _ _).1 x.property
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- The fixed-subgroup isomorphism is the first coordinate projection. -/
@[simp] public theorem fixedSubgroupEquivLeftOfSwapsFactors_apply
    (x : σ.toMonoidHom.eqLocus (MonoidHom.id (A × B))) :
    fixedSubgroupEquivLeftOfSwapsFactors σ hσ hA hB x = x.val.1 := by
  rfl

/-- The inverse of the fixed-subgroup isomorphism is the diagonal embedding. -/
@[simp] public theorem fixedSubgroupEquivLeftOfSwapsFactors_symm_apply (a : A) :
    ((fixedSubgroupEquivLeftOfSwapsFactors σ hσ hA hB).symm a : A × B) =
      (a, (σ (a, 1)).2) := by
  rfl

end MulAut
