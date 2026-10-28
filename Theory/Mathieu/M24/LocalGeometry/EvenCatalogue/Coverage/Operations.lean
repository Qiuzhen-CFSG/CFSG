module
public import Theory.Mathieu.M24.LocalGeometry.EvenCatalogue

/-!
# Indexed arithmetic for the concrete M₂₄ Sylow catalogue

Multiplication and conjugation of the certified 1024 words are computed by
left-generator transitions. The point-action specification identifies these
computations with the actual group operations, without unfolding the abstract
word evaluation. Products of conjugates of an element of an intrinsic normal
subgroup stay in that subgroup.

This supports the finite exhaustiveness argument for the catalogue associated
to condition E (Aschbacher–Smith, printed pp.3–4; GLS3, Table 5.3e).
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.Coverage
open SylowNormalizer OrderEnumeration

def act : List (Fin 4) → Fin 1024 → Fin 1024
  | [], i => i
  | a :: w, i => step a (act w i)

theorem point_act (w : List (Fin 4)) (i : Fin 1024) (x : Fin 24) :
    point (act w i) x = evaluatePoint w (point i x) := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [act, point_step, ih]; rfl

def multiply (i j : Fin 1024) : Fin 1024 := act (words i) j

theorem element_multiply (i j : Fin 1024) :
    element (multiply i j) = element i * element j := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (element (multiply i j)).val.val x = (element i).val.val ((element j).val.val x)
  simp only [element_apply]
  exact point_act (words i) j x

def inverseGenerator : Fin 4 → Fin 1024 := ![925,773,384,5]

private theorem inverse_check : ∀ a, multiply (step a 0) (inverseGenerator a) = 0 := by
  decide +kernel

theorem element_zero : element 0 = 1 := element_identity

theorem element_inverseGenerator (a : Fin 4) :
    element (inverseGenerator a) = (markedGenerator a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  have h := congrArg element (inverse_check a)
  rw [element_multiply, element_step, element_zero, mul_one] at h
  exact h

def conjugate (a : Fin 4) (i : Fin 1024) : Fin 1024 :=
  multiply (step a i) (inverseGenerator a)

theorem element_conjugate (a : Fin 4) (i : Fin 1024) :
    element (conjugate a i) = markedGenerator a * element i * (markedGenerator a)⁻¹ := by
  rw [conjugate, element_multiply, element_step, element_inverseGenerator]

def conjugateWord : List (Fin 4) → Fin 1024 → Fin 1024
  | [], i => i
  | a :: w, i => conjugate a (conjugateWord w i)

theorem conjugateWord_mem (R : Subgroup candidate) (hn : R.Normal)
    {i : Fin 1024} (hi : element i ∈ R) (w : List (Fin 4)) :
    element (conjugateWord w i) ∈ R := by
  induction w with
  | nil => exact hi
  | cons a w ih =>
      rw [conjugateWord, element_conjugate]
      exact hn.conj_mem _ ih _

def product {α : Type} (g : α → Fin 1024) : List α → Fin 1024
  | [] => 0
  | a :: w => multiply (g a) (product g w)

theorem product_mem {α : Type} (R : Subgroup candidate) (g : α → Fin 1024)
    (hg : ∀ a, element (g a) ∈ R) (w : List α) : element (product g w) ∈ R := by
  induction w with
  | nil => rw [product, element_zero]; exact R.one_mem
  | cons a w ih => rw [product, element_multiply]; exact R.mul_mem (hg a) ih

def normalProduct (i : Fin 1024) (w : List (List (Fin 4))) : Fin 1024 :=
  product (fun a => conjugateWord a i) w

theorem normalProduct_mem (R : Subgroup candidate) (hn : R.Normal)
    {i : Fin 1024} (hi : element i ∈ R) (w : List (List (Fin 4))) :
    element (normalProduct i w) ∈ R :=
  product_mem R _ (conjugateWord_mem R hn hi) w

theorem generator_mem (i : Fin 22) (a : Fin 6) :
    element (generatorIndex i a) ∈ subgroup i := Subgroup.subset_closure ⟨a, rfl⟩

theorem subgroup_le (i : Fin 22) (R : Subgroup candidate)
    (h : ∀ a, element (generatorIndex i a) ∈ R) : subgroup i ≤ R := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨a, rfl⟩
  exact h a

end Sporadic.Mathieu.M24LocalGeometry.EvenCatalogue.Coverage
