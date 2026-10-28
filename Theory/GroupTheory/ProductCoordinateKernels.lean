module
public import Theory.GroupTheory.NormalProductCoordinate
/-!
# Coordinate kernels under a product automorphism

An automorphism of two center-free factors with only two-group proper
normal quotients preserves or exchanges the literal projection kernels.
The coordinate factor-permutation theorem supplies the zero cross terms;
injectivity then detects each original coordinate. This is used to compare
the original A5 product marking with a selected natural paired marking.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {A : Type*} [Group A] [Nontrivial A]
theorem product_automorphism_coordinate_kernels
    (hA : ∀ (N : Subgroup A) [N.Normal], N ≠ ⊥ → IsPGroup 2 (A ⧸ N))
    (hcore : pCore 2 A = ⊥) (hz : center A = ⊥) (e : MulAut (A × A)) :
    ((∀ x, (e x).1 = 1 ↔ x.1 = 1) ∧ (∀ x, (e x).2 = 1 ↔ x.2 = 1)) ∨
      ((∀ x, (e x).1 = 1 ↔ x.2 = 1) ∧ (∀ x, (e x).2 = 1 ↔ x.1 = 1)) := by
  have normal_case (f : MulAut (A × A))
      (ha : ∀ a, (f (a,1)).2 = 1) (hb : ∀ b, (f (1,b)).1 = 1) :
      (∀ x, (f x).1 = 1 ↔ x.1 = 1) ∧ (∀ x, (f x).2 = 1 ↔ x.2 = 1) := by
    have he (x : A × A) : f x = ((f (x.1,1)).1,(f (1,x.2)).2) := by
      have hx : x = (x.1,1) * (1,x.2) := by simp
      rw [hx,map_mul]
      exact Prod.ext (by simp [hb]) (by simp [ha])
    constructor
    · intro x
      rw [he]
      constructor
      · intro h
        have hh : f (x.1,1) = f 1 := by
          rw [map_one]
          exact Prod.ext h (ha _)
        exact congrArg Prod.fst (f.injective hh)
      · intro h
        rw [h]
        exact congrArg Prod.fst f.map_one
    · intro x
      rw [he]
      constructor
      · intro h
        have hh : f (1,x.2) = f 1 := by
          rw [map_one]
          exact Prod.ext (hb _) h
        exact congrArg Prod.snd (f.injective hh)
      · intro h
        rw [h]
        exact congrArg Prod.snd f.map_one
  rcases automorphism_product_coordinates hA hA hcore hz e with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact Or.inl (normal_case e ha hb)
  · let s : MulAut (A × A) := e.trans MulEquiv.prodComm
    have hs := normal_case s ha hb
    exact Or.inr ⟨hs.2,hs.1⟩
end Theory.GroupTheory
