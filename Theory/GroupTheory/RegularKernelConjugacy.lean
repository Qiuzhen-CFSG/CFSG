module

public import Theory.GroupTheory.RegularKernelSplitting

/-!
# Conjugacy of sections with a regular kernel

For regular permutation coordinates the difference of two sections is a
crossed map. Evaluating its value at x in coordinate x explicitly gives a
kernel element conjugating one section onto the other. The quotient and
both original sections are retained.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {E P A : Type*} [Group E] [Group P] [CommGroup A]

/-- Two sections of the same extension are conjugate by an actual kernel
element when that kernel has the given regular conjugation coordinates. -/
theorem sections_conjugate_of_regular_kernel
    (q : E →* P) (e : q.ker ≃* (P → A))
    (he : ∀ (g : E) (v : q.ker) (x : P),
      e (MulAut.conjNormal g v) x=e v ((q g)⁻¹*x))
    (s t : P →* E) (hs : ∀ g,q (s g)=g) (ht : ∀ g,q (t g)=g) :
    ∃ v : q.ker, ∀ g, s g=(v:E)*t g*(v:E)⁻¹ := by
  let d (g : P) : q.ker := ⟨s g*(t g)⁻¹,by
    change q (s g*(t g)⁻¹)=1
    rw [map_mul,map_inv,hs,ht,mul_inv_cancel]⟩
  have hd (g h : P) : d (g*h)=d g*MulAut.conjNormal (t g) (d h) := by
    apply Subtype.ext
    change s (g*h)*(t (g*h))⁻¹=(s g*(t g)⁻¹)*(t g*(s h*(t h)⁻¹)*(t g)⁻¹)
    rw [map_mul,map_mul]
    group
  let a : P → A := fun x => e (d x) x
  have ha (g x : P) : e (d g) x=a x*(a (g⁻¹*x))⁻¹ := by
    have hh := congrArg (fun v : q.ker => e v x) (hd g (g⁻¹*x))
    rw [mul_inv_cancel_left,map_mul,Pi.mul_apply,he,ht] at hh
    exact eq_mul_inv_of_mul_eq (show e (d g) x*a (g⁻¹*x)=a x from hh.symm)
  let v := e.symm a
  have hv (g : P) : d g=v*MulAut.conjNormal (t g) v⁻¹ := by
    apply e.injective
    ext x
    rw [map_mul,Pi.mul_apply,he,map_inv,Pi.inv_apply,ht]
    simp only [v,e.apply_symm_apply]
    exact ha g x
  refine ⟨v,fun g => ?_⟩
  have hh := congrArg (fun z : q.ker => (z:E)) (hv g)
  change s g*(t g)⁻¹=(v:E)*(t g*(v:E)⁻¹*(t g)⁻¹) at hh
  have hh' := congrArg (fun z : E => z*t g) hh
  simpa only [mul_assoc,inv_mul_cancel,mul_one] using hh'

end Theory.GroupTheory
