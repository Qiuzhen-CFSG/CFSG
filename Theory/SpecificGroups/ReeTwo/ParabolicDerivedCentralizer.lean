module

public import Theory.SpecificGroups.ReeTwo.ParabolicQuotientAction

/-!
# The derived centralizer in the whole Ree local group

An element centralizing the embedded derived subgroup has trivial
complement coordinate: core conjugation is invisible on the four tail
coordinates modulo the center, whereas the specified complement acts
faithfully there. A certificate checks its twenty normal forms.
The remaining condition is exactly the computed core centralizer.

Source: Aschbacher (1982), Section 3, with the verified Shinoda (1975)
root coordinates and complement action. This is a calculation in the
local model, without an ambient Ree identification.
-/

@[expose] public section
open Subgroup
namespace ReeTwo
namespace Core
private def tailRoot (k : Fin 4) : Core := root ⟨5+k.val, by omega⟩
private def tailHead (x : Core) : Fin 4 → ZMod 2 := ![x.b5,x.b6,x.b7,x.b8]

private theorem tailHead_mul_right (x y : Core) (hy : y ∈ commutator Core) :
    tailHead (x*y) = tailHead x + tailHead y := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := (mem_derived_iff y).mp hy
  funext i
  fin_cases i <;> simp [tailHead, show ∀ a b : Core, a*b = mul a b from fun _ _ => rfl,
    mul,h0,h1,h2,h3,h4]

private theorem tailHead_mul_left (x y : Core) (hx : x ∈ commutator Core) :
    tailHead (x*y) = tailHead x + tailHead y := by
  obtain ⟨h0,h1,h2,h3,h4⟩ := (mem_derived_iff x).mp hx
  funext i
  fin_cases i <;> simp [tailHead, show ∀ a b : Core, a*b = mul a b from fun _ _ => rfl,
    mul,h0,h1,h2,h3,h4]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
private theorem complement_tail_certificate : ∀ (i : Fin 5) (j : Fin 4),
    (∀ k : Fin 4, tailHead ((c ^ i.val * a ^ j.val) (tailRoot k)) =
      tailHead (tailRoot k)) → i = 0 ∧ j = 0 := by
  decide +kernel

private theorem complement_eq_one_of_tail (t : complement)
    (ht : ∀ k : Fin 4, tailHead ((t : MulAut Core) (tailRoot k)) =
      tailHead (tailRoot k)) : t = 1 := by
  obtain ⟨i,j,he⟩ := complement_normal_form t
  have hv : (t : MulAut Core) = c ^ i.val * a ^ j.val := congrArg Subtype.val he
  rw [hv] at ht
  obtain ⟨rfl,rfl⟩ := complement_tail_certificate i j ht
  apply Subtype.ext
  simpa using hv
end Core
namespace Centralizer

/-- The actual derived tail embedded through the normal-core inclusion. -/
def derived : Subgroup Centralizer :=
  (commutator Core).map (SemidirectProduct.inl : Core →* Centralizer)

/-- The centralizer of the derived tail in the whole local group lies in the core. -/
theorem centralizer_derived_eq_map : centralizer (derived : Set Centralizer) =
    (centralizer (commutator Core : Set Core)).map
      (SemidirectProduct.inl : Core →* Centralizer) := by
  apply le_antisymm
  · intro g hg
    have hc (y : Core) (hy : y ∈ commutator Core) :
        y * g.left = g.left * (g.right : MulAut Core) y := by
      have h := mem_centralizer_iff.mp hg (SemidirectProduct.inl y)
        (mem_map_of_mem _ hy)
      have hh := congrArg SemidirectProduct.left h
      simpa using hh
    have ht : g.right = 1 := by
      apply Core.complement_eq_one_of_tail
      intro k
      let y := Core.tailRoot k
      have hy : y ∈ commutator Core := Core.tail_root_mem_derived ⟨k.val, by omega⟩
      have hty : (g.right : MulAut Core) y ∈ commutator Core :=
        characteristic_iff_le_comap.mp inferInstance (g.right : MulAut Core) hy
      have h := congrArg Core.tailHead (hc y hy)
      rw [Core.tailHead_mul_left _ _ hy, Core.tailHead_mul_right _ _ hty,
        add_comm (Core.tailHead y)] at h
      exact (add_left_cancel h).symm
    have hF : g.left ∈ centralizer (commutator Core : Set Core) := by
      apply mem_centralizer_iff.mpr
      intro y hy
      simpa only [ht, OneMemClass.coe_one, MulAut.one_apply] using hc y hy
    refine ⟨g.left,hF,?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact ht.symm
  · rintro g ⟨x,hx,rfl⟩
    apply mem_centralizer_iff.mpr
    rintro y ⟨z,hz,rfl⟩
    simpa only [← map_mul] using
      congrArg (SemidirectProduct.inl : Core →* Centralizer) (mem_centralizer_iff.mp hx z hz)
end Centralizer
end ReeTwo
