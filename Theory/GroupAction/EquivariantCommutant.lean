module
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Commutants under a marked change of actors and space

Compatible group equivalences conjugate the two actual action images.
Restricting the induced automorphism-group equivalence identifies their full
centralizers. This is the conjugation transport used for the paired moved
quotients in Aschbacher--Smith, 10.2.3(2), printed p.745.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {A B V W : Type*} [Group A] [Group B] [Group V] [Group W]

/-- Compatible equivalences of actors and spaces identify their full commutants. -/
noncomputable def actionCommutantEquiv (f : A →* MulAut V) (g : B →* MulAut W)
    (a : A ≃* B) (e : V ≃* W)
    (he : ∀ x v, e (f x v) = g (a x) (e v)) :
    centralizer (f.range : Set (MulAut V)) ≃*
      centralizer (g.range : Set (MulAut W)) := by
  let c := MulAut.congr e
  have hfg (x : A) : c (f x) = g (a x) := by
    apply MulEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := e.surjective w
    change e (f x (e.symm (e v))) = _
    rw [e.symm_apply_apply]
    exact he x v
  have hr : f.range.map c.toMonoidHom = g.range := by
    ext z
    constructor
    · rintro ⟨_,⟨x,rfl⟩,rfl⟩
      change c (f x) ∈ g.range
      rw [hfg]
      exact ⟨a x,rfl⟩
    · rintro ⟨y,rfl⟩
      obtain ⟨x,rfl⟩ := a.surjective y
      exact ⟨f x,⟨x,rfl⟩,hfg x⟩
  have hc : (centralizer (f.range : Set (MulAut V))).map c.toMonoidHom =
      centralizer (g.range : Set (MulAut W)) := by
    apply le_antisymm
    · rw [←hr]
      exact map_centralizer_le_centralizer_image _ _
    intro z hz
    refine ⟨c.symm z,?_,c.apply_symm_apply z⟩
    intro x hx
    apply c.injective
    simpa only [map_mul,c.apply_symm_apply] using hz (c x)
      (hr ▸ mem_map_of_mem c.toMonoidHom hx)
  exact (c.subgroupMap _).trans (MulEquiv.subgroupCongr hc)
end Theory.GroupTheory
