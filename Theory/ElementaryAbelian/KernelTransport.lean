module
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Elementary preimages depend only on the quotient kernel

Two quotient markings with the same kernel differ by an injective map on
the first quotient. Thus elementary full preimages for one marking imply
elementary full preimages for the other. The comparison is constructed by
the first isomorphism theorem and retains the literal maps on every element.

Source application: matching the Sylow coordinates chosen by the common
E₉ action with those of the exceptional cover in Aschbacher--Smith 2.5.7.
-/
public section

open Subgroup

theorem IsElementaryAbelian.comap_of_same_kernel
    {G U V : Type*} [Group G] [Group U] [Group V] {p : ℕ}
    (f : G →* U) (g : G →* V) (hf : Function.Surjective f)
    (hk : f.ker = g.ker)
    (hlift : ∀ W : Subgroup U, IsElementaryAbelian p W → IsElementaryAbelian p (W.comap f))
    (W : Subgroup V) (hW : IsElementaryAbelian p W) : IsElementaryAbelian p (W.comap g) := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  let b : U →* V := (QuotientGroup.lift f.ker g hk.le).comp e.symm.toMonoidHom
  have hb (x : G) : b (f x) = g x := by
    have he : e (QuotientGroup.mk' f.ker x) = f x := rfl
    change QuotientGroup.lift f.ker g hk.le (e.symm (f x)) = g x
    rw [← he, e.symm_apply_apply]
    rfl
  have hbi : Function.Injective b := by
    apply (MonoidHom.ker_eq_bot_iff b).mp
    apply bot_unique
    intro u hu
    obtain ⟨x, rfl⟩ := hf u
    have hg : x ∈ g.ker := by
      change g x = 1
      exact (hb x).symm.trans hu
    exact (show x ∈ f.ker from hk.symm ▸ hg)
  let := hW
  have hc : IsElementaryAbelian p (W.comap b) :=
    IsElementaryAbelian.comap_of_injective b hbi W
  have he : W.comap g = (W.comap b).comap f := by
    ext x
    change g x ∈ W ↔ b (f x) ∈ W
    rw [hb]
  rw [he]
  exact hlift (W.comap b) hc
