module
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Derived subgroup obstructions to centralizer fusion

A monomorphism preserves containment of each term of the derived series.
Thus a centralizer whose specified derived term is not a p-group cannot
be conjugate to a centralizer embedded in a group with a p-group at that
term. This permits a local word obstruction to exclude involution fusion,
without recognizing the entire centralizer.

The motivating application is the graph-involution exclusion in
Aschbacher--Smith F.4.36, printed p.292.
-/
public noncomputable section
namespace Theory.GroupTheory
open Subgroup
variable {G H : Type*} [Group G] [Group H]

theorem isPGroup_derivedSeries_of_injective (p n : ℕ)
    (f : G →* H) (hf : Function.Injective f)
    (hp : IsPGroup p (derivedSeries H n)) :
    IsPGroup p (derivedSeries G n) := by
  let k : derivedSeries G n →* derivedSeries H n :=
    (f.comp (derivedSeries G n).subtype).codRestrict _ (fun x =>
      map_derivedSeries_le_derivedSeries f n (mem_map_of_mem f x.property))
  apply hp.of_injective k
  intro a b hab
  apply Subtype.ext
  exact hf (congrArg Subtype.val hab)

/-- A derived-series p-group obstruction in one centralizer excludes
conjugacy to an element whose centralizer embeds in the supplied local group. -/
theorem not_isConj_of_derivedCentralizer
    (p n : ℕ) (f : H →* G) (hf : Function.Injective f)
    {t z : G}
    (ht : ¬ IsPGroup p (derivedSeries (centralizer ({t} : Set G)) n))
    (hz : centralizer ({z} : Set G) ≤ f.range)
    (hp : IsPGroup p (derivedSeries H n)) : ¬ IsConj t z := by
  intro hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hg' : MulAut.conj g t = z := hg
  let C := centralizer ({t} : Set G)
  let k : C →* G := (MulAut.conj g).toMonoidHom.comp C.subtype
  have hk : ∀ x : C, k x ∈ f.range := by
    intro x
    have hc : Commute (x : G) t := mem_centralizer_singleton_iff.mp x.property
    have hcg := hc.map (MulAut.conj g).toMonoidHom
    change Commute (MulAut.conj g (x : G)) (MulAut.conj g t) at hcg
    rw [hg'] at hcg
    exact hz (mem_centralizer_singleton_iff.mpr hcg.eq)
  let k' : C →* f.range := k.codRestrict _ hk
  have hk' : Function.Injective k' := by
    intro a b hab
    apply Subtype.ext
    apply (MulAut.conj g).injective
    exact congrArg Subtype.val hab
  let j : C →* H := (MonoidHom.ofInjective hf).symm.toMonoidHom.comp k'
  exact ht (isPGroup_derivedSeries_of_injective p n j
    ((MonoidHom.ofInjective hf).symm.injective.comp hk') hp)

end Theory.GroupTheory
