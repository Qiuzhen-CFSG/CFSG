module

public import Theory.Representation.FirstCohomology
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# First cohomology from two commuting centralizers

Suppose two commuting elements act without fixed vectors on a finite-dimensional
representation, and their centralizers generate the group. Every crossed
homomorphism is principal: subtract a principal cocycle to make its value at the
first element zero. The cocycle identity then forces vanishing on its centralizer,
hence at the second element, hence on the second centralizer and the whole group.

This criterion provides a representation-independent route to the four-dimensional
binary alternating-group calculation in Aschbacher--Smith, *The Classification of
Quasithin Groups*, Lemma I.1.6(8), printed p.408/PDF p.419.
-/

@[expose] public section

namespace Representation.OneCohomology
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V)

/-- The zero set of a crossed homomorphism is a subgroup. -/
def vanishingSubgroup (f : cocycles ρ) : Subgroup G where
  carrier := {g | f.val g = 0}
  one_mem' := by
    have h := f.property 1 1
    simpa using h.symm
  mul_mem' hx hy := by
    rw [Set.mem_ofPred_eq] at hx hy ⊢
    rw [f.property, hx, hy, map_zero, add_zero]
  inv_mem' {g} hg := by
    change f.val g = 0 at hg
    change f.val g⁻¹ = 0
    have h := f.property g⁻¹ g
    have h1 : f.val 1 = 0 := by simpa using (f.property 1 1).symm
    simpa [hg, h1] using h.symm

/-- Vanishing at a fixed-point-free element forces vanishing on its centralizer. -/
theorem centralizer_le_vanishingSubgroup (f : cocycles ρ) (a : G)
    (ha : ∀ v : V, ρ a v = v → v = 0) (hfa : f.val a = 0) :
    Subgroup.centralizer ({a} : Set G) ≤ vanishingSubgroup ρ f := by
  intro g hg
  apply ha
  have hag : a * g = g * a := (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
  have h := (f.property a g).symm.trans ((congrArg f.val hag).trans (f.property g a))
  simpa [hfa] using h

/-- Two commuting fixed-point-free elements whose centralizers generate the group
force first cohomology to vanish. -/
theorem subsingleton_H1_of_commuting_centralizers
    [FiniteDimensional k V] (a b : G) (hab : Commute a b)
    (ha : ∀ v : V, ρ a v = v → v = 0)
    (hb : ∀ v : V, ρ b v = v → v = 0)
    (hgen : Subgroup.centralizer ({a} : Set G) ⊔
      Subgroup.centralizer ({b} : Set G) = ⊤) :
    Subsingleton (H1 ρ) := by
  apply Submodule.Quotient.subsingleton_iff.mpr
  apply LinearMap.range_eq_top.mpr
  intro f
  have hinj : Function.Injective (ρ a - (1 : Module.End k V) : V →ₗ[k] V) := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    exact ha v (sub_eq_zero.mp hv)
  obtain ⟨w, hw⟩ := LinearMap.surjective_of_injective hinj (f.val a)
  let d : cocycles ρ := f - principal ρ w
  have hda : d.val a = 0 := by
    change f.val a - (ρ a w - w) = 0
    exact sub_eq_zero.mpr hw.symm
  have hCa := centralizer_le_vanishingSubgroup ρ d a ha hda
  have hdb : d.val b = 0 := hCa (Subgroup.mem_centralizer_singleton_iff.mpr hab.eq.symm)
  have hCb := centralizer_le_vanishingSubgroup ρ d b hb hdb
  have htop : vanishingSubgroup ρ d = ⊤ :=
    top_unique (hgen ▸ sup_le hCa hCb)
  refine ⟨w, ?_⟩
  apply Subtype.ext
  funext g
  have hg : g ∈ vanishingSubgroup ρ d := htop ▸ Subgroup.mem_top g
  exact (sub_eq_zero.mp hg).symm

end Representation.OneCohomology
