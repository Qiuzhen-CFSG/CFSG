module

public import Theory.Representation.FirstCohomology
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# First cohomology and a central fixed-point-free element

A central group element with no fixed vectors kills first cohomology: the value
of a cocycle at that element determines a principal cocycle, and centrality then
forces the difference to vanish everywhere. This applies in particular to a
faithful irreducible module for a central cover in which the center acts
nontrivially.
-/

@[expose] public section

namespace Representation.OneCohomology

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V)

/-- A central element acting without fixed vectors makes every crossed
homomorphism principal. The surjectivity hypothesis is automatic in finite
dimension. -/
theorem subsingleton_H1_of_central_fixedPointFree (z : G)
    (hz : z ∈ Subgroup.center G)
    (hinj : ∀ v : V, ρ z v = v → v = 0)
    (hsurj : ∀ v : V, ∃ w : V, ρ z w - w = v) :
    Subsingleton (H1 ρ) := by
  suffices hzero : ∀ f : cocycles ρ, classMap ρ f = 0 by
    constructor
    intro x y
    obtain ⟨f, rfl⟩ := (Submodule.mkQ_surjective _) x
    obtain ⟨g, rfl⟩ := (Submodule.mkQ_surjective _) y
    change classMap ρ f = classMap ρ g
    rw [hzero f, hzero g]
  intro f
  obtain ⟨w, hw⟩ := hsurj (f.val z)
  apply (classMap_eq_zero_iff ρ f).2
  refine ⟨w, ?_⟩
  apply Subtype.ext
  funext g
  have hzg : z * g = g * z := (Subgroup.mem_center_iff.mp hz g).symm
  have hc : ρ z (f.val g) + f.val z = ρ g (f.val z) + f.val g := by
    calc
      _ = f.val (z * g) := (f.property z g).symm
      _ = f.val (g * z) := by rw [hzg]
      _ = _ := f.property g z
  have hcomm : ρ z (ρ g w) = ρ g (ρ z w) := by
    change (ρ z * ρ g) w = (ρ g * ρ z) w
    rw [← map_mul, ← map_mul, hzg]
  have hrel : ρ z (f.val g) - f.val g = ρ g (f.val z) - f.val z := by
    calc
      _ = (ρ z (f.val g) + f.val z) - (f.val g + f.val z) := by abel
      _ = (ρ g (f.val z) + f.val g) - (f.val g + f.val z) := by rw [hc]
      _ = _ := by abel
  have hpr : ρ z (ρ g w - w) - (ρ g w - w) = ρ g (f.val z) - f.val z := by
    rw [map_sub, hcomm, ← hw, map_sub]
    abel
  have hfix : ρ z (f.val g - (ρ g w - w)) =
      f.val g - (ρ g w - w) := by
    apply sub_eq_zero.mp
    calc
      ρ z (f.val g - (ρ g w - w)) - (f.val g - (ρ g w - w)) =
          (ρ z (f.val g) - f.val g) -
            (ρ z (ρ g w - w) - (ρ g w - w)) := by rw [map_sub]; abel
      _ = 0 := by rw [hrel, hpr]; abel
  have hzero' := hinj _ hfix
  change ρ g w - w = f.val g
  exact sub_eq_zero.mp hzero' |>.symm

end Representation.OneCohomology

namespace Representation

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

private def centralFixedSpace (ρ : Representation k G V) (z : G)
    (hz : z ∈ Subgroup.center G) : Subrepresentation ρ where
  toSubmodule := (ρ z - 1).ker
  apply_mem_toSubmodule g := by
    intro v hv
    change ρ z v - v = 0 at hv
    change ρ z (ρ g v) - ρ g v = 0
    have hzg : z * g = g * z := (Subgroup.mem_center_iff.mp hz g).symm
    have hcomm : ρ z (ρ g v) = ρ g (ρ z v) := by
      change (ρ z * ρ g) v = (ρ g * ρ z) v
      rw [← map_mul, ← map_mul, hzg]
    rw [hcomm, ← map_sub, hv, map_zero]

/-- A faithful irreducible finite-dimensional representation of a group with
nontrivial center has vanishing first cohomology. -/
public theorem subsingleton_H1_of_faithful_irreducible_central
    (ρ : Representation k G V) [FiniteDimensional k V] [IsIrreducible ρ]
    (hfaithful : Function.Injective ρ) (z : G)
    (hz : z ∈ Subgroup.center G) (hzne : z ≠ 1) :
    Subsingleton (OneCohomology.H1 ρ) := by
  have hnotop : centralFixedSpace ρ z hz ≠ ⊤ := by
    intro htop
    have hzfix : ∀ v : V, ρ z v = v := by
      intro v
      have hv : v ∈ centralFixedSpace ρ z hz := by rw [htop]; trivial
      exact sub_eq_zero.mp hv
    exact hzne (hfaithful ((LinearMap.ext hzfix).trans ρ.map_one.symm))
  have hbot : centralFixedSpace ρ z hz = ⊥ :=
    ((inferInstance : IsIrreducible ρ).eq_bot_or_eq_top _).resolve_right hnotop
  let T : V →ₗ[k] V := ρ z - 1
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    exact congrArg Subrepresentation.toSubmodule hbot
  have hsurj := LinearMap.surjective_of_injective hinj
  apply OneCohomology.subsingleton_H1_of_central_fixedPointFree ρ z hz
  · intro v hv
    apply hinj
    simp [T, hv]
  · intro v
    obtain ⟨w, hw⟩ := hsurj v
    exact ⟨w, hw⟩

end Representation
