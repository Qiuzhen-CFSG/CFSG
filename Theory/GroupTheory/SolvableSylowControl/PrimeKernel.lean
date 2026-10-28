module
public import Theory.GroupTheory.SolvableSylowControl
public import Theory.GroupTheory.PCorePreimageCentralizer

/-!
# Solvable Sylow control across a prime-group kernel

A surjective homomorphism with p-group kernel takes a solvable Sylow
overgroup to a solvable overgroup of the image Sylow. The kernel lies in
the original Sylow, so pulling back its image normalizer gives its exact
normalizer. Thus intrinsic solvable Sylow control lifts across the kernel.

This includes the central two-covers in Aschbacher--Smith 15.1.20--21,
printed pp.1096--1098, without requiring a splitting or a trivial center.
-/

public section

open Subgroup
namespace Theory.GroupTheory.SolvableSylowControl
variable {p : ℕ} [Fact p.Prime]
variable {G H : Type*} [Group G] [Finite G] [Group H]

/-- Lift solvable Sylow control along a surjection with p-group kernel. -/
theorem of_surjective_pKernel (f : G →* H) (hf : Function.Surjective f)
    (hk : IsPGroup p f.ker) (h : SolvableSylowControl p H) :
    SolvableSylowControl p G := by
  intro S A hA hSA
  let := hA
  have hs : Group.IsSolvable (A.map f) :=
    Group.isSolvable_of_surjective (f.subgroupMap_surjective A)
  have hn := h (S.mapSurjective hf) (A.map f) hs (map_mono hSA)
  have hpre : ((S : Subgroup G).map f).comap f = S :=
    comap_map_eq_self (hk.le_sylow_of_normal S)
  change A.map f ≤ normalizer ((S : Subgroup G).map f : Set H) at hn
  have hh := comap_mono (f := f) hn
  rw [comap_normalizer_eq_of_surjective _ hf, hpre] at hh
  intro x hx
  exact hh (mem_map_of_mem f hx)
end Theory.GroupTheory.SolvableSylowControl
