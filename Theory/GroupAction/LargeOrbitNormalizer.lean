module

public import Mathlib.GroupTheory.GroupAction.Blocks
public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Normalizers preserve an orbit containing more than half the points

An orbit of U is a block for its normalizer, since U is normal in its
normalizer. Distinct translates are disjoint and have the same size, so
an orbit containing more than half the points is fixed by that normalizer.
A subgroup P transitive on such a set supplies the same conclusion for
every U between P and the set stabilizer. The last lemma pulls this bound
back through an actual homomorphism with a specified stabilizer preimage.

This elementary orbit argument is used for the four-point orbits in the
six-point actions of Held local quotients (GLS3, Table 5.3p). It assumes no
identification or structural property of those concrete quotients.
-/

public section

open Subgroup MulAction
open scoped Pointwise

namespace Subgroup

/-- An orbit larger than its complement is preserved by the normalizer. -/
theorem normalizer_le_stabilizer_of_large_orbit {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (U : Subgroup G) (x : X)
    (hlarge : Nat.card X < 2 * (orbit U x).ncard) :
    normalizer (U : Set G) ≤ stabilizer G (orbit U x) := by
  let N := normalizer (U : Set G)
  have he : orbit (U.subgroupOf N) x = orbit U x := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨⟨u.val.val, u.property⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨⟨⟨u.val, le_normalizer u.property⟩, u.property⟩, rfl⟩
  have hb : IsBlock N (orbit U x) := he ▸ IsBlock.orbit_of_normal (N := U.subgroupOf N) x
  intro g hg
  change g • orbit U x = orbit U x
  rcases (isBlock_iff_smul_eq_or_disjoint.mp hb) (⟨g, hg⟩ : N) with heq | hd
  · exact heq
  · have hc := Set.ncard_le_ncard (Set.subset_univ
      (((⟨g, hg⟩ : N) • orbit U x) ∪ orbit U x))
    rw [Set.ncard_union_eq hd, ← Set.image_smul,
      Set.ncard_image_of_injective _ (MulAction.injective (⟨g, hg⟩ : N)),
      Set.ncard_univ] at hc
    omega


/-- Transitivity of a smaller subgroup supplies the same normalizer bound. -/
theorem normalizer_le_stabilizer_of_large_suborbit
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (P U : Subgroup G) (B : Set X) (x : X)
    (hPU : P ≤ U) (hU : U ≤ stabilizer G B)
    (horbit : orbit P x = B) (hlarge : Nat.card X < 2 * B.ncard) :
    normalizer (U : Set G) ≤ stabilizer G B := by
  have hx : x ∈ B := horbit ▸ mem_orbit_self x
  have he : orbit U x = B := by
    apply Set.Subset.antisymm
    · rintro y ⟨u, rfl⟩
      have hmem : (u.val : G) • x ∈ (u.val : G) • B := ⟨x, hx, rfl⟩
      exact (hU u.property : (u.val : G) • B = B) ▸ hmem
    · intro y hy
      obtain ⟨p, rfl⟩ := horbit.symm ▸ hy
      exact ⟨⟨p.val, hPU p.property⟩, rfl⟩
  rw [← he]
  apply normalizer_le_stabilizer_of_large_orbit
  rwa [he]

/-- Pull the orbit bound back through an actual action homomorphism. The
stabilizer-preimage equality includes the required control of its kernel. -/
theorem normalizer_le_of_large_orbit_preimage
    {G H X : Type*} [Group G] [Group H] [MulAction H X] [Finite X]
    (f : G →* H) (P U K : Subgroup G) (B : Set X) (x : X)
    (hPU : P ≤ U) (hUK : U ≤ K)
    (hK : (stabilizer H B).comap f = K)
    (horbit : orbit (P.map f) x = B) (hlarge : Nat.card X < 2 * B.ncard) :
    normalizer (U : Set G) ≤ K := by
  rw [← hK, ← map_le_iff_le_comap]
  apply (le_normalizer_map f).trans
  apply normalizer_le_stabilizer_of_large_suborbit (P.map f) (U.map f) B x
    (map_mono hPU) _ horbit hlarge
  exact map_le_iff_le_comap.mpr (hK.symm ▸ hUK)

end Subgroup
