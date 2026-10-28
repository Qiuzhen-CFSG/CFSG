module

public import Mathlib.GroupTheory.Sylow
public import Theory.GroupAction.LargeOrbitNormalizer

/-!
# Sylow stabilizers in large normal-subgroup orbits

A Sylow subgroup of a point stabilizer extends to an ambient Sylow.
Conjugating that Sylow to the prescribed one aligns the point stabilizer.
Its relative index in the prescribed Sylow is the prime part of the orbit
length. A normal subgroup with an orbit larger than half the point set
has the same orbit as the whole group, so the point transporter can be
chosen in that normal subgroup.

Source application: Aschbacher--Smith, 12.5.9(1), printed p.821.
-/

public section

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem exists_sylow_inf_conjugate (T : Sylow 2 G) (H : Subgroup G) :
    ∃ g : G, ¬ 2 ∣ ((T : Subgroup G) ⊓ H.map (MulAut.conj g).toMonoidHom).relIndex
      (H.map (MulAut.conj g).toMonoidHom) := by
  let P : Sylow 2 H := Classical.choice inferInstance
  obtain ⟨S, hS⟩ := P.exists_comap_subtype_eq
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S T
  have hmap : (P : Subgroup H).map H.subtype = (S : Subgroup G) ⊓ H := by
    rw [← hS, map_comap_eq, range_subtype, inf_comm]
  have hST : (S : Subgroup G).map (MulAut.conj g).toMonoidHom = (T : Subgroup G) :=
    congrArg Sylow.toSubgroup hg
  refine ⟨g, ?_⟩
  have hh := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    ((P : Subgroup H).map H.subtype) H (MulAut.conj g).injective
  rw [hmap, map_inf _ _ _ (MulAut.conj g).injective, hST] at hh
  rw [hh, inf_relIndex_right]
  change ¬ 2 ∣ ((S : Subgroup G).comap H.subtype).index
  rw [hS]
  exact P.not_dvd_index

theorem sylow_inf_index_of_odd_relative_index (T : Sylow 2 G) (H : Subgroup G)
    (h : ¬ 2 ∣ ((T : Subgroup G) ⊓ H).relIndex H) :
    ((T : Subgroup G) ⊓ H).relIndex (T : Subgroup G) =
      2 ^ H.index.factorization 2 := by
  let Q := (T : Subgroup G) ⊓ H
  obtain ⟨k, hk⟩ := T.isPGroup'.index (Q.subgroupOf (T : Subgroup G))
  have he := (relIndex_mul_index (show Q ≤ (T : Subgroup G) from inf_le_left)).trans
    (relIndex_mul_index (show Q ≤ H from inf_le_right)).symm
  have hfac := congrArg (fun n : ℕ => n.factorization 2) he
  have hnQ : Q.relIndex H ≠ 0 := index_ne_zero_of_finite (H := Q.subgroupOf H)
  have hnT : (T : Subgroup G).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  change Q.relIndex (T : Subgroup G) = 2 ^ k at hk
  rw [hk, Nat.factorization_mul (pow_ne_zero _ (by decide)) hnT,
    Nat.factorization_mul hnQ Subgroup.index_ne_zero_of_finite, Finsupp.add_apply,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd T.not_dvd_index,
    Nat.factorization_eq_zero_of_not_dvd h] at hfac
  have hk' : k = H.index.factorization 2 := by
    simpa only [Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
      add_zero, zero_add] using hfac
  exact hk.trans (congrArg (2 ^ ·) hk')
end Theory.GroupTheory

namespace Theory.GroupTheory
open MulAction
variable {G X : Type*} [Group G] [MulAction G X] [Finite X]

/-- A normal subgroup's orbit larger than half the points is already a full orbit. -/
theorem orbit_eq_of_large_normal_orbit (L : Subgroup G) [L.Normal] (x : X)
    (hlarge : Nat.card X < 2 * (orbit L x).ncard) :
    orbit G x = orbit L x := by
  apply Set.Subset.antisymm
  · rintro y ⟨g, rfl⟩
    have hg := normalizer_le_stabilizer_of_large_orbit L x hlarge
      (show g ∈ normalizer (L : Set G) by rw [normalizer_eq_top]; trivial)
    have he : g • orbit L x = orbit L x := hg
    rw [← he]
    exact ⟨x, mem_orbit_self x, rfl⟩
  · rintro y ⟨l, rfl⟩
    exact ⟨(l : G), rfl⟩

/-- Rechoose a point using an element of the normal subgroup, with the exact
Sylow index determined by its original orbit length. -/
theorem exists_sylow_point_in_large_normal_orbit [Finite G]
    (T : Sylow 2 G) (L : Subgroup G) [L.Normal] (x : X)
    (hlarge : Nat.card X < 2 * (stabilizer L x).index) :
    ∃ l : L,
      ((T : Subgroup G) ⊓ stabilizer G (l • x)).relIndex (T : Subgroup G) =
        2 ^ (stabilizer L x).index.factorization 2 ∧
      ¬ 2 ∣ ((T : Subgroup G) ⊓ stabilizer G (l • x)).relIndex
        (stabilizer G (l • x)) := by
  have horbit := orbit_eq_of_large_normal_orbit L x (by
    rwa [← index_stabilizer] )
  obtain ⟨g, hg⟩ := exists_sylow_inf_conjugate T (stabilizer G x)
  rw [← stabilizer_smul_eq_stabilizer_map_conj] at hg
  obtain ⟨l, hl⟩ := (show g • x ∈ orbit L x by
    rw [← horbit]; exact mem_orbit _ _)
  change l • x = g • x at hl
  refine ⟨l, ?_, ?_⟩
  · rw [hl, sylow_inf_index_of_odd_relative_index T _ hg,
      stabilizer_smul_eq_stabilizer_map_conj,
      index_map_of_bijective (MulAut.conj g).bijective,
      index_stabilizer, horbit, ← index_stabilizer]
  · rwa [hl]
end Theory.GroupTheory
