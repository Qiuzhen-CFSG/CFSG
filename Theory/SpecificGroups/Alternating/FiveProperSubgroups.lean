module

public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.IntervalCases

/-!
# Proper subgroups of the alternating group on five letters

The coset action of A₅ on a proper subgroup is faithful, so its index is at
least five. Its order therefore divides sixty and is at most twelve. A
Sylow subgroup of index at most four is solvable, and its coset-action
kernel is contained in that subgroup. Solvability of S₄ completes the proof.

This is the elementary Sylow and coset-action proof of the proper-subgroup
calculation used for A₅ in Aschbacher–Smith, Theorem 0.1.2(3), condition K,
printed p.4. It uses no classification or recognition by group order.
-/

namespace alternatingGroup

private theorem solvable_of_small_index {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Group.IsSolvable H] (hi : H.index ≤ 4) :
    Group.IsSolvable G := by
  classical
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hcard : Fintype.card (G ⧸ H) ≤ Fintype.card (Fin 4) := by
    simpa only [Subgroup.index_eq_card, ← Nat.card_eq_fintype_card, Nat.card_fin] using hi
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (G ⧸ H)) :=
    Group.isSolvable_of_isSolvable_injective (Equiv.Perm.viaEmbeddingHom_injective e)
  apply Group.isSolvable_of_ker_le_range H.subtype (MulAction.toPermHom G (G ⧸ H))
  rw [Subgroup.range_subtype, ← H.normalCore_eq_ker]
  exact H.normalCore_le

private theorem solvable_of_small_sylow_index {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (hp : p ∣ Nat.card G) (hc : Nat.card G ≤ 4 * p) :
    Group.IsSolvable G := by
  let P : Sylow p G := Classical.choice inferInstance
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  apply solvable_of_small_index (P : Subgroup G)
  have hP : p ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos (P.dvd_card_of_dvd_card hp)
  have hi := (P : Subgroup G).card_mul_index
  have hpos := (Fact.out : p.Prime).pos
  nlinarith

private theorem solvable_of_small_divisor_of_sixty {G : Type*} [Group G] [Finite G]
    (hd : Nat.card G ∣ 60) (hb : Nat.card G ≤ 12) : Group.IsSolvable G := by
  by_cases hthree : 3 ∣ Nat.card G
  · let : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact solvable_of_small_sylow_index 3 hthree hb
  by_cases hfive : 5 ∣ Nat.card G
  · let : Fact (Nat.Prime 5) := ⟨by decide⟩
    exact solvable_of_small_sylow_index 5 hfive (by omega)
  have hc : Nat.card G = 1 ∨ Nat.card G = 2 ∨ Nat.card G = 4 := by
    generalize Nat.card G = n at *
    interval_cases n <;> omega
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have hpg : IsPGroup 2 G := by
    rcases hc with h | h | h
    · exact IsPGroup.of_card (n := 0) (by simpa using h)
    · exact IsPGroup.of_card (n := 1) (by simpa using h)
    · exact IsPGroup.of_card (n := 2) (by simpa using h)
  let := hpg.isNilpotent
  infer_instance

/-- Every proper subgroup of the actual A₅ is solvable. -/
public theorem isSolvable_subgroup_five_of_ne_top
    (H : Subgroup (alternatingGroup (Fin 5))) (hH : H ≠ ⊤) :
    Group.IsSolvable H := by
  have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  apply solvable_of_small_divisor_of_sixty
  · simpa only [hcard] using H.card_subgroup_dvd_card
  have hi : 5 ≤ H.index := by
    by_contra hn
    apply hH
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    have hb := Nat.factorial_le (show H.index ≤ 4 by omega)
    rw [hcard]
    norm_num [Nat.factorial] at hb ⊢
    omega
  have hp := H.card_mul_index
  rw [hcard] at hp
  nlinarith

/-- The same conclusion for any isomorphic carrier, across universes. -/
public theorem isSolvable_subgroup_of_equiv_five {G : Type*} [Group G]
    (e : G ≃* alternatingGroup (Fin 5)) (H : Subgroup G) (hH : H ≠ ⊤) :
    Group.IsSolvable H := by
  have hp : H.map e.toMonoidHom ≠ ⊤ := by
    intro h
    apply hH
    have hh := congrArg (Subgroup.map e.symm.toMonoidHom) h
    simpa [Subgroup.map_map] using hh
  let : Group.IsSolvable (H.map e.toMonoidHom) :=
    isSolvable_subgroup_five_of_ne_top _ hp
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective).toMonoidHom)
    (Subgroup.equivMapOfInjective H e.toMonoidHom e.injective).injective

end alternatingGroup
