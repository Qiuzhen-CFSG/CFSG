module

public import Theory.GroupTheory.PGroup.CyclicAbelianization
public import Theory.GroupTheory.Commutator.TwoSubgroupNormalizer

/-!
# Two-groups with a small kernel and cyclic quotient

A finite two-group with a normal subgroup of order at most four and
cyclic quotient has nilpotency class at most two. Its derived subgroup
lies in the kernel. Equality with a nontrivial kernel would make the
abelianization cyclic, hence the whole two-group cyclic. The derived
subgroup therefore has order at most two, and its next commutator is
trivial by the strict decrease of normal commutators in a finite p-group.

This is a standard consequence of Frattini nongeneration, used for the
local quotient in Parrott (1972), p.676.
-/

open Subgroup

namespace IsPGroup

/-- A cyclic quotient with kernel of order at most four forces class at most two. -/
public theorem third_commutator_eq_bot_of_cyclic_quotient_small_kernel
    {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q)
    (B : Subgroup Q) [B.Normal] [IsCyclic (Q ⧸ B)] (hB : Nat.card B ≤ 4) :
    ⁅(⊤ : Subgroup Q), commutator Q⁆ = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDB : commutator Q ≤ B :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance
  by_cases hD : commutator Q = ⊥
  · simp [hD]
  have hlt : Nat.card (commutator Q) < Nat.card B := by
    apply Nat.lt_of_not_ge
    intro hc
    have heq : commutator Q = B := eq_of_le_of_card_ge hDB hc
    let : IsCyclic (Q ⧸ commutator Q) := isCyclic_of_surjective
      (QuotientGroup.quotientMulEquivOfEq heq).symm.toMonoidHom
      (QuotientGroup.quotientMulEquivOfEq heq).symm.surjective
    let : IsCyclic Q := hQ.isCyclic_of_cyclic_abelianization
    exact hD ((commutator_eq_bot_iff Q).mpr inferInstance)
  have hcard : Nat.card (commutator Q) ≤ 2 := by
    rcases (hQ.to_subgroup (commutator Q)).card_eq_or_dvd with hone | heven
    · omega
    · omega
  rw [commutator_comm]
  apply eq_bot_of_card_le
  by_contra hn
  have hh : commutator Q ≤ ⁅commutator Q, (⊤ : Subgroup Q)⁆ := by
    apply (eq_of_le_of_card_ge (commutator_le_left _ _) (by omega)).ge
  have heq : ⁅commutator Q, (⊤ : Subgroup Q)⁆ = commutator Q :=
    le_antisymm (commutator_le_left _ _) hh
  exact hD (bot_unique (le_normal_of_quotient_isPGroup_of_eq_commutator
    (commutator Q) ⊤ ⊥ (hQ.to_quotient ⊥) heq))

/-- Transfer the class-two bound through a cyclic image after factoring out a normal subgroup. -/
public theorem third_commutator_le_of_cyclic_image
    {P M : Type*} [Group P] [Finite P] [Group M] [Finite M]
    (hP : IsPGroup 2 P) (U : Subgroup P) [U.Normal]
    (f : P →* M) [IsCyclic f.range] (hU : U ≤ f.ker)
    (hcard : Nat.card f.ker ≤ 4 * Nat.card U) :
    ⁅(⊤ : Subgroup P), commutator P⁆ ≤ U := by
  let Q := P ⧸ U
  let q := QuotientGroup.mk' U
  let g : Q →* M := QuotientGroup.lift U f hU
  have hgq : g.comp q = f := by ext s; rfl
  have hrange : g.range = f.range := by
    rw [← hgq, MonoidHom.range_comp,
      q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective U),
      ← MonoidHom.range_eq_map]
  let : IsCyclic g.range := by rw [hrange]; infer_instance
  let : IsCyclic (Q ⧸ g.ker) := isCyclic_of_injective
    (QuotientGroup.quotientKerEquivRange g).toMonoidHom
    (QuotientGroup.quotientKerEquivRange g).injective
  have hgcard : Nat.card g.ker ≤ 4 := by
    have hcP := f.ker.card_mul_index
    have hcQ := g.ker.card_mul_index
    rw [index_ker] at hcP hcQ
    rw [hrange] at hcQ
    have hcU := U.index_mul_card
    change Nat.card Q * Nat.card U = Nat.card P at hcU
    have heq : (Nat.card g.ker * Nat.card U) * Nat.card f.range =
        Nat.card f.ker * Nat.card f.range := by
      calc
        _ = (Nat.card g.ker * Nat.card f.range) * Nat.card U := by ac_rfl
        _ = Nat.card Q * Nat.card U := by rw [hcQ]
        _ = Nat.card P := hcU
        _ = _ := hcP.symm
    have hh := Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := f.range)) heq
    have hpos : 0 < Nat.card U := Nat.card_pos
    nlinarith
  have hthird := (hP.to_quotient U).third_commutator_eq_bot_of_cyclic_quotient_small_kernel
    g.ker hgcard
  have hmap : (⁅(⊤ : Subgroup P), commutator P⁆).map q = ⊥ := by
    rw [map_commutator, ← MonoidHom.range_eq_map, map_commutator_eq,
      q.range_eq_top_of_surjective (QuotientGroup.mk'_surjective U)]
    exact hthird
  have hh := (Subgroup.map_eq_bot_iff _).mp hmap
  rwa [QuotientGroup.ker_mk'] at hh

end IsPGroup
