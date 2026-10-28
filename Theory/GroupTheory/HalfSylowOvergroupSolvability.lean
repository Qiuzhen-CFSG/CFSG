module
public import Theory.GroupTheory.SylowOvergroupSolvability
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.PResidual.Defs
public import Mathlib.GroupTheory.IndexNormal

/-!
# Solvability tests for half-Sylow overgroups

A subgroup containing a subgroup of index at most two in a Sylow two-group
cannot have index divisible by four. An index-four obstruction for proper
nonsolvable subgroups lifts through O₂ in a two-perfect group. A full quotient
image would have two-power index; the only indices not divisible by four are
one and two, and two-perfectness excludes the latter.

The statements retain the literal quotient map and are used for the χ₀
local-persistence step of Aschbacher–Smith 2.4.25, printed p.542.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A subgroup containing half a Sylow cannot have index divisible by four. -/
theorem not_four_dvd_index_of_half_sylow (S : Sylow 2 G) {R J : Subgroup G}
    (hRS : R ≤ S) (hi : R.relIndex S ≤ 2) (hRJ : R ≤ J) : ¬ 4 ∣ J.index := by
  intro hd
  have hdR := hd.trans (index_dvd_of_le hRJ)
  rw [←relIndex_mul_index hRS] at hdR
  have ho : Odd (S : Subgroup G).index := Nat.odd_iff.mpr (by have := S.not_dvd_index; omega)
  have hcop : Nat.Coprime 4 (S : Subgroup G).index :=
    (Nat.coprime_two_left.mpr ho).pow_left 2
  have hh := hcop.dvd_of_dvd_mul_right hdR
  have hn : 0 < R.relIndex S := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have := Nat.le_of_dvd hn hh
  omega

/-- The index-four test lifts through the actual two-core in a two-perfect group. -/
theorem solvable_of_not_four_dvd_index_of_twoCore_quotient
    (hp : IsPPerfect 2 G)
    (hquot : ∀ J : Subgroup (G ⧸ pCore 2 G), J ≠ ⊤ →
      ¬ Group.IsSolvable J → 4 ∣ J.index)
    (H : Subgroup G) (hne : H ≠ ⊤) (hi : ¬ 4 ∣ H.index) : Group.IsSolvable H := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have him : H.map q ≠ ⊤ := by
    intro he
    have hsup : H ⊔ pCore 2 G = ⊤ := by
      have hh := congrArg (comap q) he
      simpa only [comap_map_eq,comap_top,q,QuotientGroup.ker_mk'] using hh
    have hd : H.index ∣ Nat.card (pCore 2 G) := by
      have hm := card_mul_eq_card_inf_mul_card_sup_of_normalizes (pCore 2 G) H
        le_normalizer_of_normal
      rw [sup_comm,hsup,card_top,←H.card_mul_index] at hm
      have hh : Nat.card (pCore 2 G) = Nat.card (pCore 2 G ⊓ H : Subgroup G) * H.index := by
        apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := H))
        simpa only [mul_assoc,mul_comm,mul_left_comm] using hm
      exact ⟨Nat.card (pCore 2 G ⊓ H : Subgroup G), by simpa [mul_comm] using hh⟩
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    obtain ⟨m,_,hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (hn ▸ hd)
    have hm2 : m < 2 := by
      by_contra hh
      exact hi (hm ▸ pow_dvd_pow 2 (by omega : 2 ≤ m))
    have hi12 : H.index = 1 ∨ H.index = 2 := by
      have hm01 : m = 0 ∨ m = 1 := by omega
      rcases hm01 with rfl | rfl <;> simp_all
    rcases hi12 with he | he
    · exact hne (index_eq_one.mp he)
    · let : H.Normal := normal_of_index_eq_two he
      exact hne (hp H inferInstance (IsPGroup.of_card (n := 1)
        (by simpa only [←index_eq_card,pow_one] using he)))
  have hs : Group.IsSolvable (H.map q) := by
    by_contra hns
    exact hi ((hquot _ him hns).trans (H.index_map_dvd (QuotientGroup.mk'_surjective _)))
  let := hs
  let := pCore_isNilpotent (p := 2) (G := G)
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  let := isSolvable_comap_of_solvable_ker q (H.map q)
  exact Group.isSolvable_of_isSolvable_injective
    (f := inclusion (le_comap_map q H)) (inclusion_injective _)
end Theory.GroupTheory
