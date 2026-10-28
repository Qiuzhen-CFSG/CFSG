module
public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.PrimitiveEight.FiveDivisor
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Theory.GroupAction.SimpleCosets

/-!
# Excluding the three-divisible small indices in A₈

There is no subgroup of A₈ of index 3, 6, 12 or 24. Each putative subgroup
has order divisible by five and seven. A seven-cycle has a unique fixed
point; if the subgroup is transitive, every block through that point is
trivial. The proved degree-eight factor-five criterion then forces A₈.
If the subgroup is intransitive, the same cycle forces a common fixed point.
Restriction embeds the subgroup in A₇, where Lagrange's theorem excludes
all orders except 840. That last order would give an index-three subgroup
of the simple group A₇, contradicting its faithful coset action.

This is the permutation-degree obstruction used for the M₂₄ case of
Aschbacher–Smith, A.3.12(14), printed pp.47–48. The factor-five criterion
uses only the proved multiple-primitivity and three-cycle forms of Jordan's
theorem; no general prime-cycle assertion or subgroup catalogue is used.
-/

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.MathieuLocalSections.Intransitivity

open Equiv Equiv.Perm MulAction Subgroup
open scoped Pointwise

private theorem seven_cycle_fixed (g : Perm (Fin 8)) (hc : g.IsCycle)
    (ho : orderOf g = 7) : ∃ a : Fin 8, ∀ x, g x = x ↔ x = a := by
  have hs : g.support.card = 7 := hc.orderOf.symm.trans ho
  have hf : g.supportᶜ.card = 1 := by simp [Finset.card_compl, hs]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hf
  exact ⟨a, fun x => by simpa using (show x ∈ g.supportᶜ ↔ x ∈ ({a} : Finset (Fin 8)) by rw [ha])⟩

private theorem primitive_of_seven_cycle (V : Subgroup (Perm (Fin 8)))
    [IsPretransitive V (Fin 8)] (g : Perm (Fin 8)) (hg : g ∈ V) (hc : g.IsCycle)
    (a : Fin 8) (ha : ∀ x, g x = x ↔ x = a) : IsPreprimitive V (Fin 8) := by
  apply IsPreprimitive.of_isTrivialBlock_base a
  intro D haD hD
  by_cases hsub : D ⊆ {a}
  · left
    intro x hx y hy
    exact (Set.mem_singleton_iff.mp (hsub hx)).trans
      (Set.mem_singleton_iff.mp (hsub hy)).symm
  · right
    obtain ⟨b, hbD, hba⟩ : ∃ b ∈ D, b ≠ a := by simpa [Set.subset_def] using hsub
    apply Set.eq_univ_of_forall
    intro x
    by_cases hxa : x = a
    · simpa [hxa] using haD
    obtain ⟨n, hn⟩ := hc.exists_pow_eq (fun h => hba ((ha b).mp h))
      (fun h => hxa ((ha x).mp h))
    let k : V := ⟨g ^ n, V.pow_mem hg n⟩
    have hka : k • a = a := pow_apply_eq_self_of_apply_eq_self ((ha a).mpr rfl) n
    have he : k • D = D := (isBlock_iff_smul_eq_of_mem.mp hD) haD (by rwa [hka])
    rw [← he]
    exact ⟨b, hbD, hn⟩

private theorem fixed_of_intransitive (V : Subgroup (Perm (Fin 8)))
    (ht : ¬ IsPretransitive V (Fin 8)) (g : Perm (Fin 8)) (hg : g ∈ V)
    (hc : g.IsCycle) (a : Fin 8) (ha : ∀ x, g x = x ↔ x = a) :
    ∀ k : V, k • a = a := by
  intro k
  by_contra hk
  apply ht
  apply (isPretransitive_iff_base a).mpr
  intro x
  by_cases hxa : x = a
  · exact ⟨1, by simp [hxa]⟩
  obtain ⟨n, hn⟩ := hc.exists_pow_eq (fun h => hk ((ha (k • a)).mp h))
    (fun h => hxa ((ha x).mp h))
  exact ⟨⟨g ^ n, V.pow_mem hg n⟩ * k, hn⟩

private theorem card_alt_eight : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
  rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]

private theorem small_fixed_subgroup (U : Subgroup (alternatingGroup (Fin 8)))
    (a : Fin 8) (hfix : ∀ u : U, u • a = a)
    (hcard : Nat.card U = 6720 ∨ Nat.card U = 3360 ∨
      Nat.card U = 1680 ∨ Nat.card U = 840) : False := by
  let s : Finset (Fin 8) := {a}ᶜ
  have hs : Nat.card s = 7 := by simp [s, Nat.card_eq_fintype_card]
  let : Nontrivial s := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let f := alternatingGroup.ofSubtype s
  have hle : U ≤ f.range := by
    intro u hu
    apply (alternatingGroup.mem_range_ofSubtype_iff s u).mpr
    intro x hx
    simp only [s, Finset.mem_compl, Finset.mem_singleton]
    intro he
    subst x
    exact (mem_support.mp hx) (hfix ⟨u, hu⟩)
  let e := MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := s))
  let W : Subgroup (alternatingGroup s) := (U.subgroupOf f.range).map e.symm.toMonoidHom
  have hW : Nat.card W = Nat.card U := by
    rw [card_map_of_injective e.symm.injective]
    exact Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv
  have hc : Nat.card (alternatingGroup s) = 2520 := by
    rw [nat_card_alternatingGroup, hs]; norm_num [Nat.factorial]
  have hd := W.card_subgroup_dvd_card
  rw [hW, hc] at hd
  rcases hcard with hcard | hcard | hcard | hcard
  · norm_num [hcard] at hd
  · norm_num [hcard] at hd
  · norm_num [hcard] at hd
  · have hi : W.index = 3 := by
      have hm := W.card_mul_index
      rw [hW, hcard, hc] at hm
      omega
    let : IsSimpleGroup (alternatingGroup s) := alternatingGroup.isSimpleGroup (by omega)
    have hn : W ≠ ⊤ := by intro he; simp [he] at hi
    have hh := W.card_dvd_factorial_index_of_simple hn
    rw [hc, hi] at hh
    norm_num [Nat.factorial] at hh

/-- A subgroup of A₈ whose index divides 24 has index prime to three. -/
public theorem alternatingEight_index_not_three_dvd
    (U : Subgroup (alternatingGroup (Fin 8))) (hd : U.index ∣ 24) :
    ¬ 3 ∣ U.index := by
  intro h3
  have hi : U.index = 3 ∨ U.index = 6 ∨ U.index = 12 ∨ U.index = 24 := by
    have hb : U.index ≤ 24 := Nat.le_of_dvd (by decide) hd
    interval_cases U.index <;> omega
  have hc : Nat.card U = 6720 ∨ Nat.card U = 3360 ∨
      Nat.card U = 1680 ∨ Nat.card U = 840 := by
    have hm := U.card_mul_index
    rw [card_alt_eight] at hm
    rcases hi with hi | hi | hi | hi <;> rw [hi] at hm <;> omega
  let V := U.map (alternatingGroup (Fin 8)).subtype
  have hV : Nat.card V = Nat.card U := card_map_of_injective Subtype.val_injective
  have h7 : 7 ∣ Nat.card V := by
    rw [hV]; rcases hc with hc | hc | hc | hc <;> norm_num [hc]
  have h5 : 5 ∣ Nat.card V := by
    rw [hV]; rcases hc with hc | hc | hc | hc <;> norm_num [hc]
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := V) 7 h7
  have ho : orderOf (g : Perm (Fin 8)) = 7 := by simpa using hg
  have hgc : (g : Perm (Fin 8)).IsCycle := isCycle_of_prime_order'
    (by rw [ho]; decide) (by rw [ho]; decide)
  obtain ⟨a, ha⟩ := seven_cycle_fixed g hgc ho
  by_cases ht : IsPretransitive V (Fin 8)
  · let := ht
    let := primitive_of_seven_cycle V g g.property hgc a ha
    have hle := CFSG.Quasithin.MainConverse.primitiveEight_alternating_le_of_five_dvd V h5
    have hge : V ≤ alternatingGroup (Fin 8) := map_subtype_le _
    have he : V = alternatingGroup (Fin 8) := le_antisymm hge hle
    rw [he, card_alt_eight] at hV
    omega
  · apply small_fixed_subgroup U a _ hc
    intro u
    exact fixed_of_intransitive V ht g g.property hgc a ha
      ⟨u.val.val, mem_map.mpr ⟨u.val, u.property, rfl⟩⟩

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.MathieuLocalSections.Intransitivity
