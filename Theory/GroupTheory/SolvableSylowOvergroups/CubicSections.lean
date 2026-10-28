module
public import Theory.GroupTheory.SolvableSylowOvergroups.OrderActors
public import Mathlib.Tactic.NormNum

/-!
# Cubic odd parts in small nonsolvable quotient sections

For a surjection with a two-group kernel onto a nonsolvable group of order
120 or 168, a solvable full-Sylow overgroup containing a cubic has image
order exactly 24. Odd subgroups inject through the two-kernel, so their
orders divide three. The source applications use the actual S₅ and L₃(2)
local quotient maps in Higman–Sims and Rudvalis.
Source: the local inspection in Aschbacher--Smith 5.1.13, printed p.637.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory

/-- The odd part is cubic in a solvable full-Sylow overgroup whose image contains a cubic. -/
theorem odd_card_dvd_three_of_small_nonsolvable_quotient
    {X Q : Type*} [Group X] [Finite X] [Group Q] [Finite Q]
    (f : X →* Q) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hcard : Nat.card Q = 120 ∨ Nat.card Q = 168) (hns : ¬ Group.IsSolvable Q)
    (S : Sylow 2 X) (J E : Subgroup X) (hSJ : (S : Subgroup X) ≤ J)
    (hs : Group.IsSolvable J) (h3 : 3 ∣ Nat.card J)
    (hEJ : E ≤ J) (ho : Odd (Nat.card E)) : Nat.card E ∣ 3 := by
  let := hs
  let : Group.IsSolvable (J.map f) := Group.isSolvable_of_surjective (f.subgroupMap_surjective J)
  let P := S.mapSurjective hf
  have h8 : Nat.card P = 8 := by
    rw [P.card_eq_multiplicity]
    rcases hcard with hcard | hcard <;> rw [hcard] <;> decide +kernel
  have h8J : 8 ∣ Nat.card (J.map f) := h8 ▸ card_dvd_of_le (map_mono hSJ)
  have h3J : 3 ∣ Nat.card (J.map f) := by
    let g := f.comp J.subtype
    have hkg : IsPGroup 2 g.ker := hk.comap_subtype
    obtain ⟨a,ha⟩ := hkg.exists_card_eq
    have hc : Nat.Coprime 3 (Nat.card g.ker) := by
      rw [ha]; exact (by decide : Nat.Coprime 3 2).pow_right a
    have he := g.ker.card_mul_index
    rw [index_ker] at he
    rw [←he] at h3
    have hh := hc.dvd_of_dvd_mul_left h3
    simpa only [g,MonoidHom.range_comp,range_subtype] using hh
  have hne : Nat.card (J.map f) ≠ Nat.card Q := by
    intro he
    have ht : J.map f = ⊤ := eq_top_of_card_eq _ he
    apply hns
    exact Group.isSolvable_of_surjective (f := (J.map f).subtype)
      (by rw [ht]; exact topEquiv.surjective)
  have h24 : Nat.card (J.map f) = 24 := by
    have hd := (J.map f).card_subgroup_dvd_card
    rcases hcard with hcard | hcard
    · rw [hcard] at hd hne
      have ht : ∀ m ∈ (120 : ℕ).divisors, 8 ∣ m → 3 ∣ m → m ≠ 120 → m = 24 := by decide +kernel
      exact ht _ (Nat.mem_divisors.mpr ⟨hd,by decide⟩) h8J h3J hne
    · rw [hcard] at hd hne
      have ht : ∀ m ∈ (168 : ℕ).divisors, 8 ∣ m → 3 ∣ m → m ≠ 168 → m = 24 := by decide +kernel
      exact ht _ (Nat.mem_divisors.mpr ⟨hd,by decide⟩) h8J h3J hne
  have hi : Function.Injective (f.comp E.subtype) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    have hd : Disjoint E f.ker := by
      apply disjoint_of_coprime_natCard
      obtain ⟨k,hk⟩ := hk.exists_card_eq
      rw [hk]
      exact ho.coprime_two_right.pow_right k
    exact Subtype.ext (disjoint_def.mp hd x.property hx)
  have he : Nat.card (E.map f) = Nat.card E := by
    have hh := (Nat.card_congr (MonoidHom.ofInjective hi).toEquiv).symm
    simpa only [MonoidHom.range_comp,range_subtype] using hh
  have hd := card_dvd_of_le (map_mono (f := f) hEJ)
  rw [he,h24] at hd
  exact (ho.coprime_two_right.pow_right 3).dvd_of_dvd_mul_left hd

end Theory.GroupTheory
