module
public import Theory.SpecificGroups.SymmetricFive.NoForty
public import Theory.SpecificGroups.Alternating.FiveOrderTwentyFour

/-!
# Sylow overgroups and their Borels in the five-point symmetric group

A subgroup containing a Sylow two-subgroup has order divisible by eight.
Lagrange and the exclusion of order forty leave order eight or twenty-four
for a proper subgroup. A Sylow two-subgroup fixes a point of the five-point
set; the existing order-twenty-four theorem gives a point stabilizer in the
other case. A maximal proper overgroup is therefore the actual S₄ stabilizer.

The quotient theorem preserves the original map and identifies its literal
intersection with an A₅ preimage as the even point stabilizer A₄. Kernel
containment is needed only in the maximal overgroup, not in the A₅ preimage.
No subgroups are enumerated; the small cardinal certificate counts the five
point stabilizers inside the sixty-element alternating group.

Source: Aschbacher–Smith, the single alternating case of 2.4.29.
-/

public section
open Subgroup MulAction
namespace Theory.SpecificGroups.SymmetricFive.SylowOvergroup
local notation "S5" => Equiv.Perm (Fin 5)
local notation "A5" => alternatingGroup (Fin 5)

private theorem card_symmetric : Nat.card S5 = 120 := by
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

private theorem card_stabilizer (i : Fin 5) : Nat.card (stabilizer S5 i) = 24 := by
  have hindex : (stabilizer S5 i).index = 5 := by
    rw [index_stabilizer, orbit_eq_univ]
    simp
  have hc := (stabilizer S5 i).card_mul_index
  rw [hindex, card_symmetric] at hc
  omega

private theorem stabilizer_ne_top (i : Fin 5) : stabilizer S5 i ≠ ⊤ := by
  intro h
  have hc := card_stabilizer i
  rw [h, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup S5) ≃* S5).toEquiv, card_symmetric] at hc
  omega

/-- A proper overgroup of a Sylow two-subgroup of S₅ fixes a point. -/
theorem exists_le_point_stabilizer (P : Sylow 2 S5) (B : Subgroup S5)
    (hPB : (P : Subgroup S5) ≤ B) (hB : B ≠ ⊤) :
    ∃ i : Fin 5, B ≤ stabilizer S5 i := by
  have hP : Nat.card P = 8 := by
    rw [P.card_eq_multiplicity, card_symmetric]
    decide +kernel
  have hdiv : Nat.card B ∣ 120 := card_symmetric ▸ B.card_subgroup_dvd_card
  have hdiv8 : 8 ∣ Nat.card B := hP ▸ card_dvd_of_le hPB
  have hnot120 : Nat.card B ≠ 120 := by
    intro h
    apply hB
    apply eq_of_le_of_card_ge le_top
    simp only [Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup S5) ≃* S5).toEquiv, card_symmetric, h, le_refl]
  have hnot40 := _root_.SymmetricFive.subgroup_card_ne_forty B
  have hcases : Nat.card B = 8 ∨ Nat.card B = 24 := by
    have hm := Nat.mem_divisors.mpr ⟨hdiv, by decide⟩
    have hd : Nat.divisors 120 = {1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120} := by
      decide +kernel
    rw [hd] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    omega
  rcases hcases with hcard | hcard
  · have heq : (P : Subgroup S5) = B := eq_of_le_of_card_ge hPB (by omega)
    obtain ⟨i, hi⟩ := P.isPGroup'.nonempty_fixed_point_of_prime_not_dvd_card (Fin 5)
      (by norm_num)
    refine ⟨i, ?_⟩
    rw [← heq]
    intro g hg
    exact hi ⟨g, hg⟩
  · obtain ⟨i, hi⟩ := Alternating.FivePointTwentyFour.exists_eq_stabilizer B hcard
    exact ⟨i, hi.le⟩

/-- A maximal proper Sylow two-overgroup in S₅ is an actual point stabilizer. -/
theorem exists_eq_point_stabilizer (P : Sylow 2 S5) (B : Subgroup S5)
    (hPB : (P : Subgroup S5) ≤ B) (hB : IsCoatom B) :
    ∃ i : Fin 5, B = stabilizer S5 i := by
  obtain ⟨i, hi⟩ := exists_le_point_stabilizer P B hPB hB.1
  exact ⟨i, ((hB.le_iff_eq (stabilizer_ne_top i)).mp hi).symm⟩

/-- The even part of a five-point stabilizer has order twelve. -/
theorem card_even_point_stabilizer (i : Fin 5) :
    Nat.card (A5 ⊓ stabilizer S5 i : Subgroup S5) = 12 := by
  let E : Subgroup A5 := stabilizer A5 i
  have he : E.map (alternatingGroup (Fin 5)).subtype = A5 ⊓ stabilizer S5 i := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.property, hx⟩
    · rintro ⟨ha, hi⟩
      exact ⟨⟨g, ha⟩, hi, rfl⟩
  rw [← he, ← Nat.card_congr (E.equivMapOfInjective (alternatingGroup (Fin 5)).subtype Subtype.val_injective).toEquiv]
  change Nat.card (stabilizer A5 i) = 12
  clear he E
  let : DecidablePred (· ∈ stabilizer A5 i) := fun x =>
    inferInstanceAs (Decidable (x.val i = i))
  rw [Nat.card_eq_fintype_card]
  revert i
  decide +kernel

/-- Maximal Sylow overgroups in a marked S₅ quotient have the original point coordinates. -/
theorem quotient_image_eq_point_stabilizer {H : Type*} [Group H] [Finite H]
    (q : H →* S5) (hq : Function.Surjective q) (P : Sylow 2 H)
    (B : Subgroup H) (hPB : (P : Subgroup H) ≤ B) (hB : IsCoatom B)
    (hker : q.ker ≤ B) :
    ∃ i : Fin 5, B.map q = stabilizer S5 i := by
  have hproper : B.map q ≠ ⊤ := by
    intro h
    apply hB.1
    have hc := congrArg (Subgroup.comap q) h
    rwa [comap_map_eq_self hker, comap_top] at hc
  obtain ⟨i, hi⟩ := exists_le_point_stabilizer (P.mapSurjective hq) (B.map q)
    (map_mono hPB) hproper
  have hle : B ≤ (stabilizer S5 i).comap q := map_le_iff_le_comap.mp hi
  have hp : (stabilizer S5 i).comap q ≠ ⊤ := by
    intro heq
    apply stabilizer_ne_top i
    have hm := congrArg (Subgroup.map q) heq
    rwa [map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top),
      map_top_of_surjective q hq] at hm
  have heq : B = (stabilizer S5 i).comap q := ((hB.le_iff_eq hp).mp hle).symm
  refine ⟨i, ?_⟩
  rw [heq, map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr hq]; exact le_top)]

/-- The literal intersection with an A₅ inverse image maps to the A₄ Borel. -/
theorem quotient_borel {H : Type*} [Group H] [Finite H]
    (q : H →* S5) (hq : Function.Surjective q) (P : Sylow 2 H)
    (B L : Subgroup H) (hPB : (P : Subgroup H) ≤ B) (hB : IsCoatom B)
    (hkerB : q.ker ≤ B) (hL : L.map q = A5) :
    ∃ i : Fin 5, B.map q = stabilizer S5 i ∧
      (B ⊓ L).map q = A5 ⊓ stabilizer S5 i ∧ Nat.card ((B ⊓ L).map q) = 12 := by
  obtain ⟨i, hi⟩ := quotient_image_eq_point_stabilizer q hq P B hPB hB hkerB
  have hpre : (B.map q).comap q = B := comap_map_eq_self hkerB
  have heq : (B ⊓ L).map q = A5 ⊓ stabilizer S5 i := by
    ext x
    constructor
    · rintro ⟨y, ⟨hyB, hyL⟩, rfl⟩
      exact ⟨hL ▸ mem_map_of_mem q hyL, hi ▸ mem_map_of_mem q hyB⟩
    · rintro ⟨hxA, hxB⟩
      obtain ⟨y, hy, rfl⟩ := mem_map.mp (hL.symm ▸ hxA)
      have hyB : y ∈ (B.map q).comap q := hi.symm ▸ hxB
      exact ⟨y, ⟨hpre ▸ hyB, hy⟩, rfl⟩
  exact ⟨i, hi, heq, heq ▸ card_even_point_stabilizer i⟩

end Theory.SpecificGroups.SymmetricFive.SylowOvergroup
