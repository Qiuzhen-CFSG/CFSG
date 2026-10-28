module
public import Theory.Mathieu.M22.Properties.TwoLocalSeven
public import Theory.SpecificGroups.SymmetricFive.PentagonNormalizer
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups

/-!
# Three-free Sylow overgroups in the native M₂₂ carrier

A subgroup containing a full Sylow two-subgroup and having order prime to
three and eleven cannot be transitive on the actual 22 points. Native
coverage places it in a hexad or pair stabilizer. The genuine restriction
maps have kernel sixteen and image in A₆ or S₅. Their full Sylow overgroups
of order prime to three have order eight; in S₅ the only competing order,
forty, would normalize a five-subgroup whose full normalizer has order twenty.
Thus the original subgroup has order 128.

This supplies the original prime-five exclusion in Aschbacher--Smith
15.1.22(5), printed pp.1099--1100, using the actual actor of 15.1.21(ii).
The native pair and hexad geometry is E.4.3(2), pp.241--242, and GLS3
Table 5.3c. No solvability or exhaustive sporadic classification is assumed.
-/

public section
open Subgroup MulAction
open scoped Pointwise
namespace Sporadic.Mathieu.M22QuinticSylow

private theorem symmetric_five_not_forty (H : Subgroup (Equiv.Perm (Fin 5))) :
    Nat.card H ≠ 40 := by
  intro hc
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let P : Sylow 5 H := Classical.choice inferInstance
  have hP : Nat.card P = 5 := by
    rw [Sylow.card_eq_multiplicity,hc]
    decide +kernel
  have hi : (P : Subgroup H).index = 8 := by
    have hh := (P : Subgroup H).card_mul_index
    rw [hP,hc] at hh
    omega
  have hn : Nat.card (Sylow 5 H) = 1 := by
    have hd := P.card_dvd_index
    rw [hi] at hd
    have hm := card_sylow_modEq_one 5 H
    have hb := Nat.le_of_dvd (by decide : 0 < 8) hd
    change Nat.card (Sylow 5 H) % 5 = 1 % 5 at hm
    interval_cases hn : Nat.card (Sylow 5 H) <;> omega
  let : Subsingleton (Sylow 5 H) := (Nat.card_eq_one_iff_unique.mp hn).1
  let : (P : Subgroup H).Normal := P.normal_of_subsingleton
  let Q := (P : Subgroup H).map H.subtype
  have hQ : Nat.card Q = 5 := (card_map_of_injective H.subtype_injective).trans hP
  have hHQ : H ≤ normalizer (Q : Set (Equiv.Perm (Fin 5))) := by
    have hh := (P : Subgroup H).le_normalizer_map H.subtype
    rwa [normalizer_eq_top, ←MonoidHom.range_eq_map,range_subtype] at hh
  have hd := card_dvd_of_le hHQ
  rw [hc,Equiv.Perm.five_subgroup_normalizer_card Q hQ] at hd
  norm_num at hd

private theorem pair_image_eight (H : Subgroup (Equiv.Perm (Fin 5)))
    (h8 : 8 ∣ Nat.card H) (h3 : ¬3 ∣ Nat.card H) : Nat.card H = 8 := by
  have hd : Nat.card H ∣ 120 := by
    simpa [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] using H.card_subgroup_dvd_card
  have he : ∀ n ∈ (120 : ℕ).divisors, 8 ∣ n → ¬3 ∣ n → n = 8 ∨ n = 40 := by
    decide +kernel
  exact (he _ (Nat.mem_divisors.mpr ⟨hd,by decide⟩) h8 h3).resolve_right
    (symmetric_five_not_forty H)

open M22SolvableSylow.LocalClassification

/-- A native Sylow overgroup in a pair stabilizer, of order prime to three,
is itself a Sylow two-subgroup. -/
private theorem pair_card (X : Subgroup M22) (hX : X ≤ M22ValueBound.Concrete.first)
    (P : Sylow 2 M22) (hPX : (P : Subgroup M22) ≤ X)
    (h3 : ¬3 ∣ Nat.card X) : Nat.card X = 128 := by
  have hP : Nat.card P = 128 := by
    rw [Sylow.card_eq_multiplicity,m22_order]
    decide +kernel
  have h128 : 128 ∣ Nat.card X := hP ▸ card_dvd_of_le hPX
  have hc := pair_card_formula X hX ⟨P,hPX⟩
  have h8 : 8 ∣ Nat.card ((X.subgroupOf M22ValueBound.Concrete.first).map
      M22ValueBound.Concrete.pairAction) := by omega
  have hthree : ¬3 ∣ Nat.card ((X.subgroupOf M22ValueBound.Concrete.first).map
      M22ValueBound.Concrete.pairAction) := by
    intro hh
    apply h3
    rw [hc]
    exact dvd_mul_of_dvd_right hh 16
  rw [pair_image_eight _ h8 hthree] at hc
  exact hc

/-- A native Sylow overgroup in a hexad stabilizer, of order prime to three,
is itself a Sylow two-subgroup. -/
private theorem hexad_card {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (X : Subgroup M22) (hX : X ≤ stabilizer M22 B)
    (P : Sylow 2 M22) (hPX : (P : Subgroup M22) ≤ X)
    (h3 : ¬3 ∣ Nat.card X) : Nat.card X = 128 := by
  let f := hexadRestriction hB
  let I := (X.subgroupOf (stabilizer M22 B)).map f
  let Q := (P.subtype (hPX.trans hX)).mapSurjective (hexadRestriction_surjective hB)
  have hQI : (Q : Subgroup (alternatingGroup (Fin 6))) ≤ I := map_mono (comap_mono hPX)
  have hc := hexad_card_formula hB X hX ⟨P,hPX⟩
  have h3I : ¬3 ∣ Nat.card I := by
    intro hh
    apply h3
    rw [hc]
    exact dvd_mul_of_dvd_right hh 16
  have hItop : I ≠ ⊤ := by
    intro he
    have hh : Nat.card I = 360 := by
      rw [he,card_top,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    exact h3I (by rw [hh]; decide)
  rcases AlternatingSix.ProperSylowOvergroups.card_eight_or_twentyFour Q I hQI hItop with hh | hh
  · change Nat.card X = 16 * Nat.card I at hc
    rwa [hh] at hc
  · exact (h3I (by rw [hh]; decide)).elim

/-- An M₂₂ overgroup of its full Sylow two-subgroup whose order is prime
to three and eleven has order 128. This uses the actual degree-22 action. -/
theorem card_eq_128 (P : Sylow 2 M22) (X : Subgroup M22)
    (hPX : (P : Subgroup M22) ≤ X)
    (h3 : ¬3 ∣ Nat.card X) (h11 : ¬11 ∣ Nat.card X) : Nat.card X = 128 := by
  have ht : ¬IsPretransitive X (Fin 22) := by
    intro ht
    let := ht
    have hd : 22 ∣ Nat.card X := by
      have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup X (0 : Fin 22))
      rw [Nat.card_prod,orbit_eq_univ] at hh
      simp only [Nat.card_fin,Nat.card_coe_set_eq,Set.ncard_univ] at hh
      exact ⟨_,hh.symm⟩
    exact h11 ((by decide : 11 ∣ 22).trans hd)
  rcases M22SolvableSylow.coverage_of_not_pretransitive X ⟨P,hPX⟩ ht with
    ⟨B,hB,hXB⟩ | ⟨B,hB,hXB⟩
  · exact hexad_card hB X hXB P hPX h3
  · obtain ⟨g,hg⟩ := exists_smul_pair_eq_standard hB
    let a := MulAut.conj g
    have hmap : X.map a.toMonoidHom ≤ M22ValueBound.Concrete.first := by
      have hh := map_mono (f := a.toMonoidHom) hXB
      rwa [←stabilizer_smul_eq_stabilizer_map_conj g B,hg] at hh
    have hh := pair_card (X.map a.toMonoidHom) hmap (P.mapSurjective a.surjective)
      (map_mono hPX) (by rwa [card_map_of_injective a.injective])
    rwa [card_map_of_injective a.injective] at hh

end Sporadic.Mathieu.M22QuinticSylow
