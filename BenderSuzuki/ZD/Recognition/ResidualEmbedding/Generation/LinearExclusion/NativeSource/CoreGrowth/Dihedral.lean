module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearExclusion.NativeSource.Freeness
public import Glauberman.DicksonSylowNormalizer
public import Glauberman.DicksonCase823

/-!
# The intrinsic dihedral case in Lemma 15.3

An even subgroup H of PSL₂(q) with order coprime to q−1 has a
self-normalizing Sylow two-subgroup: its normalizer quotient has order
dividing both |H| and q−1. Dickson's self-normalizing Sylow theorem then
leaves an elementary two-group or a dihedral group. Excluding the former
leaves odd rotation order dividing q+1. The impossible third case would
make a power of two equal to three.

Apply this to the actual image of J under the proved centralizer embedding.
The isomorphism transports back to J, retaining the original parameter q.
Source: GLS IV, Chapter 2, Lemma 15.3; Huppert II.8.21 and II.8.23.
-/

noncomputable section
namespace BenderSuzuki.ZD.LinearExclusion
open Subgroup Theory.GroupTheory PFAppendixIII
universe u

private theorem dihedral_of_even_coprime_split
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 2 ≤ n)
    (H : Subgroup (MatrixGroups.PSL2MatrixGroup F))
    (heven : Even (Nat.card H)) (hnot : ¬ IsPGroup 2 H)
    (hcop : Nat.Coprime (Nat.card H) (2 ^ n - 1)) :
    ∃ r : ℕ, Odd r ∧ r ∣ 2 ^ n + 1 ∧ Nat.card H = 2 * r ∧
      Nonempty (H ≃* DihedralGroup r) := by
  let P : Sylow 2 H := Classical.choice inferInstance
  have hPdiv : 2 ∣ Nat.card P := P.dvd_card_of_dvd_card heven.two_dvd
  have hPne : (P : Subgroup H) ≠ ⊥ := by
    intro he
    have ho : Nat.card P = 1 := he ▸ Subgroup.card_bot
    rw [ho] at hPdiv
    omega
  let N := normalizer (P : Set H)
  let PN := (P : Subgroup H).subgroupOf N
  let : PN.Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  have hdiv := (Glauberman.Dickson.h821_borel_quotient_data hF H P hPne N rfl PN rfl).2.1
  have hdivq : Nat.card (N ⧸ PN) ∣ 2 ^ n - 1 := by
    rw [← hF]
    exact hdiv.trans (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))
  have hdivH : Nat.card (N ⧸ PN) ∣ Nat.card H :=
    (Subgroup.card_quotient_dvd_card PN).trans N.card_subgroup_dvd_card
  have hcard : Nat.card (N ⧸ PN) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdivH hdivq
  have hPN : PN = ⊤ := (Subgroup.index_eq_one).mp hcard
  have hNorm : normalizer (P : Set H) = (P : Subgroup H) := by
    have hmap : PN.map N.subtype = (P : Subgroup H) :=
      map_subgroupOf_eq_of_le (show (P : Subgroup H) ≤ N from (P : Subgroup H).le_normalizer)
    have he := congrArg (Subgroup.map N.subtype) hPN
    rw [hmap, ← MonoidHom.range_eq_map, N.range_subtype] at he
    exact he.symm
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hpow : 1 < 2 ^ k := by
    rw [← hk]
    have := Nat.card_pos (α := P)
    omega
  rcases Glauberman.Dickson.huppert_II_8_23_dickson_case_p_part_normalizer_self
      hF H P hk hpow hNorm with htwo | ⟨_, r, hr, hrd, hc, he⟩ | ⟨hthree, _⟩
  · exact (hnot (IsPGroup.of_card htwo.1)).elim
  · have hodd : Odd (2 ^ n - 1) := Nat.Even.sub_odd Nat.one_le_two_pow
      (even_two.pow_of_ne_zero (by omega : n ≠ 0)) odd_one
    have hg : Nat.gcd (2 ^ n - 1) 2 = 1 := hodd.coprime_two_right
    simp only [hF, hg, Nat.div_one] at hrd
    refine ⟨r, Nat.not_even_iff_odd.mp (fun h => hr h.two_dvd), ?_, hc, he⟩
    rcases hrd with hminus | hplus
    · have hrH : r ∣ Nat.card H := by rw [hc]; exact dvd_mul_left _ _
      have hr1 : r = 1 := Nat.eq_one_of_dvd_coprimes hcop hrH hminus
      rw [hr1]
      exact one_dvd _
    · exact hplus
  · cases k with
    | zero => norm_num at hthree
    | succ k => rw [pow_succ] at hthree; omega

variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {n : ℕ} (d : Context Z M z t n)
include d

/-- The original J is odd-dihedral once the source coprimality is proved. -/
public theorem Context.centralizer_dihedral_of_coprime
    (hnot : ¬ IsPGroup 2 (centralizer (residualGenerated M z t : Set G)))
    (hcop : Nat.Coprime (Nat.card (centralizer (residualGenerated M z t : Set G)))
      (2 ^ n - 1)) :
    ∃ r : ℕ, Odd r ∧ r ∣ 2 ^ n + 1 ∧
      Nat.card (centralizer (residualGenerated M z t : Set G)) = 2 * r ∧
      Nonempty (centralizer (residualGenerated M z t : Set G) ≃* DihedralGroup r) := by
  obtain ⟨hm⟩ := d.centralizerLocalModelData
  let f := d.model.toMonoidHom.comp hm.embedding
  have hf : Function.Injective f := d.model.injective.comp hm.embedding_injective
  let e := MonoidHom.ofInjective hf
  have hc : Nat.card f.range = Nat.card (centralizer (residualGenerated M z t : Set G)) :=
    (Nat.card_congr e.toEquiv).symm
  obtain ⟨r, hr, hrd, hcard, ⟨er⟩⟩ := dihedral_of_even_coprime_split
    (GaloisField.card 2 n (by have := d.parameter; omega)) d.parameter
    f.range (hc ▸ d.centralizer_even)
    (fun hh => hnot (hh.of_equiv e.symm)) (hc ▸ hcop)
  exact ⟨r, hr, hrd, hc.symm.trans hcard, ⟨e.trans er⟩⟩

end BenderSuzuki.ZD.LinearExclusion
