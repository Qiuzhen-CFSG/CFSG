module
public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.Quasithin.Rank
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Normalizers of two-subgroups in the seven-point symmetric group

An elementary eight is conjugate to one of the two standard eight-groups;
each has a unique element of a specified support size. A two-subgroup with
an element of order four has a unique nonidentity square. In each case the
normalizer fixes that permutation and lies in its centralizer, of order48
or240. Thus its three-rank is at most one.

The finite checks use only the existing eight- and sixteen-word Sylow
coordinates. Source application: Aschbacher–Smith C.2.7(3),15.3.21.
-/


@[expose] public section
open Subgroup Equiv
namespace Theory.SpecificGroups.SymmetricSeven.EightNormalizers
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry

private theorem rank_three_le_one_of_card {H : Type*} [Group H] [Finite H]
    (hc : Nat.card H = 48 ∨ Nat.card H = 240) : primeRank 3 H ≤ 1 := by
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let : IsElementaryAbelian 3 E := hE
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 3 E).exists_card_eq
  have hd := E.card_subgroup_dvd_card
  rcases hc with hc | hc
  · have hd : Nat.card E ∣ 3 * 16 := by simpa only [hc] using hd
    have hp : Nat.Coprime (Nat.card E) 16 := by
      rw [hn]; exact (by decide : Nat.Coprime 3 16).pow_left n
    exact Nat.le_of_dvd (by decide) (hp.dvd_mul_right.mp hd)
  · have hd : Nat.card E ∣ 3 * 80 := by simpa only [hc] using hd
    have hp : Nat.Coprime (Nat.card E) 80 := by
      rw [hn]; exact (by decide : Nat.Coprime 3 80).pow_left n
    exact Nat.le_of_dvd (by decide) (hp.dvd_mul_right.mp hd)

private theorem normalizer_rank_transport (A : Subgroup S7) (g : S7)
    (h : primeRank 3 (normalizer (A.map (MulAut.conj g).toMonoidHom : Set S7)) ≤ 1) :
    primeRank 3 (normalizer (A : Set S7)) ≤ 1 := by
  let e := (MulAut.conj g).subgroupMap (normalizer (A : Set S7))
  have he := primeRank_congr 3 e
  change primeRank 3 (normalizer (A : Set S7)) =
    primeRank 3 ((normalizer (A : Set S7)).map (MulAut.conj g).toMonoidHom) at he
  rw [map_equiv_normalizer_eq] at he
  exact he.trans_le h

private theorem unique_support_fixed (A : Subgroup S7) (z : S7) (hz : z ∈ A)
    (hunique : ∀ x ∈ A, x.support.card = z.support.card → x = z) :
    normalizer (A : Set S7) ≤ centralizer ({z} : Set S7) := by
  intro g hg
  apply mem_centralizer_singleton_iff.mpr
  apply mul_inv_eq_iff_eq_mul.mp
  apply hunique _ ((mem_normalizer_iff.mp hg z).mp hz)
  exact Equiv.Perm.card_support_conj

private theorem pair_normalizer_rank :
    primeRank 3 (normalizer (pairElementary : Set S7)) ≤ 1 := by
  let z := swap01 * swap23 * swap45
  have hz : z ∈ pairElementary := ⟨(1,1,1),by decide +kernel⟩
  have hu : ∀ x ∈ pairElementary, x.support.card = z.support.card → x = z := by
    rintro _ ⟨v,rfl⟩
    exact (by decide +kernel : ∀ v : Triple,
      (firstWord v).support.card = (swap01 * swap23 * swap45).support.card →
        firstWord v = swap01 * swap23 * swap45) v
  apply (primeRank_mono 3 (unique_support_fixed pairElementary z hz hu)).trans
  apply rank_three_le_one_of_card
  left
  rw [Equiv.Perm.nat_card_centralizer]
  have hztype : z.cycleType = {2,2,2} := by decide +kernel
  rw [hztype]
  norm_num [Nat.factorial]

private theorem fourTwo_normalizer_rank :
    primeRank 3 (normalizer (fourTwoElementary : Set S7)) ≤ 1 := by
  have hz : swap45 ∈ fourTwoElementary := swap45_mem_fourTwoElementary
  have hu : ∀ x ∈ fourTwoElementary, x.support.card = swap45.support.card → x = swap45 := by
    rintro _ ⟨v,rfl⟩
    exact (by decide +kernel : ∀ v : Triple,
      (secondWord v).support.card = swap45.support.card → secondWord v = swap45) v
  apply (primeRank_mono 3 (unique_support_fixed fourTwoElementary swap45 hz hu)).trans
  apply rank_three_le_one_of_card
  right
  rw [Equiv.Perm.nat_card_centralizer]
  have hztype : swap45.cycleType = {2} := by decide +kernel
  rw [hztype]
  norm_num [Nat.factorial]

/-- An elementary eight in S7 has normalizer of three-rank at most one. -/
theorem elementary_normalizer_rank (A : Subgroup S7)
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 8) :
    primeRank 3 (normalizer (A : Set S7)) ≤ 1 := by
  obtain ⟨g,hg | hg⟩ := elementary_conjugate_le hA
  · have he : A.map (MulAut.conj g).toMonoidHom = pairElementary :=
      eq_of_le_of_card_ge hg (by rw [card_map_of_injective (MulAut.conj g).injective,hc,pairElementary_card])
    apply normalizer_rank_transport A g
    rw [he]
    exact pair_normalizer_rank
  · have he : A.map (MulAut.conj g).toMonoidHom = fourTwoElementary :=
      eq_of_le_of_card_ge hg (by rw [card_map_of_injective (MulAut.conj g).injective,hc,fourTwoElementary_card])
    apply normalizer_rank_transport A g
    rw [he]
    exact fourTwo_normalizer_rank

private theorem word_square_unique (v : Quadruple) (hv : word v ^ 2 ≠ 1) :
    word v ^ 2 = swap01 * swap23 :=
  (by decide +kernel : ∀ v : Quadruple,
    word v ^ 2 ≠ 1 → word v ^ 2 = swap01 * swap23) v hv

/-- Every non-elementary two-subgroup of S7 has a unique nontrivial square.
Its normalizer fixes the corresponding double transposition. -/
theorem noninvolution_normalizer_rank (A : Subgroup S7) (hA : IsPGroup 2 A)
    (hx : ∃ x ∈ A, x ^ 2 ≠ 1) :
    primeRank 3 (normalizer (A : Set S7)) ≤ 1 := by
  obtain ⟨P,hAP⟩ := hA.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq S7 P standardSylow
  have hP : (P : Subgroup S7).map (MulAut.conj g).toMonoidHom = sylowTwo :=
    congrArg Sylow.toSubgroup hg
  let B := A.map (MulAut.conj g).toMonoidHom
  have hB : B ≤ sylowTwo := hP ▸ map_mono hAP
  obtain ⟨x,hxA,hx2⟩ := hx
  let y := (MulAut.conj g) x
  have hyB : y ∈ B := mem_map_of_mem _ hxA
  have hy2 : y ^ 2 ≠ 1 := by
    intro he
    apply hx2
    apply (MulAut.conj g).injective
    simpa only [map_pow,map_one] using he
  obtain ⟨v,hv⟩ := hB hyB
  have hy : y ^ 2 = swap01 * swap23 := by
    rw [←hv]
    exact word_square_unique v (hv ▸ hy2)
  have hn : normalizer (B : Set S7) ≤ centralizer ({swap01 * swap23} : Set S7) := by
    intro b hb
    have hby := (mem_normalizer_iff.mp hb y).mp hyB
    obtain ⟨w,hw⟩ := hB hby
    have hne : (b * y * b⁻¹) ^ 2 ≠ 1 := by
      intro he
      apply hy2
      apply (MulAut.conj b).injective
      simpa only [map_pow,map_one, MulAut.conj_apply] using he
    have he : (b * y * b⁻¹) ^ 2 = swap01 * swap23 := by
      rw [←hw]
      exact word_square_unique w (hw ▸ hne)
    apply mem_centralizer_singleton_iff.mpr
    apply mul_inv_eq_iff_eq_mul.mp
    calc
      b * (swap01 * swap23) * b⁻¹ = b * y ^ 2 * b⁻¹ := by rw [hy]
      _ = (b * y * b⁻¹) ^ 2 := by simp only [pow_two]; group
      _ = swap01 * swap23 := he
  apply normalizer_rank_transport A g
  apply (primeRank_mono 3 hn).trans
  apply rank_three_le_one_of_card
  left
  rw [Equiv.Perm.nat_card_centralizer]
  have hztype : (swap01 * swap23).cycleType = {2,2} := by decide +kernel
  rw [hztype]
  norm_num [Nat.factorial]

end Theory.SpecificGroups.SymmetricSeven.EightNormalizers
