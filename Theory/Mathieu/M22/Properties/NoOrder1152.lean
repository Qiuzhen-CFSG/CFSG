module

public import Theory.Mathieu.M22.Properties.HexadExtension
public import Theory.Mathieu.M22.Properties.FixedHexads
public import Theory.GroupAction.SimpleCosets
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# No subgroup of order 1152 in the concrete M₂₂

An order-1152 subgroup has odd index 385. Its orbits in the natural action
on 22 points therefore have even length. Orbit-stabilizer and an exhaustive
check of the divisors of 1152 force an orbit of size two, four, or six:
without these, an orbit of size eighteen leaves only four points, and all
remaining possible orbit lengths are divisible by four.

A two-point orbit contradicts the pair stabilizer's order 1920. For a
four- or six-point orbit, the restriction kernel has even order. An
involution in this kernel places the orbit inside its fixed hexad, and
uniqueness of a hexad through three points makes the subgroup preserve
that hexad. It then has index five in a group with quotient A₆. Its image
in A₆ has index dividing five; orders exclude index one, and simplicity
and the coset action exclude index five.

This supplies the M₂₂ subgroup-order obstruction used in the sporadic
case of Aschbacher–Smith, Proposition 1.3.4, printed p.511 (PDF p.528),
which cites Aschbacher (1986), *Overgroups of Sylow subgroups in sporadic
groups*. Compare GLS3, Table 5.3c. The proof uses the actual degree-22
Witt design and its checked stabilizer quotients, without an exhaustive
maximal-subgroup table.
-/

open MulAction Subgroup
open scoped Pointwise

namespace Sporadic.Mathieu

/-- The actual A₆ quotient rules out index five in a hexad stabilizer. -/
private theorem hexad_exclusion {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (H : Subgroup M22) (hH : Nat.card H = 1152)
    (hle : H ≤ stabilizer M22 B) : False := by
  let K := stabilizer M22 B
  let L := H.subgroupOf K
  have hL : Nat.card L = 1152 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans hH
  have hi : L.index = 5 := by
    have hc := L.card_mul_index
    rw [hL, m22Hexad_stabilizer_card hB] at hc
    omega
  let f : K →* alternatingGroup (Fin 6) :=
    (m22HexadQuotientAlternatingEquiv hB).toMonoidHom.comp
      (QuotientGroup.mk' (m22SetAction B).ker)
  have hf : Function.Surjective f :=
    (m22HexadQuotientAlternatingEquiv hB).surjective.comp (QuotientGroup.mk'_surjective _)
  let R := L.map f
  have hRidx : R.index ∣ 5 := hi ▸ L.index_map_dvd hf
  have hcA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    decide
  have hproper : R ≠ ⊤ := by
    intro he
    have hd := L.card_map_dvd f
    rw [show L.map f = ⊤ from he, Nat.card_congr (Subgroup.topEquiv).toEquiv, hcA, hL] at hd
    norm_num at hd
  have hfive : R.index = 5 := by
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hRidx with h | h
    · exact (hproper (Subgroup.index_eq_one.mp h)).elim
    · exact h
  let : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hd := R.card_dvd_factorial_index_of_simple hproper
  rw [hcA, hfive] at hd
  norm_num [Nat.factorial] at hd

private theorem pair_stabilizer_card {S : Finset (Fin 22)} (hS : S.card = 2) :
    Nat.card (stabilizer M22 S) = 1920 := by
  rcases Finset.card_eq_two.mp hS with ⟨x, y, hxy, rfl⟩
  obtain ⟨g, hg1, hg2⟩ := (MulAction.is_two_pretransitive_iff.mp m22_isTwoPretransitive)
    (by decide : (1 : Fin 22) ≠ 2) hxy
  have hg : g • m22Pair12 = ({x, y} : Finset (Fin 22)) := by
    rw [m22Pair12, Finset.smul_finset_insert, Finset.smul_finset_singleton, ← hg1, ← hg2]
  exact (Nat.card_congr (stabilizerEquivStabilizer hg.symm).toEquiv).symm.trans
    m22PairStabilizer_card

/-- An involution in the restriction kernel supplies the preserved hexad. -/
private theorem invariant_small_set_in_hexad
    (H : Subgroup M22) (hH : Nat.card H = 1152)
    (S : Finset (Fin 22)) (hS : S.card = 4 ∨ S.card = 6)
    (hstab : H ≤ stabilizer M22 S) :
    ∃ B ∈ m22Blocks, H ≤ stabilizer M22 B := by
  classical
  let f : H →* Equiv.Perm S := (m22SetAction S).comp (inclusion hstab)
  have hmul : Nat.card f.ker * Nat.card f.range = 1152 := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index, hH]
  have hdiv : Nat.card f.range ∣ 720 := by
    have hd := card_subgroup_dvd_card f.range
    have hp : Nat.card (Equiv.Perm S) ∣ 720 := by
      rw [Nat.card_perm]
      have hs : Nat.card S = S.card := by simp
      rw [hs]
      rcases hS with h | h <;> rw [h] <;> norm_num [Nat.factorial]
    exact hd.trans hp
  have heven : 2 ∣ Nat.card f.ker := by
    have hd := Nat.mul_dvd_mul_left (Nat.card f.ker) hdiv
    rw [hmul] at hd
    omega
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := f.ker) 2 heven
  have htM : orderOf (t.val.val : M22) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact ht
  obtain ⟨B, hB, hfix⟩ := m22_exists_fixed_hexad t.val.val htM
  have hSB : S ⊆ B := by
    intro x hx
    apply (hfix x).mp
    have he := congrArg (fun p : Equiv.Perm S => (p ⟨x, hx⟩).val)
      (MonoidHom.mem_ker.mp t.property)
    exact he
  refine ⟨B, hB, ?_⟩
  intro g hg
  apply MulAction.mem_stabilizer_iff.mpr
  obtain ⟨T, hTS, hT⟩ := Finset.exists_subset_card_eq (s := S) (n := 3) (by omega)
  have hgS : g • S = S := hstab hg
  have hSB' : S ⊆ g • B := by
    rw [← hgS]
    exact Finset.smul_finset_subset_smul_finset hSB
  exact m22Blocks_eq_of_common_triple T (g • B) B hT (m22_smul_block_mem g B hB)
    hB (hTS.trans hSB') (hTS.trans hSB)



/-- All possible orbit lengths, using the odd subgroup index and Lagrange. -/
private theorem orbit_card_options (H : Subgroup M22) (hH : Nat.card H = 1152)
    (x : Fin 22) :
    (orbit H x).ncard = 2 ∨ (orbit H x).ncard = 4 ∨ (orbit H x).ncard = 6 ∨
    (orbit H x).ncard = 8 ∨ (orbit H x).ncard = 12 ∨ (orbit H x).ncard = 16 ∨
    (orbit H x).ncard = 18 := by
  let : IsPretransitive M22 (Fin 22) := m22_isPretransitive
  have hiH : H.index = 385 := by
    have hc := H.card_mul_index
    rw [hH, m22_order] at hc
    omega
  let L := stabilizer M22 x
  have hiL : L.index = 22 := by
    rw [index_stabilizer_of_transitive]
    simp
  have hdvd : 22 ∣ (H ⊓ L).index :=
    by simpa only [hiL] using
      (Subgroup.index_dvd_of_le (show H ⊓ L ≤ L from inf_le_right))
  rw [← Subgroup.relIndex_mul_index (show H ⊓ L ≤ H from inf_le_left),
    Subgroup.inf_relIndex_left, hiH] at hdvd
  change 22 ∣ (stabilizer H x).index * 385 at hdvd
  rw [index_stabilizer] at hdvd
  have heven : 2 ∣ (orbit H x).ncard := by omega
  have hd : (orbit H x).ncard ∣ 1152 := by
    rw [← index_stabilizer, ← hH]
    exact (stabilizer H x).index_dvd_card
  have hpos : 0 < (orbit H x).ncard := (Set.ncard_pos).mpr ⟨x, mem_orbit_self x⟩
  have hle : (orbit H x).ncard ≤ 22 := by simpa using Set.ncard_le_card (orbit H x)
  interval_cases hn : (orbit H x).ncard <;> omega

/-- Larger orbits cannot partition the 22 points. -/
private theorem exists_small_orbit (H : Subgroup M22) (hH : Nat.card H = 1152) :
    ∃ x : Fin 22, (orbit H x).ncard = 2 ∨ (orbit H x).ncard = 4 ∨
      (orbit H x).ncard = 6 := by
  classical
  by_contra hn
  push Not at hn
  have hlarge (x : Fin 22) : 8 ≤ (orbit H x).ncard := by
    have ho := orbit_card_options H hH x
    have hx := hn x
    omega
  have hnot18 (x : Fin 22) : (orbit H x).ncard ≠ 18 := by
    intro hx
    have hc : (orbit H x)ᶜ.ncard = 4 := by
      rw [Set.ncard_compl, hx]
      simp
    obtain ⟨y, hy⟩ := (Set.ncard_pos).mp (show 0 < (orbit H x)ᶜ.ncard by omega)
    have hsub : orbit H y ⊆ (orbit H x)ᶜ := by
      intro z hz hzx
      exact hy (orbit_eq_iff.mp ((orbit_eq_iff.mpr hz).symm.trans (orbit_eq_iff.mpr hzx)))
    have hb := Set.ncard_mono hsub
    have hl := hlarge y
    omega
  have hfour (x : Fin 22) : 4 ∣ (orbit H x).ncard := by
    have ho := orbit_card_options H hH x
    have hl := hlarge x
    have hn18 := hnot18 x
    rcases ho with h | h | h | h | h | h | h <;> omega
  let : Fintype (orbitRel.Quotient H (Fin 22)) := Fintype.ofFinite _
  have hsum := Nat.card_congr (selfEquivSigmaOrbits H (Fin 22))
  rw [Nat.card_sigma] at hsum
  have hd : 4 ∣ Nat.card (Fin 22) := by
    rw [hsum]
    exact Finset.dvd_sum fun q _ => hfour q.out
  norm_num at hd



/-- The Steiner-design Mathieu group M₂₂ has no subgroup of order 1152. -/
public theorem m22_subgroup_card_ne_1152 (H : Subgroup M22) : Nat.card H ≠ 1152 := by
  classical
  intro hH
  obtain ⟨x, hx⟩ := exists_small_orbit H hH
  let S := (orbit H x).toFinset
  have hScard : S.card = (orbit H x).ncard := (Set.ncard_eq_toFinset_card' _).symm
  have hstab : H ≤ stabilizer M22 S := by
    intro g hg
    apply MulAction.mem_stabilizer_finset'.mpr
    intro y hy
    apply Set.mem_toFinset.mpr
    exact mem_orbit_of_mem_orbit (⟨g, hg⟩ : H) (Set.mem_toFinset.mp hy)
  rcases hx with htwo | hfour | hsix
  · have hd := card_dvd_of_le hstab
    rw [hH, pair_stabilizer_card (hScard.trans htwo)] at hd
    norm_num at hd
  · obtain ⟨B, hB, hle⟩ := invariant_small_set_in_hexad H hH S
      (Or.inl (hScard.trans hfour)) hstab
    exact hexad_exclusion hB H hH hle
  · obtain ⟨B, hB, hle⟩ := invariant_small_set_in_hexad H hH S
      (Or.inr (hScard.trans hsix)) hstab
    exact hexad_exclusion hB H hH hle

end Sporadic.Mathieu
