module

public import Stellmacher.Recognition.LyonsU3Four.NormalizerAction
public import Theory.GroupTheory.NormalizerInnerAutomorphisms
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse

/-!
# The elementary automizer bound in Lyons's Sylow configuration

The automizer index is odd and divides the order of the full automorphism
group of the supplied Sylow subgroup. The Frattini quotient has order sixteen.
The kernel of the action on this quotient is a two-group, and its image has
order dividing |GL₄(2)| = 20160. Thus every odd divisor of the automorphism
group order, including the automizer index, divides 315.

Source: Lyons, *A Characterization of the Group U₃(4)* (1972), Lemma 1,
printed p. 372. The divisibility argument uses the full automorphism group
and does not require a choice of complement in the actual normalizer.
-/

namespace Stellmacher.Recognition.LyonsU3Four

public theorem automizerIndex_dvd_sylow_index {G : Type*} [Group G]
    (S : Sylow 2 G) : automizerIndex S ∣ (S : Subgroup G).index := by
  exact (Subgroup.relIndex_dvd_of_le_left _
    (show (S : Subgroup G) ≤ (S : Subgroup G) ⊔ Subgroup.centralizer (S : Set G)
      from le_sup_left)).trans
    (Subgroup.relIndex_dvd_index_of_le (S : Subgroup G).le_normalizer)

public theorem automizerIndex_odd {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) : Odd (automizerIndex S) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply Nat.not_even_iff_odd.mp
  intro he
  exact S.not_dvd_index (he.two_dvd.trans (automizerIndex_dvd_sylow_index S))

public theorem automizerIndex_pos {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) : 0 < automizerIndex S := by
  apply Nat.pos_of_ne_zero
  intro he
  have ho := automizerIndex_odd S
  simp [he] at ho

public theorem automizerIndex_dvd_card_mulAut {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) : automizerIndex S ∣ Nat.card (MulAut S) := by
  change (((S : Subgroup G) ⊔ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf
    (Subgroup.normalizer ((S : Subgroup G) : Set G))).index ∣ Nat.card (MulAut S)
  rw [← Subgroup.normalizerMonoidHom_comap_conj_range (S : Subgroup G),
    Subgroup.index_comap]
  exact (Subgroup.relIndex_dvd_card _ _).trans
    (Subgroup.card_subgroup_dvd_card _)

public theorem odd_dvd_mulAut_card_dvd_315
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) {m : ℕ}
    (hodd : Odd m) (hdiv : m ∣ Nat.card (MulAut S)) : m ∣ 315 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fact (IsPGroup 2 S) := ⟨S.isPGroup'⟩
  let : IsElementaryAbelian 2 (S ⧸ frattini S) :=
    isElementaryAbelian_quotient_frattini (p := 2)
  have hquot : Nat.card (S ⧸ frattini S) = 2 ^ 4 := by
    have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini S)
    have hphi : Nat.card (frattini S) = 4 := h.center_eq_frattini ▸ h.center_card
    rw [h.card, hphi] at hc
    omega
  have hlinear : Nat.card (MulAut (S ⧸ frattini S)) = 20160 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 4 hquot]
    norm_num [Fin.prod_univ_succ]
  let f := Subgroup.quotientAut (frattini S)
  obtain ⟨n, hn⟩ := (Subgroup.isPGroup_quotientAut_frattini_kernel S.isPGroup').exists_card_eq
  have hr : Nat.card f.range ∣ 20160 := hlinear ▸ f.range.card_subgroup_dvd_card
  have hc : Nat.card (MulAut S) = 2 ^ n * Nat.card f.range := by
    have he := f.ker.card_mul_index
    rw [Subgroup.index_ker] at he
    exact he.symm.trans (congrArg (· * Nat.card f.range) hn)
  have hd : m ∣ 2 ^ n * 20160 :=
    hdiv.trans (hc ▸ Nat.mul_dvd_mul_left _ hr)
  have hd' : m ∣ 20160 :=
    (hodd.coprime_two_right.pow_right n).dvd_of_dvd_mul_left hd
  exact (hodd.coprime_two_right.pow_right 6).dvd_of_dvd_mul_left hd'

/-- The numerical bound preceding the prime exclusions in Lyons's Lemma 1. -/
public theorem automizerIndex_dvd_315
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (h : SylowStructure S) : automizerIndex S ∣ 315 :=
  odd_dvd_mulAut_card_dvd_315 S h (automizerIndex_odd S)
    (automizerIndex_dvd_card_mulAut S)

end Stellmacher.Recognition.LyonsU3Four
