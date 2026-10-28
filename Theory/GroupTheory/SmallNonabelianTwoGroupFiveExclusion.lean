module

public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderFive
public import Theory.ElementaryAbelian.Extraspecial

/-!
# Excluding five from a small self-centralizing two-group

A nonabelian two-group of order 32 containing an elementary eight has no
automorphism of order five. Apply the existing quadratic-form obstruction
to a cyclic subgroup of order five in its automorphism group. For a normal
self-centralizing such subgroup, the conjugation kernel is contained in the
two-group, so five also cannot divide the order of the ambient finite group.

This is the automorphism obstruction used to eliminate the dihedral-ten row
in Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985), (11.7),
printed p.174. The extraspecial variant retains the elementary-eight premise;
the other extraspecial group of order 32 has automorphisms of order five.
-/

open Subgroup

namespace SmallNonabelianTwoGroup

/-- An elementary eight excludes five from the full automorphism group of a
nonabelian two-group of order 32. -/
public theorem not_five_dvd_mulAut_card
    {Q : Type*} [Group Q] [Finite Q]
    (htwo : IsPGroup 2 Q) (hnoncomm : ¬ IsMulCommutative Q)
    (hQ : Nat.card Q = 32) (E : Subgroup Q)
    (hE : IsElementaryAbelian 2 E) (hEc : Nat.card E = 8) :
    ¬ 5 ∣ Nat.card (MulAut Q) := by
  intro hfive
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 5 hfive
  let A := zpowers a
  have hA : Nat.card A = 5 := (Nat.card_zpowers a).trans ha
  have hodd : Odd (Nat.card A) := by rw [hA]; decide
  have hdiv : 5 ∣ Nat.card A := by rw [hA]
  have hquot := frattini_quotient_card_eq_sixteen_of_five_dvd
    htwo hnoncomm (by omega) A hodd hdiv
  obtain ⟨_, hphi, _⟩ := frattini_structure_of_quotient_sixteen
    htwo hnoncomm (by omega) hquot
  exact not_five_dvd_odd_actor_card_of_frattini_two
    htwo hnoncomm hQ hphi E hE hEc A hodd hdiv

/-- The literal conjugation kernel, which lies in the self-centralizing
normal two-group, contributes no factor five. -/
public theorem not_five_dvd_card_of_selfCentralizing
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] (htwo : IsPGroup 2 Q)
    (hnoncomm : ¬ IsMulCommutative Q) (hQ : Nat.card Q = 32)
    (E : Subgroup Q) (hE : IsElementaryAbelian 2 E) (hEc : Nat.card E = 8)
    (hself : centralizer (Q : Set G) ≤ Q) : ¬ 5 ∣ Nat.card G := by
  let f : G →* MulAut Q := MulAut.conjNormal
  have hk : f.ker ≤ Q := by
    intro x hx
    apply hself
    rw [mem_centralizer_iff]
    intro y hy
    have hh := congrArg (fun a : MulAut Q => (a ⟨y, hy⟩ : G)) hx
    change x * y * x⁻¹ = y at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hkcard : Nat.card f.ker ∣ 32 := hQ ▸ card_dvd_of_le hk
  have hrcard : Nat.card f.range ∣ Nat.card (MulAut Q) :=
    f.range.card_subgroup_dvd_card
  have hcount := f.ker.card_mul_index
  rw [index_ker] at hcount
  intro h5
  rw [← hcount] at h5
  rcases (by decide : Nat.Prime 5).dvd_mul.mp h5 with h5 | h5
  · exact (by decide : ¬ 5 ∣ 32) (h5.trans hkcard)
  · exact not_five_dvd_mulAut_card htwo hnoncomm hQ E hE hEc (h5.trans hrcard)

/-- The extraspecial form of the same obstruction, with its elementary
subgroup specified inside the actual normal subgroup. -/
public theorem not_five_dvd_card_of_selfCentralizing_extraspecial
    {G : Type*} [Group G] [Finite G]
    (Q : Subgroup G) [Q.Normal] [IsExtraspecial 2 Q]
    (hQ : Nat.card Q = 32) (E : Subgroup Q)
    (hE : IsElementaryAbelian 2 E) (hEc : Nat.card E = 8)
    (hself : centralizer (Q : Set G) ≤ Q) : ¬ 5 ∣ Nat.card G := by
  have hn : ¬ IsMulCommutative Q := by
    intro hcomm
    let : IsMulCommutative Q := hcomm
    have hc := IsExtraspecial.center_order_p 2 Q
    rw [center_eq_top, Nat.card_congr (topEquiv : (⊤ : Subgroup Q) ≃* Q).toEquiv,
      hQ] at hc
    norm_num at hc
  exact not_five_dvd_card_of_selfCentralizing Q (IsExtraspecial.isPGroup 2 Q)
    hn hQ E hE hEc hself

end SmallNonabelianTwoGroup
