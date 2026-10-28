module
public import Theory.GroupTheory.GeneralizedFitting.ElementaryEightAction
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Normal subgroups above an elementary-eight generalized Fitting subgroup

When F*(P) is an elementary eight with quotient of order 168, the full
conjugation action makes that eight a minimal normal subgroup. Every other
nontrivial normal subgroup contains it: a disjoint normal subgroup would
centralize the eight and hence lie in it. If the literal quotient is simple,
there are exactly three normal subgroups, and P is perfect and centerless.
Every proper normal subgroup has index divisible by seven, so a homomorphism
to a group of order prime to seven is trivial.

These are the normal-subgroup and small-action reductions for the M in
Aschbacher–Smith, §I.4(G2), printed p.417. The source configuration application
and the resulting obstruction to M normalizing H are in
`CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.NormalStructure`.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.GeneralizedFittingEight
variable {P : Type*} [Group P] [Finite P]
variable (V : Subgroup P) [V.Normal] [IsElementaryAbelian 2 V]
variable (hfit : V = generalizedFitting P) (hV : Nat.card V = 8)
variable (hquot : Nat.card (P ⧸ V) = 168)

include hfit hV hquot in
theorem normal_subgroup_in_seed (N : Subgroup P) [N.Normal] (hNV : N ≤ V) :
    N = ⊥ ∨ N = V := by
  by_cases hn : N = ⊥
  · exact Or.inl hn
  right
  apply le_antisymm hNV
  obtain ⟨x, hx, hx1⟩ := (bot_or_exists_ne_one N).resolve_left hn
  intro y hy
  by_cases hy1 : y = 1
  · simp [hy1]
  obtain ⟨g, hg⟩ := nonidentity_conjugate V hfit hV hquot
    ⟨x, hNV hx⟩ ⟨y, hy⟩
    (fun h => hx1 (congrArg Subtype.val h))
    (fun h => hy1 (congrArg Subtype.val h))
  change g * x * g⁻¹ = y at hg
  rw [← hg]
  exact Subgroup.Normal.conj_mem (inferInstance : N.Normal) x hx g

include hfit hV hquot in
theorem seed_le_nontrivial_normal (N : Subgroup P) [N.Normal] (hn : N ≠ ⊥) :
    V ≤ N := by
  rcases normal_subgroup_in_seed V hfit hV hquot (N ⊓ V) inf_le_right with h | h
  · have hc : ⁅N, V⁆ = ⊥ := bot_unique (h ▸ commutator_le_inf N V)
    have hNV : N ≤ V := by
      rw [← centralizer_eq V hfit]
      exact commutator_eq_bot_iff_le_centralizer.mp hc
    exact (hn ((inf_eq_left.mpr hNV).symm.trans h)).elim
  · exact h.symm.le.trans inf_le_left

include hfit hV hquot in
theorem normal_subgroup_trichotomy [IsSimpleGroup (P ⧸ V)]
    (N : Subgroup P) [N.Normal] : N = ⊥ ∨ N = V ∨ N = ⊤ := by
  by_cases hn : N = ⊥
  · exact Or.inl hn
  right
  have hVN := seed_le_nontrivial_normal V hfit hV hquot N hn
  let q := QuotientGroup.mk' V
  have hnormal : (N.map q).Normal := Subgroup.Normal.map inferInstance q
    (QuotientGroup.mk'_surjective V)
  have hk : q.ker = V := QuotientGroup.ker_mk' V
  rcases hnormal.eq_bot_or_eq_top with h | h
  · left
    have hh := congrArg (Subgroup.comap q) h
    simpa only [comap_map_eq, MonoidHom.comap_bot, hk,
      sup_of_le_left hVN] using hh
  · right
    have hh := congrArg (Subgroup.comap q) h
    simpa only [comap_map_eq, comap_top, hk,
      sup_of_le_left hVN] using hh

omit [Finite P] [IsElementaryAbelian 2 V] in
include hquot in
theorem quotient_not_commutative [IsSimpleGroup (P ⧸ V)] :
    ¬ IsMulCommutative (P ⧸ V) := by
  intro h
  let := h
  have hp := IsSimpleGroup.prime_card (α := P ⧸ V)
  rw [hquot] at hp
  norm_num at hp

include hfit hV hquot in
theorem perfect [IsSimpleGroup (P ⧸ V)] : Group.IsPerfect P := by
  refine ⟨?_⟩
  rcases normal_subgroup_trichotomy V hfit hV hquot (_root_.commutator P)
      with h | h | h
  · exact (quotient_not_commutative V hquot
      (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
        (h ▸ bot_le))).elim
  · exact (quotient_not_commutative V hquot
      (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr h.le)).elim
  · exact h

include hfit hV hquot in
theorem center_eq_bot : center P = ⊥ := by
  have hZV : center P ≤ V := by
    rw [← centralizer_eq V hfit]
    exact center_le_centralizer _
  rcases normal_subgroup_in_seed V hfit hV hquot (center P) hZV with h | h
  · exact h
  · have hcent : centralizer (V : Set P) = ⊤ := by
      rw [← h]
      exact centralizer_center
    have htop : V = ⊤ := (centralizer_eq V hfit).symm.trans hcent
    have hc := card_group V hV hquot
    have hv := hV
    rw [htop, Nat.card_congr (topEquiv : (⊤ : Subgroup P) ≃* P).toEquiv, hc] at hv
    norm_num at hv

include hfit hV hquot in
theorem seven_dvd_index_of_proper_normal [IsSimpleGroup (P ⧸ V)]
    (N : Subgroup P) [N.Normal] (hne : N ≠ ⊤) : 7 ∣ N.index := by
  rcases normal_subgroup_trichotomy V hfit hV hquot N with h | h | h
  · rw [h, index_bot, card_group V hV hquot]
    decide
  · rw [h, index_eq_card, hquot]
    decide
  · exact (hne h).elim

include hfit hV hquot in
theorem hom_eq_one_of_seven_not_dvd [IsSimpleGroup (P ⧸ V)]
    {K : Type*} [Group K] (f : P →* K) (hK : ¬ 7 ∣ Nat.card K) : f = 1 := by
  apply MonoidHom.ker_eq_top_iff.mp
  by_contra hn
  have hd := seven_dvd_index_of_proper_normal V hfit hV hquot f.ker hn
  rw [index_ker] at hd
  exact hK (hd.trans f.range.card_subgroup_dvd_card)

end Theory.GroupTheory.GeneralizedFittingEight
