module
public import ABG.ChapterII.Section3.QSimpleSectionReduction
public import GorensteinWalter.PSL2SectionOrderBound
public import GorensteinWalter.PSL2NoASevenSection
public import GorensteinWalter.SL2ProjectiveCover
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Simple sections of full-shape Q-groups

A finite Q-group with semidihedral or wreathed Sylow two-subgroups and
source characteristic power q has no A7 section. Every section isomorphic
to PSL2(E), for an odd finite field E with more than three elements, has
field order at most q. Sections are expressed by actual surjections from
arbitrary subgroups, so quotient kernels need not be central.

The structural reduction puts each even nonsolvable simple section into
PSL2 over the prescribed field of order q. The actual Dickson theorem
excludes A7 sections there, and the PSL2 order formula bounds field orders.
A7 perfection and PSL2 perfection above field order three provide
nonsolvability; the canonical dihedral Sylow model supplies even order.
The ambient source parameter q may itself equal three.

This is the section-exclusion step of ABG II.3 Lemma2, article p24. Its
structural input uses odd-index and abelian layers from Gorenstein--Walter,
without invoking the subsequent ABG Proposition3.
-/

namespace ABG
open GorensteinWalter
universe u v

public theorem qGroup_simple_section_exclusions
    {G : Type u} [Group G] [Finite G] (hQ : IsQGroup G)
    (S : Sylow 2 G) (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S)
    (q : ℕ) (hq : HasSourceQCharacteristicPower G q) :
    (∀ (U : Subgroup G) (f : U →* alternatingGroup (Fin 7)),
      Function.Surjective f → False) ∧
    (∀ (E : Type v) [Field E] [Finite E], IsOddPrimePower (Nat.card E) →
      3 < Nat.card E → ∀ (U : Subgroup G) (f : U →* PSL2 E),
      Function.Surjective f → Nat.card E ≤ q) := by
  constructor
  · intro U f hf
    let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    let : Group.IsPerfect (alternatingGroup (Fin 7)) :=
      ⟨commutator_alternatingGroup_eq_top (by norm_num)⟩
    have htwo : 2 ∣ Nat.card (alternatingGroup (Fin 7)) := by
      rw [nat_card_alternatingGroup]
      norm_num
    obtain ⟨F, iF, fF, hF, _, W, g, hg⟩ := qGroup_simple_section_in_psl2 hQ S hS q hq
      htwo (Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 7))) U f hf
    let : Field F := iF
    let : Finite F := fF
    exact no_surjective_subgroup_a7_of_psl2_odd F hF W g hg
  · intro E iE fE hE hE3 U f hf
    let : IsSimpleGroup (PSL2 E) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) E) :=
      sl2_isPerfect_of_card_gt_three E hE3
    let : Group.IsPerfect (PSL2 E) := inferInstance
    let T : Sylow 2 (PSL2 E) := Classical.choice inferInstance
    obtain ⟨n, _hn, ⟨e⟩⟩ := psl2_odd_hasDihedralSylowTwo_model E hE T
    have htwoT : 2 ∣ Nat.card T := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
      exact dvd_mul_right _ _
    have htwo : 2 ∣ Nat.card (PSL2 E) := htwoT.trans T.card_subgroup_dvd_card
    obtain ⟨F, iF, fF, hF, hFq, W, g, hg⟩ := qGroup_simple_section_in_psl2 hQ S hS q hq
      htwo (Group.IsPerfect.not_isSolvable (PSL2 E)) U f hf
    let : Field F := iF
    let : Finite F := fF
    rw [← hFq]
    exact psl2_section_field_card_le F E hF hE W g hg

end ABG

