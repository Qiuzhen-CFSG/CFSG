module

public import Theory.GroupTheory.SylowThreeCubic
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Theory.GroupTheory.Amalgam.ThreeClosed
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.LocalNormalizer

/-!
# The three-closed local bound and its singularity application

For the actual faithful cubic inclusion amalgam, suppose that each local group
has a normal subgroup of order three. Conjugation maps the common overlap into
the product of their automorphism groups. The common kernel centralizes both
order-three subgroups, so the previously proved local normalizer argument kills
it. The overlap therefore has order at most four and each local group has order
at most twelve.

The order formula of a regular arc action then gives regularity at most three.
The final theorem applies this to isomorphic endpoint groups and the inequality
between singularity and regularity used by the normalizer quotient in Section 5.
It takes precisely those earlier conclusions and requires no general upper
bound on regularity.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (2.16)(b),
printed p.386, and its application in (5.3), printed p.395.
-/

@[expose] public section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

/-- Normal order-three subgroups at both endpoints give a faithful conjugation
action of the overlap on their product, whose automorphism group has order four. -/
theorem CubicTreeAction.overlap_card_le_four_of_normal_three
    (h : CubicTreeAction F)
    (X : Subgroup (F false)) (Y : Subgroup (F true)) [X.Normal] [Y.Normal]
    (hX : Nat.card X = 3) (hY : Nat.card Y = 3) :
    Nat.card (F false ⊓ F true : Subgroup G) ≤ 4 := by
  let : Finite (F false) := h.finite false
  let : Finite (F true) := h.finite true
  exact Subgroup.overlap_card_le_four_of_normal_three (F false) (F true) X Y hX hY
    (fun K hK hXK hYK => h.normalized_overlap_eq_bot_of_three_subgroups K hK X Y hX hY hXK hYK)

/-- The overlap has order at most four when both local groups are three-closed. -/
theorem CubicTreeAction.overlap_card_le_four_of_normal_sylow_three
    (h : CubicTreeAction F) (P : Sylow 3 (F false)) (Q : Sylow 3 (F true))
    [(P : Subgroup (F false)).Normal] [(Q : Subgroup (F true)).Normal] :
    Nat.card (F false ⊓ F true : Subgroup G) ≤ 4 := by
  let : Finite (F false) := h.finite false
  let : Finite (F true) := h.finite true
  obtain ⟨S, hS⟩ := h.primitive.sylow.left_sylow
  obtain ⟨T, hT⟩ := h.primitive.sylow.right_sylow
  apply h.overlap_card_le_four_of_normal_three (P : Subgroup (F false))
    (Q : Subgroup (F true))
  · exact card_sylow_three_of_two_group_index_three _ (hS ▸ S.isPGroup')
      h.primitive.left_index P
  · exact card_sylow_three_of_two_group_index_three _ (hT ▸ T.isPGroup')
      h.primitive.right_index Q

/-- The cubic local index converts the overlap bound into a local order bound. -/
theorem CubicTreeAction.local_card_le_twelve_of_normal_sylow_three
    (h : CubicTreeAction F) (P : Sylow 3 (F false)) (Q : Sylow 3 (F true))
    [(P : Subgroup (F false)).Normal] [(Q : Subgroup (F true)).Normal] (i : Bool) :
    Nat.card (F i) ≤ 12 := by
  let : Finite (F false) := h.finite false
  let : Finite (F true) := h.finite true
  have hb := h.overlap_card_le_four_of_normal_sylow_three P Q
  let α := inclusionAmalgam (F false) (F true)
  have hc (i : Bool) : Nat.card (F i) = 3 * Nat.card (F false ⊓ F true : Subgroup G) := by
    cases i
    · rw [← α.left.range.index_mul_card, h.primitive.left_index,
        Nat.card_congr (MonoidHom.ofInjective h.primitive.sylow.left_injective).toEquiv]
    · rw [← α.right.range.index_mul_card, h.primitive.right_index,
        Nat.card_congr (MonoidHom.ofInjective h.primitive.sylow.right_injective).toEquiv]
  rw [hc]
  omega

/-- The local order formula for a regular arc action forces regularity at most
three when the local Sylow three-subgroups are normal. -/
theorem CubicTreeAction.regularity_le_three_of_normal_sylow_three
    (h : CubicTreeAction F) (P : Sylow 3 (F false)) (Q : Sylow 3 (F true))
    [(P : Subgroup (F false)).Normal] [(Q : Subgroup (F true)).Normal]
    (t : ℕ) (hcard : Nat.card (F false) = 3 * 2 ^ (t - 1)) : t ≤ 3 := by
  have hbound := h.local_card_le_twelve_of_normal_sylow_three P Q false
  rw [hcard] at hbound
  by_contra! hlarge
  have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 3 ≤ t - 1 by omega)
  norm_num at hp
  omega

/-- The three-closed exclusion used in Goldschmidt (5.3). The endpoint
isomorphism transports normality of the Sylow three-subgroup; the local order
formula and the singularity inequality are the conclusions used from (5.2). -/
theorem CubicTreeAction.not_normal_sylow_three_of_singularity_at_least_five
    (h : CubicTreeAction F) (e : F false ≃* F true) (P : Sylow 3 (F false))
    (s t : ℕ) (hcard : Nat.card (F false) = 3 * 2 ^ (t - 1))
    (hs : 5 ≤ s) (hst : s ≤ 2 * t - 3) : ¬ (P : Subgroup (F false)).Normal := by
  intro hP
  let : Finite (F false) := h.finite false
  let : Finite (F true) := h.finite true
  let := hP
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have : (Q : Subgroup (F true)).Normal :=
    hP.map e.toMonoidHom e.surjective
  have ht := h.regularity_le_three_of_normal_sylow_three P Q t hcard
  omega

/-- The strict singularity bound is a special case of the source conclusion. -/
theorem CubicTreeAction.not_normal_sylow_three_of_large_singularity
    (h : CubicTreeAction F) (e : F false ≃* F true) (P : Sylow 3 (F false))
    (s t : ℕ) (hcard : Nat.card (F false) = 3 * 2 ^ (t - 1))
    (hs : 5 < s) (hst : s ≤ 2 * t - 3) : ¬ (P : Subgroup (F false)).Normal :=
  h.not_normal_sylow_three_of_singularity_at_least_five e P s t hcard hs.le hst

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
