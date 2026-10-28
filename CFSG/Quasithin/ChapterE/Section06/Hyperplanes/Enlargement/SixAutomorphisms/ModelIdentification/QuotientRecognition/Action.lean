module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.Inputs
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# The faithful quotient action in the six-component enlargement

The embedded A₆ injects into Y/Z(Y). It cannot surject: perfectness would
then force X = Y, contradicting strict enlargement. In particular the
central quotient has order greater than 360. The order-two A-action
also descends faithfully and fixes this actual embedded A₆ pointwise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the
further-enlargement paragraph of E.6.23, printed p.254 (PDF p.265).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
variable {G : Type*} [Group G] [Finite G] {M V U A L X Y : Subgroup G} {g : G}

/-- A proper component enlargement strictly increases the central quotient order. -/
theorem quotient_card_gt_six
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    360 < Nat.card (Y ⧸ center Y) := by
  let _ := extension_quasisimple hY
  obtain ⟨e⟩ := d.six.model
  have hx : Nat.card X = 360 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num
  by_contra hsmall
  have hs := (six_quotient_embedding_injective d hY).bijective_of_nat_card_le
    (show Nat.card (Y ⧸ center Y) ≤ Nat.card X by omega)
  have hi := PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
    (QuotientGroup.mk' (center Y)) (inclusion hY.proper.le) hs.surjective
    (by rw [QuotientGroup.ker_mk'])
  apply hY.proper.ne
  apply le_antisymm hY.proper.le
  intro y hy
  obtain ⟨x, hx⟩ := hi ⟨y, hy⟩
  have hxy : (x : G) = y := congrArg Subtype.val hx
  exact hxy ▸ x.property

/-- A genuine involution on the central quotient fixes the actual embedded A₆. -/
theorem quotient_involution [IsElementaryAbelian 2 V]
    (d : EscapeConfiguration M V U A L X g)
    (hY : NormalComponentExtension U A X g Y) :
    ∃ a : MulAut (Y ⧸ center Y), orderOf a = 2 ∧
      ∀ x : X, a (QuotientGroup.mk' (center Y) (inclusion hY.proper.le x)) =
        QuotientGroup.mk' (center Y) (inclusion hY.proper.le x) := by
  let _ := extension_quasisimple hY
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := actionImage A Y) 2
    (by rw [action_order_two d hY])
  refine ⟨quotientAut (center Y) b.val, ?_, ?_⟩
  · rw [orderOf_injective _ MulAut.quotient_center_injective,
      Subgroup.orderOf_coe, hb]
  · intro x
    rw [quotientAut_apply_mk]
    have hx := (six_fixed_component d hY).1
      (show inclusion hY.proper.le x ∈ X.subgroupOf Y from x.property)
    have he := hx b
    exact congrArg (QuotientGroup.mk' (center Y)) he

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.SixAutomorphisms.ModelIdentification.QuotientScreen
