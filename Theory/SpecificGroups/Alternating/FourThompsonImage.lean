module

public import Theory.SpecificGroups.Alternating.FourPairOuter
public import Stellmacher.SectionsOneToFourDefs

/-!
# A moved normal A₄ has the full symmetric automorphism image

A faithful action on a normal A₄ embeds the group in S₄. Its order is
therefore 12 or 24. In the first case the group is A₄, whose derived group
has order four, contradicting X=[X,J(R)] for the original A₄ subgroup X.
Thus the faithful action is the full symmetric group.

Source: Aschbacher--Smith 14.1.10, printed p.978, the one-block case.
-/

public section
open Subgroup Stellmacher
namespace AlternatingFourPair
variable {G : Type*} [Group G] [Finite G]

/-- The original movement, without a full-image assumption, identifies the faithful one-block group. -/
theorem symmetric_four_of_moved_normal
    (N X R : Subgroup G) [N.Normal]
    (eN : N ≃* A) (eX : X ≃* A)
    (hc : centralizer (N : Set G) = ⊥)
    (hm : X = ⁅X,elementaryAbelianMaxJ R⁆) : Nonempty (G ≃* Equiv.Perm (Fin 4)) := by
  let f : G →* Equiv.Perm (Fin 4) :=
    eA.symm.toMonoidHom.comp ((MulAut.congr eN).toMonoidHom.comp MulAut.conjNormal)
  have hf : Function.Injective f := eA.symm.injective.comp
    ((MulAut.congr eN).injective.comp (MulAut.conjNormal_injective_of_centralizer_eq_bot N hc))
  have hNcard : Nat.card N = 12 := (Nat.card_congr eN.toEquiv).trans
    (alternatingGroup.card_of_card_eq_four (by norm_num))
  have hXcard : Nat.card X = 12 := (Nat.card_congr eX.toEquiv).trans
    (alternatingGroup.card_of_card_eq_four (by norm_num))
  have hle : Nat.card G ≤ 24 := by
    simpa only [Nat.card_perm,Nat.card_fin,show Nat.factorial 4 = 24 by decide] using
      Nat.card_le_card_of_injective f hf
  have hd : 12 ∣ Nat.card G := hNcard ▸ N.card_subgroup_dvd_card
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hcases : Nat.card G = 12 ∨ Nat.card G = 24 := by
    obtain ⟨k,hk⟩ := hd
    omega
  have hGcard : Nat.card G = 24 := by
    rcases hcases with h | h
    · exfalso
      have hXt : X = ⊤ := eq_of_le_of_card_ge le_top (by rw [card_top,h,hXcard])
      have hderived : commutator G = ⊤ := by
        apply top_unique
        rw [←hXt,hm]
        exact (commutator_mono le_top le_top).trans_eq (_root_.commutator_def G).symm
      let e : G ≃* A := topEquiv.symm.trans ((MulEquiv.subgroupCongr hXt.symm).trans eX)
      have hcA : commutator A = ⊤ := by
        have hh := map_commutator_eq G e.toMonoidHom
        rw [hderived,map_top_of_surjective _ e.surjective,
          MonoidHom.range_eq_top.mpr e.surjective,←_root_.commutator_def A] at hh
        exact hh.symm
      have he := congrArg (fun H : Subgroup A => Nat.card H)
        ((alternatingGroup.kleinFour_eq_commutator (by norm_num : Nat.card (Fin 4) = 4)).trans hcA)
      rw [alternatingGroup.kleinFour_card_of_card_eq_four (by norm_num),card_top,
        alternatingGroup.card_of_card_eq_four (by norm_num)] at he
      norm_num at he
    · exact h
  exact ⟨MulEquiv.ofBijective f (hf.bijective_of_nat_card_le (by
    rw [hGcard,Nat.card_perm,Nat.card_fin]
    decide))⟩

end AlternatingFourPair
