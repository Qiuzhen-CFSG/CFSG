module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.FiveOvergroups.Normalizer

/-!
# Maximality of the large full-Ree five-overgroup

The native Sylow-five coverage bounds every subgroup avoiding the derived Tits
group by 15600. An order-15600 subgroup meets that derived group in order7800
and projects onto the quotient of order2. Every proper overgroup must still
avoid the derived group, so the same bound forces equality. The earlier
normalizer theorem also identifies its derived intersection's full normalizer.

Source: the primitive second-suborbit step in Aschbacher--Smith J.5.6, p.447.
-/

public section
open Subgroup
namespace Tits.ExceptionalParabolics.FullRee.FiveOvergroups

private theorem derived_card : Nat.card D=17971200 :=
  (Nat.card_congr atlasDerivedEquiv.toEquiv).symm.trans atlas1600Group_card

private theorem avoids_derived_of_card (J : Subgroup R) (hc : Nat.card J=15600) :
    ¬D≤J := by
  intro hd
  have hle:=card_le_of_le hd
  rw [derived_card,hc] at hle
  omega

theorem isCoatom_of_card (J : Subgroup R) (hc : Nat.card J=15600) : IsCoatom J := by
  have hD := avoids_derived_of_card J hc
  obtain ⟨_,_,hindex,_⟩ := large_derivedPart_conjugate J hD (by rw [hc]; decide) hc.ge
  apply isCoatom_iff_ge_of_le.mpr
  refine ⟨?_,fun K hK hJK=>?_⟩
  · intro he
    have hh:=hc
    rw [he,Nat.card_congr (Subgroup.topEquiv).toEquiv,group_card] at hh
    contradiction
  · have hDK : ¬D≤K := by
      intro hd
      have he := relIndex_mul_index hd
      rw [derived_index] at he
      have hk : K.index≠1 := fun h=>hK (index_eq_one.mp h)
      have hk0 : K.index≠0 := Subgroup.FiniteIndex.index_ne_zero
      have hk2 : K.index=2 :=
        ((Nat.dvd_prime Nat.prime_two).mp (derived_index ▸ index_dvd_of_le hd)).resolve_left hk
      rw [hk2] at he
      have hi : D.relIndex K=1 := by omega
      have hJD : J≤D := hJK.trans (relIndex_eq_one.mp hi)
      have hj : D.relIndex J=1 := relIndex_eq_one.mpr hJD
      omega
    have hb := card_le K hDK ((show 25∣Nat.card J by rw [hc]; decide).trans (card_dvd_of_le hJK))
    exact (eq_of_le_of_card_ge hJK (by simpa only [hc] using hb)).ge

theorem normalizer_intersection_of_card (J : Subgroup R) (hc : Nat.card J=15600) :
    normalizer ((J⊓D : Subgroup R) : Set R)=J :=
  normalizer_intersection J (avoids_derived_of_card J hc) (by rw [hc]; decide) hc.ge

theorem intersection_card_of_card (J : Subgroup R) (hc : Nat.card J=15600) :
    Nat.card (J⊓D : Subgroup R)=7800 := by
  rw [←derivedPart_card]
  exact (large_derivedPart_conjugate J (avoids_derived_of_card J hc)
    (by rw [hc]; decide) hc.ge).2.1
end Tits.ExceptionalParabolics.FullRee.FiveOvergroups
