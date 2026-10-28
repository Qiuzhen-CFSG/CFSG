module

public import Mathlib.GroupTheory.Nilpotent

/-!
# A self-centralizing subgroup modulo the center

The quotient centralizer condition lifts to the original group when the
subgroup contains the quotient kernel. In particular, a subgroup that is
self-centralizing modulo the center contains the second center. This is the
precise inference from (*) in Aschbacher--Smith, Lemma 14.2.21, printed p.988.
It does not identify the second center with a derived-subgroup centralizer.
-/

namespace Subgroup

/-- Self-centralization after a central quotient implies self-centralization
before quotienting; the statement also allows a smaller centralizing subgroup. -/
public theorem le_of_centralizer_quotient_le {P : Type*} [Group P] (Z Q F : Subgroup P) [Z.Normal]
    (hZQ : Z ≤ Q) (hFC : F ≤ centralizer (Q : Set P))
    (hself : centralizer (Q.map (QuotientGroup.mk' Z) : Set (P ⧸ Z)) ≤
      Q.map (QuotientGroup.mk' Z)) : F ≤ Q := by
  intro f hf
  have hm : QuotientGroup.mk' Z f ∈ Q.map (QuotientGroup.mk' Z) := by
    apply hself
    rw [mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    simpa only [map_mul] using congrArg (QuotientGroup.mk' Z)
      (mem_centralizer_iff.mp (hFC hf) q hq)
  have he := Subgroup.comap_map_eq_self (f := QuotientGroup.mk' Z)
    (H := Q) (by simpa using hZQ)
  exact he ▸ hm

/-- The valid conclusion from the quotient centralizer chain is containment
of the second center, without any larger centralizer identification. -/
public theorem second_center_le_of_quotient_centralizer_le {P : Type*} [Group P] (Q : Subgroup P)
    (hZQ : center P ≤ Q)
    (hself : centralizer (Q.map (QuotientGroup.mk' (center P)) : Set (P ⧸ center P)) ≤
      Q.map (QuotientGroup.mk' (center P))) : upperCentralSeries P 2 ≤ Q := by
  have hc := comap_upperCentralSeries_quotient_center (G := P) 1
  rw [upperCentralSeries_one] at hc
  rw [← hc]
  have hle := (center_le_centralizer
    (Q.map (QuotientGroup.mk' (center P)) : Set (P ⧸ center P))).trans hself
  have hm := Subgroup.comap_mono (f := QuotientGroup.mk' (center P)) hle
  rwa [comap_map_eq_self (by simpa using hZQ)] at hm

end Subgroup
