module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenGeometry.Actions
public import Theory.GroupTheory.PResidual.TwoThreeComparison

/-!
# The literal prime-complement residual in 15.2.12

The convention bridge is re-exported from `SourceChosenGeometry.Actions`.
Using that single declaration lets the residual and action consumers be
imported together. For finite groups, the prime-set definition with primes
other than three equals the coprime-index definition O^{3'}. The wreath quotient makes H
a {2,3}-group, so its O² is already O^{3'}. Normality of the latter in Mc
then contains the entire Mc-orbit span. Hence the reverse inclusion in
15.2.12(4) is exactly a coprime-index obligation on that actual span.

Source: Aschbacher--Smith, 15.2.12(4), printed p.1111; residual
conventions in A.1.26. No O₃ or O³ is substituted for O^{3'}.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
variable {G : Type*} [Group G] [Finite G]

/-- The original ambient embedding is unchanged by the convention bridge. -/
theorem threePrimeResidual_eq (H : Subgroup G) :
    threePrimeResidual H = (primeToResidual 3 H).map H.subtype := by
  rw [threePrimeResidual, piResidual_threeComplement_eq_primeToResidual]

/-- The source wreath quotient has only the primes two and three. -/
theorem twoThree_of_wreath (H : Subgroup G)
    (e : (H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) :
    IsPiGroup twoThreePrimes H := by
  have hQ : IsPiGroup twoThreePrimes (H ⧸ pCore 2 H) := by
    rw [IsPiGroup_iff]
    intro p hp
    have hc : Nat.card (H ⧸ pCore 2 H) = 72 := by
      rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card, Nat.card_perm]
      norm_num [Nat.card_eq_fintype_card]
    rw [hc,show 72 = 2 ^ 3 * 3 ^ 2 by decide] at hp
    rcases p.property.dvd_mul.mp hp with h2 | h3
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
        (p.property.dvd_of_dvd_pow h2) |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp
        (p.property.dvd_of_dvd_pow h3) |>.resolve_left p.property.ne_one)
  have hN : IsPiGroup twoThreePrimes (pCore 2 H) := by
    rw [IsPiGroup_iff]
    intro p hp
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (p.property.dvd_of_dvd_pow (hn ▸ hp)) |>.resolve_left p.property.ne_one)
  exact IsPiGroup.of_normal_subgroup_and_quotient (pCore 2 H) (hN.isPiSubgroup _) hQ

/-- The two residual conventions agree on the actual source H. -/
theorem residual_eq_threePrimeResidual_of_wreath (H : Subgroup G)
    (e : (H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) :
    residual H = threePrimeResidual H := by
  rw [threePrimeResidual_eq, residual, twoResidual_eq_primeToResidual_three
    (twoThree_of_wreath H e)]

/-- Every conjugate in the actual partner span belongs to O^{3'}(Mc). -/
theorem partnerSpan_le_threePrimeResidual {H Mc : Subgroup G} (hHM : H ≤ Mc)
    (e : (H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))) :
    partnerSpan H Mc ≤ threePrimeResidual Mc := by
  apply conjugateSpanBy_le
  · rw [residual_eq_threePrimeResidual_of_wreath H e]
    exact threePrimeResidual_mono hHM
  · rw [threePrimeResidual_eq]
    have hn := (primeToResidual 3 Mc).le_normalizer_map Mc.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn

/-- A three-free quotient by Kc supplies the remaining direction in the
source equality; relative normality is constructed from the orbit span. -/
theorem partnerSpan_eq_threePrimeResidual_of_index {H Mc : Subgroup G}
    (hHM : H ≤ Mc)
    (e : (H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2)))
    (hi : Nat.Coprime 3 ((partnerSpan H Mc).subgroupOf Mc).index) :
    partnerSpan H Mc = threePrimeResidual Mc := by
  apply le_antisymm (partnerSpan_le_threePrimeResidual hHM e)
  have hKM : partnerSpan H Mc ≤ Mc := conjugateSpanBy_le_self
    ((map_subtype_le _).trans hHM)
  let : ((partnerSpan H Mc).subgroupOf Mc).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  rw [threePrimeResidual_eq]
  have hm := map_mono (f := Mc.subtype) (primeToResidual_le
    ((partnerSpan H Mc).subgroupOf Mc) hi)
  rwa [map_subgroupOf_eq_of_le hKM] at hm

end CFSG.Quasithin.Chapter15.Section02.ChosenGeometry
