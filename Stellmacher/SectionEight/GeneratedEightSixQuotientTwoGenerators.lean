module

public import Stellmacher.LaterDefs
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Two generators for the small-index quotient in (8.6)

Two order-two images generating an elementary abelian quotient give quotient
order two or four. Transport by an ambient automorphism preserves both the
image order and its noncontainment in the kernel. The order-two alternative
is excluded using the supplied commutator generation equality.

The normalizer version proves the necessary order-two action triviality
directly. The callback version also permits applications where normalization
is available only after assuming quotient order two. Containment of `D` in
`Q` follows from generation; its relative normality follows from the quotient
witness, so neither needs to be imposed separately in the cardinal lemmas.
-/

namespace Stellmacher.SectionEight

open Later
open scoped commutatorElement IsMulCommutative

universe u

public theorem quotient_two_generators_commutator_le
    {G : Type u} [Group G] (Q D : Subgroup G)
    (helem : QuotientIsElementaryAbelian Q D 2) : ⁅Q, Q⁆ ≤ D := by
  obtain ⟨witness, helem⟩ := helem
  let _ := witness.groupX
  let _ := helem.toIsMulCommutative
  apply Subgroup.commutator_le.mpr
  intro first hfirst second hsecond
  have hker : ⁅(⟨first, hfirst⟩ : Q), (⟨second, hsecond⟩ : Q)⁆ ∈
      witness.projection.ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  rw [witness.kernel_eq] at hker
  exact hker

public theorem quotient_two_generators_transport
    {G : Type u} [Group G] [Finite G] (A B D : Subgroup G) (transport : G ≃* G)
    (hA : A.map transport.toMonoidHom = B)
    (hD : D.map transport.toMonoidHom = D)
    (hcard : QuotientCardEq A (A ⊓ D) 2) :
    QuotientCardEq B (B ⊓ D) 2 ∧ ¬ B ≤ D := by
  have hmap : (A ⊓ D).map transport.toMonoidHom = B ⊓ D := by
    rw [Subgroup.map_inf _ _ _ transport.injective, hA, hD]
  have hBcard : QuotientCardEq B (B ⊓ D) 2 := by
    unfold QuotientCardEq at *
    rw [← hmap, ← hA, Subgroup.card_map_of_injective transport.injective,
      Subgroup.card_map_of_injective transport.injective]
    exact hcard
  refine ⟨hBcard, ?_⟩
  intro hBD
  change Nat.card B = 2 * Nat.card (B ⊓ D : Subgroup G) at hBcard
  rw [inf_eq_left.mpr hBD] at hBcard
  have hpos : 0 < Nat.card B := Nat.card_pos
  omega

public theorem quotient_two_generators_card_cases
    {G : Type u} [Group G] [Finite G] (A B D Q : Subgroup G)
    (hgen : Q = A ⊔ B ⊔ D) (helem : QuotientIsElementaryAbelian Q D 2)
    (hA : QuotientCardEq A (A ⊓ D) 2)
    (hB : QuotientCardEq B (B ⊓ D) 2) :
    QuotientCardEq Q D 2 ∨ QuotientCardEq Q D 4 := by
  have hAQ : A ≤ Q := hgen ▸ le_sup_of_le_left le_sup_left
  have hBQ : B ≤ Q := hgen ▸ le_sup_of_le_left le_sup_right
  have hDQ : D ≤ Q := hgen ▸ le_sup_right
  have hcomm := quotient_two_generators_commutator_le Q D helem
  have hnorm : Q ≤ Subgroup.normalizer D :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono hDQ le_rfl).trans hcomm)
  have hAprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes D A
    (hAQ.trans hnorm)
  have hBprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes D B
    (hBQ.trans hnorm)
  rw [inf_comm D A, sup_comm D A] at hAprod
  rw [inf_comm D B, sup_comm D B] at hBprod
  change Nat.card A = 2 * Nat.card (A ⊓ D : Subgroup G) at hA
  change Nat.card B = 2 * Nat.card (B ⊓ D : Subgroup G) at hB
  have hAD : Nat.card (A ⊔ D : Subgroup G) = 2 * Nat.card D := by
    have hpos : 0 < Nat.card (A ⊓ D : Subgroup G) := Nat.card_pos
    nlinarith [hAprod]
  have hBD : Nat.card (B ⊔ D : Subgroup G) = 2 * Nat.card D := by
    have hpos : 0 < Nat.card (B ⊓ D : Subgroup G) := Nat.card_pos
    nlinarith [hBprod]
  have hADQ : A ⊔ D ≤ Q := sup_le hAQ hDQ
  have hBDQ : B ⊔ D ≤ Q := sup_le hBQ hDQ
  have hnormAD : B ⊔ D ≤ Subgroup.normalizer (A ⊔ D : Subgroup G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      (((Subgroup.commutator_mono hADQ hBDQ).trans hcomm).trans le_sup_right)
  have hprod := Subgroup.card_mul_eq_card_inf_mul_card_sup_of_normalizes
    (A ⊔ D) (B ⊔ D) hnormAD
  have hsup : (A ⊔ D) ⊔ (B ⊔ D) = Q := by rw [hgen]; ac_rfl
  rw [hsup, hAD, hBD] at hprod
  have hI : Nat.card D ≤ Nat.card ((A ⊔ D) ⊓ (B ⊔ D) : Subgroup G) :=
    Subgroup.card_le_of_le (le_inf le_sup_right le_sup_right)
  have hpos : 0 < Nat.card D := Nat.card_pos
  have hbound : Nat.card Q ≤ 4 * Nat.card D := by
    nlinarith [Nat.mul_le_mul_right (Nat.card Q) hI]
  obtain ⟨factor, hfactor⟩ := Subgroup.card_dvd_of_le hADQ
  rw [hAD] at hfactor
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hfactorpos : 0 < factor := by nlinarith
  have hfactorle : factor ≤ 2 := by nlinarith
  have hcases : factor = 1 ∨ factor = 2 := by omega
  rcases hcases with rfl | rfl
  · left; simpa [QuotientCardEq] using hfactor
  · right; simpa [QuotientCardEq, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      using hfactor

public theorem quotient_two_generators_commutator_le_of_card_two
    {G : Type u} [Group G] [Finite G] (Q D R : Subgroup G)
    (hDQ : D ≤ Q) (hRQ : R ≤ Subgroup.normalizer Q)
    (hRD : R ≤ Subgroup.normalizer D)
    (hcard : QuotientCardEq Q D 2) : ⁅Q, R⁆ ≤ D := by
  have hindex : D.relIndex Q = 2 := by
    have hproduct := (D.subgroupOf Q).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDQ).toEquiv] at hproduct
    change Nat.card D * D.relIndex Q = Nat.card Q at hproduct
    change Nat.card Q = 2 * Nat.card D at hcard
    have hpos : 0 < Nat.card D := Nat.card_pos
    nlinarith
  apply Subgroup.commutator_le.mpr
  intro element helement actor hactor
  have hconjQ : actor * element⁻¹ * actor⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hRQ hactor) _).mp (Q.inv_mem helement)
  have hconjD : element ∈ D ↔ actor * element⁻¹ * actor⁻¹ ∈ D :=
    D.inv_mem_iff.symm.trans (Subgroup.mem_normalizer_iff.mp (hRD hactor) _)
  have hmul := (D.subgroupOf Q).mul_mem_iff_of_index_two hindex
    (a := ⟨element, helement⟩) (b := ⟨actor * element⁻¹ * actor⁻¹, hconjQ⟩)
  have hmem := hmul.mpr hconjD
  simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, commutatorElement_def,
    mul_assoc] using hmem

public theorem quotient_two_generators_not_card_two
    {G : Type u} [Group G] (Q D B R : Subgroup G)
    (hBD : ¬ B ≤ D) (heq : ⁅Q, R⁆ ⊔ D = B ⊔ D)
    (hsmall : QuotientCardEq Q D 2 → ⁅Q, R⁆ ≤ D) :
    ¬ QuotientCardEq Q D 2 := by
  intro hcard
  apply hBD
  have hle : B ⊔ D ≤ D := by
    rw [← heq]
    exact sup_le (hsmall hcard) le_rfl
  exact le_sup_left.trans hle

public theorem quotient_two_generators_card_four
    {G : Type u} [Group G] [Finite G] (A B D Q R : Subgroup G)
    (hgen : Q = A ⊔ B ⊔ D) (helem : QuotientIsElementaryAbelian Q D 2)
    (hA : QuotientCardEq A (A ⊓ D) 2)
    (transport : G ≃* G) (htransport : A.map transport.toMonoidHom = B)
    (hD : D.map transport.toMonoidHom = D)
    (heq : ⁅Q, R⁆ ⊔ D = B ⊔ D)
    (hsmall : QuotientCardEq Q D 2 → ⁅Q, R⁆ ≤ D) :
    QuotientCardEq Q D 4 := by
  obtain ⟨hB, hBD⟩ := quotient_two_generators_transport A B D transport htransport hD hA
  exact (quotient_two_generators_card_cases A B D Q hgen helem hA hB).resolve_left
    (quotient_two_generators_not_card_two Q D B R hBD heq hsmall)

public theorem quotient_two_generators_card_four_of_normalizes
    {G : Type u} [Group G] [Finite G] (A B D Q R : Subgroup G)
    (hgen : Q = A ⊔ B ⊔ D) (helem : QuotientIsElementaryAbelian Q D 2)
    (hA : QuotientCardEq A (A ⊓ D) 2)
    (transport : G ≃* G) (htransport : A.map transport.toMonoidHom = B)
    (hD : D.map transport.toMonoidHom = D)
    (heq : ⁅Q, R⁆ ⊔ D = B ⊔ D)
    (hRQ : R ≤ Subgroup.normalizer Q) (hRD : R ≤ Subgroup.normalizer D) :
    QuotientCardEq Q D 4 := by
  apply quotient_two_generators_card_four A B D Q R hgen helem hA transport
    htransport hD heq
  exact quotient_two_generators_commutator_le_of_card_two Q D R
    (hgen ▸ le_sup_right) hRQ hRD

end Stellmacher.SectionEight
