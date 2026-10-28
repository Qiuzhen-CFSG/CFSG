module

public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreCandidates
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.Containment
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreMaximality.Setup
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreMaximality.UpperBounds
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.E64Containment.CentralizerCertificates.CoreMaximality.Extensions
public import Theory.GroupTheory.TwoCoreOfIndexThree

/-!
# Finite-data assembly for the actual Held centralizer two-cores

For rows 1 and 3 let P be the intersection of the fixed representative with
the actual ambient centralizer C. The candidate Q already has order 256.
A checked order of 512 for P and an ambient bound |C| ≤ 1536 make Q have
index two in P. An element of order three centralizing the row and normalizing
Q, but not P, then proves normality and maximality of Q by
`Subgroup.normal_two_maximal_of_index_two_of_order_three`.

For row 5, the candidate has order 128, so the bound |C| ≤ 128 forces C = Q.
Every transfer uses the literal subgroup inclusions, including the two relative
normalizers. No subgroupOf expression is treated as an inclusion without proof.

The final theorem supplies the full-centralizer bounds from `UpperBounds` and
the intersection orders and order-three witnesses from `Extensions`. The checked
normalizing generator series supplies the representative's two-group property.
Thus the candidate certificates have no remaining hypotheses beyond the row
selection. The earlier conditional assembly remains available separately.
Source context: GLS3 Table 5.3p; quasithin condition E; original ATLAS Held words.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
open Subgroup LocalPairs.SylowGeometry.Calculations

/-- The two nontrivial-quotient rows from their independent finite inputs. -/
public theorem coreCandidate_normal_maximal_of_extension
    (hp : IsPGroup 2 representative) (j : Fin 22) (hj : j = 1 ∨ j = 3)
    (hbound : Nat.card (centralizer (ambient j : Set He)) ≤ 1536)
    (hPcard : Nat.card (centralizerTwoCandidate j) = 512)
    (t : He) (htC : t ∈ centralizer (ambient j : Set He)) (ht : orderOf t = 3)
    (htQ : t ∈ normalizer (coreCandidate j : Set He))
    (htP : t ∉ normalizer (centralizerTwoCandidate j : Set He)) :
    ((coreCandidate j).subgroupOf (centralizer (ambient j : Set He))).Normal ∧
      ∀ R : Subgroup (centralizer (ambient j : Set He)),
        R.Normal → IsPGroup 2 R →
          R ≤ (coreCandidate j).subgroupOf (centralizer (ambient j : Set He)) := by
  let C := centralizer (ambient j : Set He)
  let Q := (coreCandidate j).subgroupOf C
  let P := (centralizerTwoCandidate j).subgroupOf C
  have hj' : j = 1 ∨ j = 3 ∨ j = 5 := hj.imp_right Or.inl
  have hQC := coreCandidate_le_centralizer j hj'
  have hPC := centralizerTwoCandidate_le_centralizer j
  have hQP : Q ≤ P := fun _ hx => coreCandidate_le_centralizerTwoCandidate j hj' hx
  have hq : Nat.card Q = 256 :=
    (Nat.card_congr (subgroupOfEquivOfLe hQC).toEquiv).trans (coreCandidate_card j hj)
  have hp' : Nat.card P = 512 :=
    (Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv).trans hPcard
  have hindex : (Q.subgroupOf P).index = 2 := by
    have hc := (Q.subgroupOf P).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hQP).toEquiv, hq, hp'] at hc
    omega
  have htQ' : (⟨t, htC⟩ : C) ∈ normalizer (Q : Set C) := by
    rw [← subgroupOf_normalizer_eq hQC]
    exact htQ
  have htP' : (⟨t, htC⟩ : C) ∉ normalizer (P : Set C) := by
    rw [← subgroupOf_normalizer_eq hPC]
    exact htP
  exact normal_two_maximal_of_index_two_of_order_three Q P hQP
    ((centralizerTwoCandidate_isPGroup hp j).comap_subtype) hindex
    (by simpa only [hp'] using hbound) ⟨t, htC⟩
    (by simpa only [Subgroup.orderOf_mk] using ht) htQ' htP'

/-- The row-five centralizer equals the candidate once the ambient bound is checked. -/
public theorem coreCandidate_five_eq_centralizer_of_bound
    (hbound : Nat.card (centralizer (ambient 5 : Set He)) ≤ 128) :
    coreCandidate 5 = centralizer (ambient 5 : Set He) :=
  eq_of_le_of_card_ge (coreCandidate_le_centralizer 5 (Or.inr (Or.inr rfl)))
    (by simpa only [coreCandidate_five_card] using hbound)

/-- The certificate family from independent centralizer bounds and extension data. -/
public theorem centralizer_coreCandidate_certificates_of_bounds_and_extensions
    (hp : IsPGroup 2 representative)
    (hbound : ∀ j : Fin 22, j = 1 ∨ j = 3 →
      Nat.card (centralizer (ambient j : Set He)) ≤ 1536)
    (hfive : Nat.card (centralizer (ambient 5 : Set He)) ≤ 128)
    (hPcard : ∀ j : Fin 22, j = 1 ∨ j = 3 →
      Nat.card (centralizerTwoCandidate j) = 512)
    (hext : ∀ j : Fin 22, j = 1 ∨ j = 3 →
      ∃ t : He, t ∈ centralizer (ambient j : Set He) ∧ orderOf t = 3 ∧
        t ∈ normalizer (coreCandidate j : Set He) ∧
        t ∉ normalizer (centralizerTwoCandidate j : Set He)) :
    ∀ j : Fin 22, j = 1 ∨ j = 3 ∨ j = 5 →
      IsPGroup 2 ((coreCandidate j).subgroupOf (centralizer (ambient j : Set He))) ∧
      ((coreCandidate j).subgroupOf (centralizer (ambient j : Set He))).Normal ∧
      ∀ R : Subgroup (centralizer (ambient j : Set He)),
        R.Normal → IsPGroup 2 R →
          R ≤ (coreCandidate j).subgroupOf (centralizer (ambient j : Set He)) := by
  intro j hj
  refine ⟨centralizer_coreCandidate_isPGroup hp j, ?_⟩
  rcases hj with h | h | rfl
  · obtain ⟨t, htC, ht, htQ, htP⟩ := hext j (Or.inl h)
    exact coreCandidate_normal_maximal_of_extension hp j (Or.inl h)
      (hbound j (Or.inl h)) (hPcard j (Or.inl h)) t htC ht htQ htP
  · obtain ⟨t, htC, ht, htQ, htP⟩ := hext j (Or.inr h)
    exact coreCandidate_normal_maximal_of_extension hp j (Or.inr h)
      (hbound j (Or.inr h)) (hPcard j (Or.inr h)) t htC ht htQ htP
  · rw [coreCandidate_five_eq_centralizer_of_bound hfive, subgroupOf_self]
    exact ⟨inferInstance, fun _ _ _ => le_top⟩

/-- In each of the three actual Held centralizers, the literal candidate is a
normal two-subgroup containing every normal two-subgroup. All finite inputs are
discharged by the checked word, enumeration, and coset certificates. -/
public theorem centralizer_coreCandidate_certificates (j : Fin 22)
    (hj : j = 1 ∨ j = 3 ∨ j = 5) :
    IsPGroup 2 ((coreCandidate j).subgroupOf (centralizer (ambient j : Set He))) ∧
    ((coreCandidate j).subgroupOf (centralizer (ambient j : Set He))).Normal ∧
    ∀ R : Subgroup (centralizer (ambient j : Set He)),
      R.Normal → IsPGroup 2 R →
        R ≤ (coreCandidate j).subgroupOf (centralizer (ambient j : Set He)) :=
  centralizer_coreCandidate_certificates_of_bounds_and_extensions representative_isPGroup
    ambient_centralizer_card_bounds.1 ambient_centralizer_card_bounds.2
    centralizerTwoCandidate_card exists_order_three_extension j hj

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.E64Containment.CentralizerCertificates
