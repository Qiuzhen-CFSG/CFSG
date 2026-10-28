module

public import Glauberman.SuzukiCharacterization.Hypotheses
public import Glauberman.SuzukiCharacterization.NoncyclicCenter
public import Glauberman.SuzukiCharacterization.CentralizerReduction
public import Glauberman.SuzukiCharacterization.OddNormalizedExclusion

/-!
# Centralizer containment in Glauberman's Suzuki characterization

The group-theoretic completion on p. 92 of Glauberman, *A Characterization
of the Suzuki Groups* (1968), reduces containment to Theorem 4.1(i): P
normalizes no nontrivial odd-order subgroup. The noncyclic-center input is
proved independently using Z*. The odd-subgroup exclusion from Sections 3–4
discharges the explicit input of the group-theoretic reduction, proving
containment for every nonidentity element of P.

The complete paper is saved at
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

namespace Glauberman.SuzukiCharacterization

/-- Theorem 4.1(i) suffices for centralizer containment in the binary case. -/
public theorem Hypotheses.centralizer_le_of_no_normalized_odd_subgroup
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) (h : Hypotheses P)
    (hodd : ∀ H : Subgroup G, Nat.Coprime 2 (Nat.card H) →
      (P : Subgroup G) ≤ Subgroup.normalizer (H : Set G) → H = ⊥) :
    ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ (P : Subgroup G) :=
  h.centralizer_le_of_noncyclic_center_of_no_normalized_odd_subgroup P
    (h.not_isCyclic_center P) hodd

/-- Under Glauberman's Suzuki characterization hypotheses, the centralizer
of every nonidentity element of the Sylow two-subgroup lies in that subgroup. -/
public theorem Hypotheses.centralizer_le
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) (h : Hypotheses P) :
    ∀ x ∈ (P : Subgroup G), x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ (P : Subgroup G) :=
  h.centralizer_le_of_no_normalized_odd_subgroup P (h.odd_normalized_eq_bot P)

end Glauberman.SuzukiCharacterization
