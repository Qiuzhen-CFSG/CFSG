module

public import Glauberman.SuzukiCharacterization.NormalizerFrobenius
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupAction.NormalizerConjugacyFibers

/-!
# Normalizer conjugacy-fiber cardinalities

Write N = N_G(P), K = O_{2'}(N). Fusion control identifies ambient conjugacy
of elements of P with nonempty fibers of the normalizer action. Each such
fiber has order |C_N(x)|. For nonidentity x, the centralizer factorization
C_N(x) = C_P(x)K and disjointness of the two and odd factors give
|C_N(x)| = |C_P(x)||K|. Similarly |PK| = |P||K|. These identities give the
weighted fiber count required for the principal-block restriction pairing.

Source: Glauberman, *A Characterization of the Suzuki Groups* (1968),
equations (3.2)–(3.5), pp. 83–84, saved at
`refs/original/n-group-global/odd-core-rank-two-source/glauberman-suzuki-1968-euclid-wayback.pdf`.
-/

open Subgroup
attribute [local instance] Classical.propDecidable

namespace Glauberman.SuzukiCharacterization
variable {G : Type*} [Group G] [Finite G]
private theorem normalizer_sylow_disjoint_oddCore (P : Sylow 2 G) :
    Disjoint ((P : Subgroup G).subgroupOf (normalizer (P : Set G)))
      (pPrimeCore 2 (normalizer (P : Set G))) := by
  let S := P.subtype (P : Subgroup G).le_normalizer
  obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
  apply disjoint_of_coprime_natCard
  change Nat.Coprime (Nat.card S) _
  rw [hk]
  exact (pPrimeCore_coprime_card (p := 2)).pow_left k

/-- The Sylow subgroup and odd core have disjoint product in the normalizer. -/
public theorem normalizerSylowCore_card (P : Sylow 2 G) : Nat.card (normalizerSylowCore P) =
    Nat.card P * Nat.card (pPrimeCore 2 (normalizer (P : Set G))) := by
  let S := (P : Subgroup G).subgroupOf (normalizer (P : Set G))
  have hd : Disjoint S (pPrimeCore 2 (normalizer (P : Set G))) :=
    normalizer_sylow_disjoint_oddCore P
  change Nat.card ↥(S ⊔ _) = _
  rw [sup_comm, card_sup_eq_mul_of_normalizes_of_disjoint _ _
    le_normalizer_of_normal hd.symm]
  dsimp only [S]
  rw [Nat.card_congr (subgroupOfEquivOfLe (K := normalizer (P : Set G))
    (P : Subgroup G).le_normalizer).toEquiv]
  exact Nat.mul_comm _ _

/-- The order of the centralizer in the normalizer splits into its two and odd parts. -/
public theorem Hypotheses.normalizer_centralizer_card (P : Sylow 2 G) (h : Hypotheses P)
    (x : P) (hx : x ≠ 1) :
    Nat.card (centralizer
      ({⟨x, (P : Subgroup G).le_normalizer x.property⟩} : Set (normalizer (P : Set G)))) =
      Nat.card (centralizer ({x} : Set P)) *
        Nat.card (pPrimeCore 2 (normalizer (P : Set G))) := by
  let nx : normalizer (P : Set G) := ⟨x, (P : Subgroup G).le_normalizer x.property⟩
  have hnx : nx ≠ 1 := fun he => hx (Subtype.ext (congrArg (fun z : normalizer (P : Set G) => (z : G)) he))
  rw [h.normalizer_centralizer_eq P nx x.property hnx, sup_comm,
    card_sup_eq_mul_of_normalizes_of_disjoint _ _ le_normalizer_of_normal
      ((normalizer_sylow_disjoint_oddCore P).mono_left inf_le_left).symm,
    card_inf_centralizer_subgroupOf (P : Subgroup G) (normalizer (P : Set G))
      (P : Subgroup G).le_normalizer x]
  exact Nat.mul_comm _ _

/-- The normalizer conjugacy-fiber count used in the restriction pairing formula. -/
public theorem Hypotheses.normalizer_conjugacy_fiber_card (P : Sylow 2 G) (h : Hypotheses P)
    (x : P) (hx : x ≠ 1) (y : P) :
    Nat.card P * Nat.card {n : normalizer (P : Set G) //
      (P : Subgroup G).normalizerMonoidHom n x = y} =
    if IsConj (x : G) (y : G) then
      Nat.card (normalizerSylowCore P) * Nat.card (centralizer ({x} : Set P)) else 0 := by
  by_cases hxy : IsConj (x : G) (y : G)
  · rw [if_pos hxy, normalizerSylowCore_card]
    obtain ⟨n, hn, hny⟩ := h.fusion x x.property y y.property hxy
    have hf : Nat.card {n : normalizer (P : Set G) //
        (P : Subgroup G).normalizerMonoidHom n x = y} =
        Nat.card (centralizer
          ({⟨x, (P : Subgroup G).le_normalizer x.property⟩} :
            Set (normalizer (P : Set G)))) :=
      card_normalizer_conjugacy_fiber_of_witness (P : Subgroup G) x y
        ⟨n, hn⟩ (Subtype.ext hny)
    rw [hf, h.normalizer_centralizer_card P x hx]
    ac_rfl
  · rw [if_neg hxy]
    have : IsEmpty {n : normalizer (P : Set G) //
        (P : Subgroup G).normalizerMonoidHom n x = y} :=
      ⟨fun n => hxy (isConj_iff.mpr ⟨(n.val : G), congrArg Subtype.val n.property⟩)⟩
    simp only [Nat.card_of_isEmpty, mul_zero]
end Glauberman.SuzukiCharacterization
