module
public import Theory.Representation.BinaryPermutation.SixTransitivity
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.PGroupCore
public import Theory.GroupAction.SubgroupConjugation
public import Mathlib.GroupTheory.Index

/-!
# Point-centralizer orders in a marked natural A₆ module

The actual A₆ action is transitive on the fifteen nonzero vectors. Lifting
through K → K/O₂(K) preserves that orbit, so the centralizer of every
nonidentity vector has order 24 |O₂(K)|. The proof uses the literal ambient
centralizer and conjugation action, with no enumeration or order-based
recognition of its quotient. The fixed-core source consumer uses the formula
to bound its three-rank and compare the reciprocal point residuals.

Source: Aschbacher–Smith, B.3 and 13.4.10(2–5), printed pp.83–85,908–909.
-/

public noncomputable section
open Subgroup
namespace BinaryPermutation
variable {G : Type*} [Group G] [Finite G]

theorem six_natural_point_card (K U : Subgroup G)
    (hn : K ≤ normalizer (U : Set G))
    (q : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6))
    (e : U ≃* Multiplicative (natural (Fin 6)))
    (he : ∀ (k : K) (v : U),
      (e (U.normalizerMonoidHom ⟨k.val,hn k.property⟩ v)).toAdd =
        alternatingNaturalRepresentation (Fin 6) (q (QuotientGroup.mk' (pCore 2 K) k))
          (e v).toAdd)
    (w : U) (hw : w ≠ 1) :
    Nat.card (K ⊓ centralizer ({w.val} : Set G) : Subgroup G) =
      24 * Nat.card (pCore 2 K) := by
  let := conjMulDistribMulActionOfLeNormalizer K U hn
  have hcard : Nat.card U = 16 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (natural (Fin 6)) = 16
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      finrank_natural_even _ (by decide)]
    norm_num
  have horbit : MulAction.orbit K w = ({1} : Set U)ᶜ := by
    ext v
    constructor
    · rintro ⟨k,rfl⟩
      change k • w ≠ 1
      intro hh
      exact hw ((MulAction.injective k) (hh.trans (smul_one k).symm))
    · intro hv
      have hv1 : v ≠ 1 := hv
      obtain ⟨a,ha⟩ := alternatingSix_natural_nonzero_transitive (e w).toAdd (e v).toAdd
        (fun hh => hw (e.injective (hh.trans e.map_one.symm)))
        (fun hh => hv1 (e.injective (hh.trans e.map_one.symm)))
      obtain ⟨b,hb⟩ := q.surjective a
      obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) b
      refine ⟨k,?_⟩
      apply e.injective
      apply Multiplicative.toAdd.injective
      exact (he k w).trans (hb ▸ ha)
  let C := (centralizer ({w.val} : Set G)).subgroupOf K
  have hs : MulAction.stabilizer K w = C := by
    ext k
    change k • w = w ↔ k.val ∈ centralizer ({w.val} : Set G)
    rw [Subtype.ext_iff]
    change k.val * w.val * k.val⁻¹ = w.val ↔ _
    rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff,eq_comm]
  have hi : C.index = 15 := by
    rw [←hs,MulAction.index_stabilizer,horbit,Set.ncard_compl,Set.ncard_singleton,hcard]
  have hK : Nat.card K = 360 * Nat.card (pCore 2 K) := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 K),Nat.card_congr q.toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hmul := C.card_mul_index
  rw [hi,hK] at hmul
  have hC : Nat.card C = Nat.card (K ⊓ centralizer ({w.val} : Set G) : Subgroup G) :=
    by
      rw [show C = (K ⊓ centralizer ({w.val} : Set G)).subgroupOf K from (inf_subgroupOf_left _ _).symm]
      exact Nat.card_congr (subgroupOfEquivOfLe (show K ⊓ centralizer ({w.val} : Set G) ≤ K from inf_le_left)).toEquiv
  rw [hC] at hmul
  omega

end BinaryPermutation
