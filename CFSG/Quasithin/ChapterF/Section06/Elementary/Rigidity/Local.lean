module

public import CFSG.Quasithin.ChapterF.Section06.Elementary.Residual

/-!
# The local two-core has index two in the common Sylow subgroup

The quotient image of the common Sylow subgroup is Sylow in the actual S₃
quotient and therefore has order two. We retain ambient embeddings and the
normalizer inclusion for later rigidity arguments.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, §F.6,
Hypothesis F.6.2 and the proofs of F.6.12 and F.6.14, printed pp.304, 307.
-/

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterF
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

private theorem sylow_core_index (S : Sylow 2 G)
    (he : Nonempty ((G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3))) :
    (pCore 2 G).relIndex (S : Subgroup G) = 2 := by
  obtain ⟨e⟩ := he
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))
  have hc : Nat.card (G ⧸ pCore 2 G) = 6 := by
    rw [Nat.card_congr e.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hp : Nat.card P = 2 := by
    rw [P.card_eq_multiplicity, hc]
    have hf : Nat.factorization 6 2 = 1 := by
      change Nat.factorization (2 * 3) 2 = 1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
    rw [hf, pow_one]
  rw [← QuotientGroup.ker_mk' (pCore 2 G), relIndex_ker]
  exact hp

/-- The embedded local two-core has relative index two in the common Sylow subgroup. -/
public theorem IsGoldschmidtTriple.left_core_index (h : IsGoldschmidtTriple G₁ G₂) :
    ((pCore 2 G₁).map G₁.subtype).relIndex (G₁ ⊓ G₂) = 2 := by
  obtain ⟨S, hS⟩ := h.intersection_sylow
  have hle : (S : Subgroup G) ≤ G₁ := hS.symm.le.trans inf_le_left
  have hind := sylow_core_index (S.subtype hle) h.quotient_left
  have hh := relIndex_map_map_of_injective (pCore 2 G₁)
    ((S.subtype hle : Sylow 2 G₁) : Subgroup G₁) G₁.subtype_injective
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hle, ← hS] at hh
  apply hh.trans
  simpa only [Sylow.coe_subtype, hS] using hind

/-- The left generator normalizes its embedded two-core. -/
public theorem IsGoldschmidtTriple.left_core_normalized (_h : IsGoldschmidtTriple G₁ G₂) :
    G₁ ≤ normalizer ((pCore 2 G₁).map G₁.subtype : Set G) := by
  have hn := (pCore 2 G₁).le_normalizer_map G₁.subtype
  simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hn


end CFSG.Quasithin.ChapterF
