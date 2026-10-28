module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ExternalQuotient.Product
public import Theory.GroupTheory.PrimeRankProduct
public import CFSG.Quasithin.Defs

/-!
# The bad-character external quotient and proper-two-local rank bound

For the actual external B=Y_E and H=G₀, the source kernel identities
place B₀ in N=O₂(H)∩ker χ. The nontrivial character branch gives
B∩H=B₀, O₂(B⊔H)=N, and the compatible cubic product in (B⊔K)/N.
The imported modules retain the quotient maps, the local core identities,
and the supplied Sylow subgroup.

The three-rank argument takes place in N_G(B₀). The nonidentity two-group
B₀ makes this a proper two-local of the finite simple ambient QTKE group.
Elementary three-subgroups lift isomorphically across N, so the independent
cubic factor forces m₃(H/O₂(H))≤1. No rank bound for arbitrary subgroups
of the ambient group is assumed.

Source: the repaired bad-character argument for Aschbacher–Smith 15.3.68,
combined manuscript (1 March 2004), printed pp.1152–1155. The final theorem
here is conditional on genuine preceding source data; module construction,
recognition and the proof of centrality remain with the parent argument.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ExternalQuotient
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem external_join_normalizes_core (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G)) :
    B ⊔ H ≤ normalizer (ambientTwoCore B : Set G) :=
  (sup_le B.le_normalizer hHB).trans
    (normalizer_le_normalizer_characteristic_image B (pCore 2 B))

theorem external_normalizer_proper_sqtk {𝒦 : CFSG.Quasithin.GroupClass.{u}}
    (hG : CFSG.Quasithin.IsSimpleQTKE 𝒦 G) (B : Subgroup G)
    (h0 : ambientTwoCore B ≠ ⊥) :
    normalizer (ambientTwoCore B : Set G) ≠ ⊤ ∧
      CFSG.Quasithin.IsSQTK 𝒦 (normalizer (ambientTwoCore B : Set G)) := by
  let := hG.simple
  have hlocal : IsTwoLocal (normalizer (ambientTwoCore B : Set G)) :=
    ⟨ambientTwoCore B,h0,isPGroup_pCoreIn 2 B,rfl⟩
  exact ⟨CFSG.Quasithin.twoLocal_ne_top_of_nonabelian_simple hG.nonabelian hlocal,
    hG.twoLocal_sqtk hlocal⟩

private theorem cubic_rank_pos (B : Subgroup G)
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) :
    1 ≤ primeRank 3 (B ⧸ localTwoCore B) := by
  let := isCyclic_of_prime_card hc
  let : CommGroup (B ⧸ localTwoCore B) := IsMulCommutative.instCommGroup
  apply primeRank_ge_of_elementary_embedding (p := 3) (e := 1)
    (G := B ⧸ localTwoCore B) (fun x => ?_) (by simpa using hc)
    (MonoidHom.id _) Function.injective_id
  rw [← hc]
  exact pow_card_eq_one'

/-- A quotient by a two-group cannot gain three-rank: lift an elementary subgroup attaining it. -/
private theorem quotient_three_rank_le {A : Type*} [Group A] [Finite A]
    (N : Subgroup A) [N.Normal] (hp : IsPGroup 2 N) :
    primeRank 3 (A ⧸ N) ≤ primeRank 3 A := by
  let π := QuotientGroup.mk' N
  have hcop : Nat.Coprime 3 (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n,hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  obtain ⟨E,hE,hc⟩ := exists_elementaryAbelian_card_primeRank (G := A ⧸ N) (p := 3)
  let := hE
  exact IsElementaryAbelian.primeRank_ge_of_coprime_quotient π
    (QuotientGroup.mk'_surjective N) hcop E hc

theorem rank_bound_of_product {𝒦 : CFSG.Quasithin.GroupClass.{u}}
    (hG : CFSG.Quasithin.IsSimpleQTKE 𝒦 G) (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (h0 : ambientTwoCore B ≠ ⊥)
    (hn : ((kernelIntersection H B hHB).subgroupOf (B ⊔ characterKernel H B hHB)).Normal)
    (e : letI := hn
      (B ⧸ localTwoCore B) × (H ⧸ localTwoCore H) ≃*
        ((B ⊔ characterKernel H B hHB : Subgroup G) ⧸
          (kernelIntersection H B hHB).subgroupOf (B ⊔ characterKernel H B hHB))) :
    primeRank 3 (H ⧸ localTwoCore H) ≤ 1 := by
  let := hn
  let J := B ⊔ characterKernel H B hHB
  let N := (kernelIntersection H B hHB).subgroupOf J
  have hN : IsPGroup 2 N := (isPGroup_pCoreIn 2 H).to_inf_left.comap_subtype
  have hJN : J ≤ normalizer (ambientTwoCore B : Set G) :=
    (sup_le_sup_left (map_subtype_le _) B).trans (external_join_normalizes_core H B hHB)
  have hupper : primeRank 3 J ≤ 2 :=
    (Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hJN)
      (inclusion_injective hJN)).trans
        ((external_normalizer_proper_sqtk hG B h0).2.stronglyQuasithin 3 Nat.prime_three (by decide))
  have hquot := quotient_three_rank_le N hN
  have he := Theory.GroupTheory.primeRank_equiv 3 e
  rw [primeRank_prod_eq_add] at he
  change primeRank 3 (B ⧸ localTwoCore B) + primeRank 3 (H ⧸ localTwoCore H) =
    primeRank 3 (J ⧸ N) at he
  have hpos := cubic_rank_pos B hc
  omega

/-- Discharge the quotient-product premise of the rank argument using the actual character. -/
theorem quotient_three_rank {𝒦 : CFSG.Quasithin.GroupClass.{u}}
    (hG : CFSG.Quasithin.IsSimpleQTKE 𝒦 G) (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (h0 : ambientTwoCore B ≠ ⊥)
    (h0N : ambientTwoCore B ≤ kernelIntersection H B hHB)
    (hbad : ∃ q : ambientTwoCore H, coreCharacter H B hHB q ≠ 1) :
    primeRank 3 (H ⧸ localTwoCore H) ≤ 1 := by
  have hinter := external_intersection H B hHB hc (h0N.trans inf_le_left) hbad
  obtain ⟨hn,e,_⟩ := kernel_join_product H B hHB hc hinter h0N hbad
  exact rank_bound_of_product hG H B hHB hc h0 hn e

/-- The external-group branch assembled from the source-local kernel outputs.
The equalities supplied by SourceKernel concern the two individual kernels,
not the invalid intersection of the two local cores. -/
theorem terminal_external_reduction {𝒦 : CFSG.Quasithin.GroupClass.{u}}
    (hG : CFSG.Quasithin.IsSimpleQTKE 𝒦 G) (H B G₁ S V : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (h0Q : ambientTwoCore B ≤ ambientTwoCore H)
    (h0U : ambientTwoCore B ≤ centralizer (conjugateSpanBy V H : Set G))
    (hN : kernelIntersection H B hHB = H ⊓ centralizer (conjugateSpanBy V H : Set G))
    (hV : V ≠ ⊥) (hV0 : V ≤ ambientTwoCore B)
    (hG₁ : G₁ ≤ H)
    (hR : ambientTwoCore G₁ ⊓ characterKernel H B hHB = centralizer (V : Set G))
    (hS : Chapter1.IsSylowIn 2 S H)
    (hbad : ∃ q : ambientTwoCore H,
      quotientAction H B hHB ⟨q.1,pCoreIn_le 2 H q.2⟩ ≠ 1) :
    let K := characterKernel H B hHB
    let N := kernelIntersection H B hHB
    B ⊓ H = ambientTwoCore B ∧
      (N.subgroupOf (B ⊔ H)).Normal ∧
      ambientTwoCore (B ⊔ H) = N ∧
      Chapter1.IsSylowIn 2 S (B ⊔ H) ∧
      ambientTwoCore K = N ∧
      ambientTwoCore (G₁ ⊓ K) = centralizer (V : Set G) ∧
      Chapter1.IsSylowIn 2 (S ⊓ K) K ∧
      primeRank 3 (H ⧸ localTwoCore H) ≤ 1 := by
  have h0N := external_core_le_kernel_inter H B (conjugateSpanBy V H) hHB h0Q h0U hN
  have hinter := external_intersection H B hHB hc h0Q hbad
  have hnorm := kernel_inter_normalized_join H B hHB h0N
  have h0 : ambientTwoCore B ≠ ⊥ := fun hz => hV (bot_unique (hV0.trans hz.le))
  exact ⟨hinter,normal_subgroupOf_of_le_normalizer hnorm,
    external_join_core H B hHB hc hinter h0N,
    sylow_in_external_join H B S hHB hc hinter hS,
    kernel_core H B hHB,first_kernel_core H B G₁ (centralizer (V : Set G)) hHB hG₁ hR,
    kernel_sylow H B S hHB hS,quotient_three_rank hG H B hHB hc h0 h0N hbad⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ExternalQuotient
