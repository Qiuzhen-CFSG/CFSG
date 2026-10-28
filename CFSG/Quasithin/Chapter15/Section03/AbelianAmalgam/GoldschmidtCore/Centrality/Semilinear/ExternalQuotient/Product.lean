module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ExternalQuotient.LocalStructure
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# The actual external cubic quotient product

Let K be the kernel of the action of H on B/B₀ and N=O₂(H)∩K.
The images of B and K in (B⊔K)/N commute, generate the quotient, and
intersect trivially. The B-image has kernel B₀, while the K-image has
kernel N; the already constructed K/N≃H/O₂(H) therefore gives the
actual product C₃×(H/O₂(H)). The displayed representative formula
retains both original embeddings, including the chosen cubic marking.

Source: the repaired bad-character branch of Aschbacher–Smith 15.3.68,
combined manuscript (1 March 2004), printed pp.1152–1155. This is the
sufficient index-two subgroup of the proposed external S₃ product.
-/

@[expose] public section
open Subgroup Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ExternalQuotient
variable {G : Type*} [Group G] [Finite G]

noncomputable def cubicEquiv (B : Subgroup G)
    (hc : Nat.card (B ⧸ localTwoCore B) = 3) :
    (B ⧸ localTwoCore B) ≃* Multiplicative (ZMod 3) :=
  mulEquivOfPrimeCardEq hc (by simp)

theorem kernel_join_product (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (hinter : B ⊓ H = ambientTwoCore B)
    (h0N : ambientTwoCore B ≤ kernelIntersection H B hHB)
    (hbad : ∃ q : ambientTwoCore H, coreCharacter H B hHB q ≠ 1) :
    let K := characterKernel H B hHB
    let N := kernelIntersection H B hHB
    let J := B ⊔ K
    ∃ hn : (N.subgroupOf J).Normal,
      let := hn
      ∃ e : (B ⧸ localTwoCore B) × (H ⧸ localTwoCore H) ≃* (J ⧸ N.subgroupOf J),
        ∀ (b : B) (k : K),
          e (QuotientGroup.mk' _ b, kernelToCoreQuotient H B hHB k) =
            QuotientGroup.mk' _ ⟨(b : G) * (k : G), mul_mem_sup b.property k.property⟩ := by
  let K := characterKernel H B hHB
  let N := kernelIntersection H B hHB
  let J := B ⊔ K
  have hKH : K ≤ H := map_subtype_le _
  have hNK : N ≤ K := inf_le_right
  have hNB : N ⊓ B = ambientTwoCore B := by
    apply le_antisymm
    · intro x hx
      rw [← hinter]
      exact ⟨hx.2,hKH (hNK hx.1)⟩
    · exact le_inf h0N (pCoreIn_le 2 B)
  have hn : (N.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer
    ((sup_le_sup_left hKH B).trans (kernel_inter_normalized_join H B hHB h0N))
  refine ⟨hn,?_⟩
  let := hn
  let π := QuotientGroup.mk' (N.subgroupOf J)
  let fB : B →* (J ⧸ N.subgroupOf J) := π.comp (inclusion le_sup_left)
  let fK : K →* (J ⧸ N.subgroupOf J) := π.comp (inclusion le_sup_right)
  have hbker : fB.ker = localTwoCore B := by
    ext b
    change QuotientGroup.mk' (N.subgroupOf J) (inclusion le_sup_left b) = 1 ↔ _
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    change (b : G) ∈ N ↔ (b : G) ∈ ambientTwoCore B
    exact ⟨fun hb => hNB ▸ ⟨hb,b.property⟩,fun hb => h0N hb⟩
  have hkker : fK.ker = N.subgroupOf K := by
    ext k
    change QuotientGroup.mk' (N.subgroupOf J) (inclusion le_sup_right k) = 1 ↔ _
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    rfl
  have hdis : Disjoint fB.range fK.range := by
    apply disjoint_def.mpr
    rintro x ⟨b,rfl⟩ ⟨k,hk⟩
    have hbk : (b : G) * (k : G)⁻¹ ∈ N := by
      have he : fB b * (fK k)⁻¹ = 1 := by rw [hk,mul_inv_cancel]
      change π (inclusion le_sup_left b) * (π (inclusion le_sup_right k))⁻¹ = 1 at he
      rw [← map_inv,← map_mul] at he
      have hx : (inclusion (show B ≤ J from le_sup_left) b) *
          (inclusion (show K ≤ J from le_sup_right) k)⁻¹ ∈ N.subgroupOf J :=
        (QuotientGroup.eq_one_iff _).mp he
      exact hx
    have hbK : (b : G) ∈ K := by
      have h := K.mul_mem (hNK hbk) k.property
      simpa only [inv_mul_cancel_right] using h
    have hb0 : (b : G) ∈ ambientTwoCore B := hinter ▸ ⟨b.property,hKH hbK⟩
    exact show b ∈ fB.ker from hbker.symm ▸ hb0
  have hcomm : fB.range ≤ centralizer (fK.range : Set (J ⧸ N.subgroupOf J)) := by
    rintro x ⟨b,rfl⟩ y ⟨k,rfl⟩
    apply commutatorElement_eq_one_iff_mul_comm.mp
    change ⁅π (inclusion le_sup_right k), π (inclusion le_sup_left b)⁆ = 1
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact h0N ((mem_characterKernel_iff H B hHB k (hKH k.property)).mp k.property b b.property)
  have htop : fB.range ⊔ fK.range = ⊤ := by
    dsimp [fB,fK]
    rw [MonoidHom.range_comp,MonoidHom.range_comp,inclusion_range,inclusion_range,
      ← Subgroup.map_sup, ← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self,
      ← MonoidHom.range_eq_map,MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  let eB : (B ⧸ localTwoCore B) ≃* fB.range :=
    (QuotientGroup.quotientMulEquivOfEq hbker.symm).trans (QuotientGroup.quotientKerEquivRange fB)
  let eK : (K ⧸ N.subgroupOf K) ≃* fK.range :=
    (QuotientGroup.quotientMulEquivOfEq hkker.symm).trans (QuotientGroup.quotientKerEquivRange fK)
  let eH := kernelQuotientEquiv H B hHB hc hbad
  obtain ⟨em,hem⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting fB.range fK.range hdis hcomm
  let et : (fB.range ⊔ fK.range : Subgroup (J ⧸ N.subgroupOf J)) ≃* (J ⧸ N.subgroupOf J) :=
    (MulEquiv.subgroupCongr htop).trans topEquiv
  refine ⟨((eB.prodCongr (eH.symm.trans eK)).trans em).trans et,?_⟩
  intro b k
  have heH : eH.symm (kernelToCoreQuotient H B hHB k) = QuotientGroup.mk' _ k := by
    rw [← kernelQuotientEquiv_mk H B hHB hc hbad k]
    exact eH.symm_apply_apply _
  change ((em (eB (QuotientGroup.mk' _ b), eK (eH.symm (kernelToCoreQuotient H B hHB k)))) :
    J ⧸ N.subgroupOf J) = _
  rw [heH,hem]
  change fB b * fK k = _
  exact (map_mul π (inclusion le_sup_left b) (inclusion le_sup_right k)).symm


/-- The same actual quotient with the external factor identified with the concrete C₃. -/
theorem kernel_join_cubic_product (H B : Subgroup G)
    (hHB : H ≤ normalizer (B : Set G))
    (hc : Nat.card (B ⧸ localTwoCore B) = 3)
    (hinter : B ⊓ H = ambientTwoCore B)
    (h0N : ambientTwoCore B ≤ kernelIntersection H B hHB)
    (hbad : ∃ q : ambientTwoCore H, coreCharacter H B hHB q ≠ 1) :
    let K := characterKernel H B hHB
    let N := kernelIntersection H B hHB
    let J := B ⊔ K
    ∃ hn : (N.subgroupOf J).Normal,
      letI := hn
      ∃ e : Multiplicative (ZMod 3) × (H ⧸ localTwoCore H) ≃* (J ⧸ N.subgroupOf J),
        ∀ (b : B) (k : K),
          e (cubicEquiv B hc (QuotientGroup.mk' _ b), kernelToCoreQuotient H B hHB k) =
            QuotientGroup.mk' _ ⟨(b : G) * (k : G), mul_mem_sup b.property k.property⟩ := by
  obtain ⟨hn,e,he⟩ := kernel_join_product H B hHB hc hinter h0N hbad
  let := hn
  refine ⟨hn, (((cubicEquiv B hc).symm).prodCongr (MulEquiv.refl _)).trans e, ?_⟩
  intro b k
  change e ((cubicEquiv B hc).symm (cubicEquiv B hc (QuotientGroup.mk' _ b)),
    kernelToCoreQuotient H B hHB k) = _
  rw [MulEquiv.symm_apply_apply]
  exact he b k


section QuotientInclusion
variable (H B : Subgroup G) (hHB : H ≤ normalizer (B : Set G))
variable [((kernelIntersection H B hHB).subgroupOf (B ⊔ characterKernel H B hHB)).Normal]
variable [((kernelIntersection H B hHB).subgroupOf (B ⊔ H)).Normal]

/-- The actual inclusion of the sufficient product quotient in the full external quotient. -/
noncomputable def kernelJoinQuotientInclusion :
    ((B ⊔ characterKernel H B hHB : Subgroup G) ⧸
      (kernelIntersection H B hHB).subgroupOf (B ⊔ characterKernel H B hHB)) →*
    ((B ⊔ H : Subgroup G) ⧸ (kernelIntersection H B hHB).subgroupOf (B ⊔ H)) :=
  QuotientGroup.map _ _ (inclusion (sup_le_sup_left (map_subtype_le _) B)) (fun _ hx => hx)

omit [Finite G] in
theorem kernelJoinQuotientInclusion_mk (j : (B ⊔ characterKernel H B hHB : Subgroup G)) :
    kernelJoinQuotientInclusion H B hHB (QuotientGroup.mk' _ j) =
      QuotientGroup.mk' _ (inclusion (sup_le_sup_left (map_subtype_le _) B) j) := rfl

omit [Finite G] in
theorem kernelJoinQuotientInclusion_injective :
    Function.Injective (kernelJoinQuotientInclusion H B hHB) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro x hx
  obtain ⟨j,rfl⟩ := QuotientGroup.mk'_surjective _ x
  change kernelJoinQuotientInclusion H B hHB (QuotientGroup.mk' _ j) = 1 at hx
  rw [kernelJoinQuotientInclusion_mk] at hx
  have hjL : inclusion (sup_le_sup_left (map_subtype_le _) B) j ∈
      (kernelIntersection H B hHB).subgroupOf (B ⊔ H) :=
    (QuotientGroup.eq_one_iff _).mp hx
  exact show QuotientGroup.mk' _ j = 1 from (QuotientGroup.eq_one_iff j).mpr hjL
end QuotientInclusion

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.ExternalQuotient
