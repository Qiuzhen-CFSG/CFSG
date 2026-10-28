module
public import Theory.GroupTheory.RankOneCentralChiefKernel
public import Theory.GroupTheory.PCoreResidualCentralQuotient
public import Theory.GroupTheory.UniqueMaximalQuotient
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.SylowTwistedGeneratingPair

/-!
# The actual quotient satisfying the rank-one Main Hypothesis

The maximal automorphism-invariant normal kernel gives an induced automorphism
on the literal quotient image of the original Sylow subgroup. Its maximality
excludes every nontrivial ambient-normal subgroup fixed by that automorphism.
Residual centralization preserves characteristic two through the quotient,
and subgroup correspondence preserves the unique Sylow maximal subgroup.
The original simple quotient is retained by the third isomorphism theorem.

Combining these facts with the central-chief construction proves every
quotient hypothesis in Niles (1979), Theorem 7.2, conditional only on the
explicit cyclic-orbit identity from Lemma 7.6. That identity is a separate
source proof; it is not hidden in an asserted Main Hypothesis witness.
-/

public section
open Subgroup NilesRankOneKernel
namespace Theory.GroupTheory
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem quotientImage_noInvariantNormal
    (S : Subgroup H) (α : MulAut S) :
    ∃ β : MulAut (S.map (QuotientGroup.mk'
      ((invariantNormalKernel S α).map S.subtype))),
      NoInvariantNormal (S.map (QuotientGroup.mk'
        ((invariantNormalKernel S α).map S.subtype))) β := by
  obtain ⟨β,hβ⟩ := exists_quotientImageAut S α
  refine ⟨β, ?_⟩
  intro B hB hfix
  let P := S.map (QuotientGroup.mk' ((invariantNormalKernel S α).map S.subtype))
  let L := B.map P.subtype
  let _ := hB
  have hL : L = ⊥ := quotient_normal_eq_bot_of_imageAut_fixed S α β hβ L
    (map_subtype_le B) (by
      change ((B.map P.subtype).comap P.subtype).map β.toMonoidHom =
        (B.map P.subtype).comap P.subtype
      rw [comap_map_eq_self_of_injective P.subtype_injective]
      exact hfix)
  exact (B.map_eq_bot_iff_of_injective P.subtype_injective).mp hL

theorem invariantKernel_quotient_structure
    (S : Sylow 2 H) (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (hf : generalizedFitting H = pCore 2 H) (α : MulAut S)
    (hR : pResidual 2 H ≤ centralizer
      ((invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype : Set H)) :
    generalizedFitting (H ⧸ (invariantNormalKernel (S : Subgroup H) α).map
        (S : Subgroup H).subtype) =
      pCore 2 (H ⧸ (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype) ∧
    Order.HasUniqueMaximalOver ((S : Subgroup H).map (QuotientGroup.mk'
      ((invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype))) ⊤ ∧
    ∃ β : MulAut ((S : Subgroup H).map (QuotientGroup.mk'
      ((invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype))),
      NoInvariantNormal ((S : Subgroup H).map (QuotientGroup.mk'
        ((invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype))) β := by
  let N := (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype
  let q := QuotientGroup.mk' N
  have hq := QuotientGroup.mk'_surjective N
  have hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    hf ▸ centralizer_generalizedFitting_le H
  have hqc : centralizer (pCore 2 (H ⧸ N) : Set (H ⧸ N)) ≤ pCore 2 (H ⧸ N) :=
    q.centralizer_pCore_le_of_surjective_residualCentralizesKernel hq
      (by simpa only [q,QuotientGroup.ker_mk'] using hR) hc
  exact ⟨generalizedFitting_eq_pCore_of_selfCentralizing 2 hqc,
    hasUniqueMaximalOver_map_of_surjective q hq
      (by simpa only [q,QuotientGroup.ker_mk'] using
        (map_subtype_le (invariantNormalKernel (S : Subgroup H) α))) hu,
    quotientImage_noInvariantNormal (S : Subgroup H) α⟩

/-- All actual Main Hypothesis quotient inputs follow from the central-chief
kernel construction, retaining the original simple quotient and Sylow image. -/
theorem exists_main_quotient_of_orbit_formula
    (S : Sylow 2 H) (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal] [IsSimpleGroup (H ⧸ K)]
    (hK : ¬ IsPGroup 2 (H ⧸ K))
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoCharacteristicNormal (S : Subgroup H))
    (hformula : ∀ α : MulAut S,
      (omegaCenterIn (pCore 2 H)).subgroupOf (S : Subgroup H) ≤
        invariantNormalKernel (S : Subgroup H) α →
      invariantNormalKernel (S : Subgroup H) α =
        ⨅ n : ℤ, ((pCore 2 H).subgroupOf (S : Subgroup H)).map ((α ^ n).toMonoidHom)) :
    ∃ α : MulAut S,
      let N := (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype
      let q := QuotientGroup.mk' N
      ∃ s : NoncentralChiefRefinement.SeriesOn N, (∀ i, s.Central i) ∧ N ≤ K ∧
        Nonempty (((H ⧸ N) ⧸ K.map q) ≃* (H ⧸ K)) ∧
        generalizedFitting (H ⧸ N) = pCore 2 (H ⧸ N) ∧
        Order.HasUniqueMaximalOver ((S : Subgroup H).map q) ⊤ ∧
        ∃ β : MulAut ((S : Subgroup H).map q),
          NoInvariantNormal ((S : Subgroup H).map q) β := by
  obtain ⟨α,s,hc⟩ := exists_central_chief_invariantKernel_of_orbit_formula
    S hu K hK hf hno hformula
  refine ⟨α,s,hc,?_⟩
  let N := (invariantNormalKernel (S : Subgroup H) α).map (S : Subgroup H).subtype
  have hNS : N ≤ (S : Subgroup H) := map_subtype_le _
  have hp : IsPGroup 2 N := S.isPGroup'.of_injective (inclusion hNS) (inclusion_injective hNS)
  have hNQ : N ≤ pCore 2 H := le_sSup ⟨inferInstance,hp⟩
  have hQK : pCore 2 H ≤ K := by
    simpa only [QuotientGroup.ker_mk'] using
      MinimalParabolicKernel.core_le_simple_kernel (QuotientGroup.mk' K)
        (QuotientGroup.mk'_surjective K) hK
  have hNK := hNQ.trans hQK
  exact ⟨hNK, ⟨QuotientGroup.quotientQuotientEquivQuotient N K hNK⟩,
    invariantKernel_quotient_structure S hu hf α
      (residual_le_centralizer_of_central_chief_series N hp s hc)⟩

end Theory.GroupTheory
