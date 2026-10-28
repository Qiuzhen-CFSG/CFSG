module

public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.SylowPointwiseSection
public import Theory.GroupAction.SubgroupConjugation
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Solvability of a layer Sylow centralizer under two-Schreier

A Sylow subgroup of the layer meets each component in a Sylow subgroup.
Its image in the simple central quotient is nontrivial. An element fixing
that Sylow subgroup cannot move the component to a distinct commuting
component. The resulting action on each simple quotient lies in its actual
pointwise Sylow fixer. Two-Schreier makes that fixer solvable, and
perfectness makes the central-quotient automorphism action faithful.

The solvable residual of the centralizer therefore centralizes the layer.
If F(G) is central, it centralizes F*(G); generalized-Fitting
self-centralization makes this residual abelian and hence trivial.
The even-order hypothesis on the simple central quotients is explicit so
that the odd order theorem can be supplied by the source adapter.
Source: GLS II, Chapter B, proof of Proposition 5.16.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem exists_component_sylow_le_layer_sylow
    {K : Subgroup G} (hK : IsComponent G K) (P : Sylow 2 (componentLayer G)) :
    ∃ T : Sylow 2 K, (T : Subgroup K).map K.subtype ≤
      (P : Subgroup (componentLayer G)).map (componentLayer G).subtype := by
  obtain ⟨S, hS⟩ := P.exists_comap_subtype_eq
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_subnormal K hK.1
  refine ⟨T, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxS : (x : G) ∈ (S : Subgroup G) := by
    rw [hT] at hx
    exact hx
  have hxE : (x : G) ∈ componentLayer G :=
    (show K ≤ componentLayer G from le_sSup hK) x.property
  refine ⟨⟨x, hxE⟩, ?_, rfl⟩
  rw [← hS]
  exact hxS

theorem IsComponent.centralizer_sylow_le_normalizer
    {K : Subgroup G} (hK : IsComponent G K) (T : Sylow 2 K)
    (hdiv : 2 ∣ Nat.card (K ⧸ center K)) :
    centralizer ((T : Subgroup K).map K.subtype : Set G) ≤ normalizer (K : Set G) := by
  intro z hz
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hne
  have hc := hK.commutator_eq_bot_of_ne (hK.map_conj z) (Ne.symm hne)
  have hTZ : (T : Subgroup K) ≤ center K := by
    intro t ht
    have hfix : MulAut.conj z (t : G) = t := by
      change z * (t : G) * z⁻¹ = t
      rw [← hz (t : G) (mem_map_of_mem K.subtype ht), mul_inv_cancel_right]
    have htc : (t : G) ∈ K.map (MulAut.conj z).toMonoidHom :=
      hfix ▸ mem_map_of_mem (MulAut.conj z).toMonoidHom t.property
    apply mem_center_iff.mpr
    intro k
    exact Subtype.ext ((commutator_eq_bot_iff_le_centralizer.mp hc k.property) t htc).symm
  let Q := T.mapSurjective (f := QuotientGroup.mk' (center K))
    (QuotientGroup.mk'_surjective _)
  apply Q.ne_bot_of_dvd_card hdiv
  change (T : Subgroup K).map (QuotientGroup.mk' (center K)) = ⊥
  exact (Subgroup.map_eq_bot_iff _).mpr
    (by simpa only [QuotientGroup.ker_mk'] using hTZ)

theorem solvable_centralizer_layer_sylow_of_twoSchreier
    (hS : HasTwoSchreier G)
    (heven : ∀ K : Subgroup G, IsComponent G K → 2 ∣ Nat.card (K ⧸ center K))
    (hF : fittingSubgroup G ≤ center G) (P : Sylow 2 (componentLayer G)) :
    Group.IsSolvable (centralizer
      ((P : Subgroup (componentLayer G)).map (componentLayer G).subtype : Set G)) := by
  let C := centralizer
    ((P : Subgroup (componentLayer G)).map (componentLayer G).subtype : Set G)
  have hcentral : (solvableResidual C).map C.subtype ≤
      centralizer (componentLayer G : Set G) := by
    apply le_centralizer_iff.mpr
    apply sSup_le
    intro K hK
    let := hK.2
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    obtain ⟨T, hT⟩ := exists_component_sylow_le_layer_sylow hK P
    have hCT : C ≤ centralizer ((T : Subgroup K).map K.subtype : Set G) :=
      centralizer_le hT
    have hCK : C ≤ normalizer (K : Set G) :=
      hCT.trans (hK.centralizer_sylow_le_normalizer T (heven K hK))
    let : MulDistribMulAction C K := conjMulDistribMulActionOfLeNormalizer C K hCK
    let ρ := MulDistribMulAction.toMulAut C K
    let Q := T.mapSurjective (f := QuotientGroup.mk' (center K))
      (QuotientGroup.mk'_surjective _)
    let F := fixingSubgroup (MulAut (K ⧸ center K)) (Q : Set (K ⧸ center K))
    let : Group.IsSolvable F := hS K (K ⧸ center K)
      (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) Q
    let f : C →* F := ((quotientAut (center K)).comp ρ).codRestrict F (by
      intro c
      apply (mem_fixingSubgroup_iff _).mpr
      rintro y ⟨t, ht, rfl⟩
      change quotientAut (center K) (ρ c) (QuotientGroup.mk' (center K) t) = _
      rw [quotientAut_apply_mk]
      congr 1
      apply Subtype.ext
      change (c : G) * (t : G) * (c : G)⁻¹ = t
      rw [← hCT c.property (t : G) (mem_map_of_mem K.subtype ht),
        mul_inv_cancel_right])
    have hr : solvableResidual C ≤ f.ker := by
      have h := map_solvableResidual_le f
      rwa [solvableResidual_eq_bot (G := F), map_le_iff_le_comap,
        MonoidHom.comap_bot] at h
    intro k hk r hrC
    obtain ⟨c, hc, rfl⟩ := hrC
    have hq : quotientAut (center K) (ρ c) = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp (hr hc))
    have hρ : ρ c = 1 := MulAut.quotient_center_injective
      (hq.trans (map_one (quotientAut (center K))).symm)
    have hfix := congrArg (fun a : MulAut K => (a ⟨k, hk⟩ : G)) hρ
    change (c : G) * k * (c : G)⁻¹ = k at hfix
    exact mul_inv_eq_iff_eq_mul.mp hfix
  have hGF : (solvableResidual C).map C.subtype ≤ centralizer (generalizedFitting G : Set G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (hF.trans (center_le_centralizer _)) (le_centralizer_iff.mp hcentral)
  let R := solvableResidual C
  have hcomm : IsMulCommutative R := by
    apply le_centralizer_iff_isMulCommutative.mp
    intro x hx y hy
    apply Subtype.ext
    have hx' := hGF (mem_map_of_mem C.subtype hx)
    have hy' := centralizer_generalizedFitting_le G
      (hGF (mem_map_of_mem C.subtype hy))
    exact hx' y hy'
  let : IsMulCommutative R := hcomm
  let : Subsingleton R := Group.IsPerfect.subsingleton_of_isMulCommutative
  let : Group.IsSolvable R := inferInstance
  exact Group.isSolvable_of_ker_le_range R.subtype (QuotientGroup.mk' R)
    (by rw [QuotientGroup.ker_mk', range_subtype])

end Theory.GroupTheory
