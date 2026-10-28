module
public import Theory.GroupTheory.GeneralizedFitting.SylowCentralizerSchreier
/-!
# No components in a layer Sylow normalizer

A component of the normalizer centralizes its normal two-subgroup and the
ambient Fitting subgroup. The pointwise Sylow-fixer solvability supplied by
two-Schreier makes its perfect image centralize each ambient component.
It therefore centralizes the ambient generalized Fitting subgroup; its
self-centralization forces that image to be abelian, contradicting
quasisimplicity. No centrality assumption on the Fitting subgroup is used.

Source: the component-normalizer step in Aschbacher--Smith 2.5.3(4),
using the Schreier action argument of GLS II, Proposition B.5.16.
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


omit [Finite G] in
/-- A component centralizes every normal solvable subgroup. -/
theorem IsComponent.le_centralizer_normal_solvable {K : Subgroup G}
    (hK : IsComponent G K) (D : Subgroup G) [D.Normal] [Group.IsSolvable D] :
    K≤centralizer (D:Set G) := by
  rcases hK.normal_dichotomy D with hKD | hKD
  · let : IsQuasisimple K := hK.2
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective (inclusion_injective hKD)
    exact (Group.IsPerfect.not_isSolvable K inferInstance).elim
  · exact commutator_eq_bot_iff_le_centralizer.mp hKD

/-- A perfect subgroup centralizing the layer's Sylow two-group centralizes
the layer under the literal two-Schreier and even-quotient hypotheses. -/
theorem perfect_le_centralizer_layer_of_sylow
    (hS : HasTwoSchreier G)
    (heven : ∀ K : Subgroup G, IsComponent G K → 2 ∣ Nat.card (K ⧸ center K))
    (P : Sylow 2 (componentLayer G)) (A : Subgroup G) [Group.IsPerfect A]
    (hA : A≤centralizer ((P:Subgroup (componentLayer G)).map (componentLayer G).subtype : Set G)) :
    A≤centralizer (componentLayer G:Set G) := by
  apply le_centralizer_iff.mpr
  apply sSup_le
  intro K hK
  let := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  obtain ⟨T,hT⟩ := exists_component_sylow_le_layer_sylow hK P
  have hAT := hA.trans (centralizer_le hT)
  have hAK := hAT.trans (hK.centralizer_sylow_le_normalizer T (heven K hK))
  let : MulDistribMulAction A K := conjMulDistribMulActionOfLeNormalizer A K hAK
  let ρ := MulDistribMulAction.toMulAut A K
  let Q := T.mapSurjective (f:=QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
  let F := fixingSubgroup (MulAut (K ⧸ center K)) (Q:Set (K ⧸ center K))
  let : Group.IsSolvable F := hS K (K ⧸ center K) (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _) Q
  let f : A→*F := ((quotientAut (center K)).comp ρ).codRestrict F (by
    intro a
    apply (mem_fixingSubgroup_iff _).mpr
    rintro y ⟨t,ht,rfl⟩
    change quotientAut (center K) (ρ a) (QuotientGroup.mk' (center K) t)=_
    rw [quotientAut_apply_mk]
    congr 1
    apply Subtype.ext
    change (a:G)*(t:G)*(a:G)⁻¹=t
    rw [← hAT a.property (t:G) (mem_map_of_mem K.subtype ht),mul_inv_cancel_right])
  have hr : solvableResidual A≤f.ker := by
    have h := map_solvableResidual_le f
    rwa [solvableResidual_eq_bot (G:=F),map_le_iff_le_comap,MonoidHom.comap_bot] at h
  rw [solvableResidual_eq_top] at hr
  intro k hk a ha
  have hq : quotientAut (center K) (ρ ⟨a,ha⟩)=1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp (hr (mem_top _)))
  have hρ : ρ ⟨a,ha⟩=1 := MulAut.quotient_center_injective
    (hq.trans (map_one (quotientAut (center K))).symm)
  have hfix := congrArg (fun α:MulAut K => (α ⟨k,hk⟩:G)) hρ
  change a*k*a⁻¹=k at hfix
  exact mul_inv_eq_iff_eq_mul.mp hfix

/-- A layer Sylow-two normalizer has no components under the genuine section
Schreier property and evenness of the components' simple quotients. -/
theorem not_isComponent_normalizer_layer_sylow_of_twoSchreier
    (hS : HasTwoSchreier G)
    (heven : ∀ K : Subgroup G, IsComponent G K → 2 ∣ Nat.card (K ⧸ center K))
    (P : Sylow 2 (componentLayer G))
    (K : Subgroup (normalizer (((P:Subgroup (componentLayer G)).map
      (componentLayer G).subtype):Set G))) :
    ¬ IsComponent (normalizer (((P:Subgroup (componentLayer G)).map
      (componentLayer G).subtype):Set G)) K := by
  intro hK
  let Q := (P:Subgroup (componentLayer G)).map (componentLayer G).subtype
  let X := normalizer (Q:Set G)
  let A := K.map X.subtype
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  let : Group.IsPerfect A := Group.IsPerfect.map X.subtype
  have hQp : IsPGroup 2 Q := P.isPGroup'.map _
  let : (Q.subgroupOf X).Normal := inferInstance
  let : Group.IsNilpotent (Q.subgroupOf X) := (hQp.comap_subtype (K:=X)).isNilpotent
  have hKQ := hK.le_centralizer_normal_solvable (Q.subgroupOf X)
  have hAQ : A≤centralizer (Q:Set G) := by
    rintro a ⟨k,hk,rfl⟩ q hq
    exact congrArg Subtype.val (hKQ hk ⟨q,Q.le_normalizer hq⟩ hq)
  have hAE := perfect_le_centralizer_layer_of_sylow hS heven P A hAQ
  have hFE : fittingSubgroup G≤centralizer (componentLayer G:Set G) := by
    apply le_centralizer_iff.mpr
    apply sSup_le
    intro L hL
    exact hL.le_centralizer_normal_solvable (fittingSubgroup G)
  have hFX : fittingSubgroup G≤X :=
    (hFE.trans (centralizer_le (map_subtype_le _))).trans (Subgroup.centralizer_le_normalizer _)
  let : Group.IsSolvable ((fittingSubgroup G).subgroupOf X) :=
    Group.isSolvable_of_isSolvable_injective (f:=(subgroupOfEquivOfLe hFX).toMonoidHom) (subgroupOfEquivOfLe hFX).injective
  have hKF := hK.le_centralizer_normal_solvable ((fittingSubgroup G).subgroupOf X)
  have hAF : A≤centralizer (fittingSubgroup G:Set G) := by
    rintro a ⟨k,hk,rfl⟩ f hf
    exact congrArg Subtype.val (hKF hk ⟨f,hFX hf⟩ hf)
  have hAG : A≤centralizer (generalizedFitting G:Set G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp hAF) (le_centralizer_iff.mp hAE)
  have hcomm : IsMulCommutative K := by
    apply le_centralizer_iff_isMulCommutative.mp
    intro x hx y hy
    apply Subtype.ext
    exact hAG (mem_map_of_mem X.subtype hx) y
      (centralizer_generalizedFitting_le G (hAG (mem_map_of_mem X.subtype hy)))
  exact Group.IsPerfect.not_isMulCommutative K hcomm

/-- The layer of the literal normalizer is trivial. -/
theorem componentLayer_normalizer_layer_sylow_eq_bot_of_twoSchreier
    (hS : HasTwoSchreier G)
    (heven : ∀ K : Subgroup G, IsComponent G K → 2 ∣ Nat.card (K ⧸ center K))
    (P : Sylow 2 (componentLayer G)) :
    componentLayer (normalizer (((P:Subgroup (componentLayer G)).map
      (componentLayer G).subtype):Set G))=⊥ := by
  apply sSup_eq_bot.mpr
  intro K hK
  exact (not_isComponent_normalizer_layer_sylow_of_twoSchreier hS heven P K hK).elim

end Theory.GroupTheory
