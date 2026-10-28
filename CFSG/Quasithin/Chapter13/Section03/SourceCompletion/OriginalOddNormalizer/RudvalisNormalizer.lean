module

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisPoints
public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalizerQuotient
public import Theory.SpecificGroups.Rudvalis.TransitiveSixtyFourNormalizer

/-!
# The original Rudvalis local normalizer and its module kernel

In the same central quotient marking as the original residual and full
module, C.2.12 identifies the residual-image normalizer with the image of
K intersect N(L). The transitive E64 calculation identifies its two-core,
and inherited characteristic two makes its module centralizer exactly E64.
The last theorem applies these results to the actual escaping odd-actor
pair, retaining the original relative Sylow and section conjugation.

The full normalizer order, rank-three flag and quaternion-intersection
calculation, J4 exclusion and odd-normalizer discharge remain with
qt-d-13316-source. The earlier Structural1222 input retains its final
source discharge with qt-theorem-d.
Source: Aschbacher--Smith 4.2.13 and 4.4.5--6, printed pp.611--612,620.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original local intersection maps onto the full residual-image
normalizer, whose two-core and module centralizer are the same literal E64. -/
theorem unitary_original_pushingUp_rudvalis_normalizer (s : Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Rudvalis.Model)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let B := ((Y.subgroupOf H).subgroupOf K).map f
    let E := ((W.subgroupOf H).subgroupOf K).map f
    let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
    normalizer (B : Set Rudvalis.Model) = C ∧
      C.pCoreIn 2 = E ∧ C ⊓ centralizer (E : Set Rudvalis.Model) = E := by
  let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let q := QuotientGroup.mk' (center K)
  let f := e.toMonoidHom.comp q
  let A := (Y.subgroupOf H).subgroupOf K
  let U := (W.subgroupOf H).subgroupOf K
  let C0 := ((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K
  let B := A.map f
  let E := U.map f
  let C := C0.map f
  change normalizer (B : Set Rudvalis.Model) = C ∧
    C.pCoreIn 2 = E ∧ C ⊓ centralizer (E : Set Rudvalis.Model) = E
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have hM := h12.source_normalizer_maximal_unique s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer s.chosen.sylow_normalizes_component,hM.2⟩
  obtain ⟨hn,a,_⟩ := source_intersection_quotient h12.toHypothesis1221 hu hcover hJH
  have hspan : conjugateSpanBy Y (H ⊓ normalizer (L : Set G)) = Y :=
    hc.normalized_span_eq ((normal_subgroupOf_iff_le_normalizer hc.component_le).mp hn)
  have hYH : Y ≤ H := hc.component_le.trans hc.local_le
  have hYK : Y.subgroupOf H ≤ K := hc.ordinary_component_contains_original K hK
  have hWY : W ≤ Y := hc.module_le.trans hspan.le
  have hEB : E ≤ B := map_mono (subgroupOf_mono K (subgroupOf_mono H hWY))
  have hE : Nat.card E = 64 := by
    dsimp only [E,f]
    rw [←map_map,card_map_of_injective e.injective]
    exact hc.unitary_ordinary_rudvalis_module_card (a.trans s.quotient) K hK e
  obtain ⟨hBE,hB,_⟩ := unitary_original_pushingUp_rudvalis_module_and_points
    s hcover hJH hc K hK e c hVW
  change B.pCoreIn 2 = E at hBE
  change Nat.card B = 64 * 6048 at hB
  obtain ⟨hNC,hchar⟩ := hc.ordinary_image_normalizer K hK
  rw [hspan] at hNC
  have hNC' : normalizer (B : Set Rudvalis.Model) = C := by
    have he := congrArg (map e.toMonoidHom) hNC
    rw [map_normalizer_eq_of_bijective _ e.bijective,map_map,map_map] at he
    exact he
  let d : C0.map q ≃* C := (e.subgroupMap (C0.map q)).trans
    (MulEquiv.subgroupCongr (map_map _ _ _))
  have hchar' := (Theory.Quasithin.centralizer_pCore_le_iff 2 d).mp hchar
  obtain ⟨_,hel,_,_,_,_⟩ := hc.unitary_ordinary_module_image (a.trans s.quotient) K hK
  let : IsElementaryAbelian 2 (U.map q) := hel
  let instE : IsElementaryAbelian 2 E := by
    let dE : (U.map q).map e.toMonoidHom ≃* E := MulEquiv.subgroupCongr (map_map _ _ _)
    let : IsElementaryAbelian 2 ((U.map q).map e.toMonoidHom) := IsElementaryAbelian.map _
    exact IsElementaryAbelian.of_surjective dE.toMonoidHom dE.surjective
  have hBC : B ≤ C := hNC' ▸ B.le_normalizer
  have hCE : C ≤ normalizer (E : Set Rudvalis.Model) := by
    rw [←hNC',←hBE]
    exact normalizer_le_normalizer_characteristic_image B (pCore 2 B)
  have ht : ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 → ∃ b ∈ B, b*x*b⁻¹ = y := by
    intro x hx y hy hx1 hy1
    obtain ⟨u,hu,rfl⟩ := hx
    obtain ⟨v,hv,rfl⟩ := hy
    have hu1 : (u : G) ≠ 1 := by
      intro hh
      have hh' : u = 1 := K.subtype_injective (H.subtype_injective hh)
      exact hx1 (hh' ▸ map_one f)
    have hv1 : (v : G) ≠ 1 := by
      intro hh
      have hh' : v = 1 := K.subtype_injective (H.subtype_injective hh)
      exact hy1 (hh' ▸ map_one f)
    obtain ⟨l,hl,he⟩ := unitary_original_pushingUp_rudvalis_fusion s hcover hJH hc K hK e c hVW
      u hu v hv hu1 hv1
    let k : K := ⟨⟨l,hYH hl⟩,hYK hl⟩
    refine ⟨f k,mem_map_of_mem f (show k ∈ A from hl),?_⟩
    have he' : k*u*k⁻¹ = v := K.subtype_injective (H.subtype_injective he)
    simpa only [map_mul,map_inv] using congrArg f he'
  have hcore := Rudvalis.transitive_sixtyFour_overgroup_core B E C hEB hBC hCE hE hB hBE ht
  refine ⟨hNC',hcore,le_antisymm ?_ ?_⟩
  · intro x hx
    have hcX : (⟨x,hx.1⟩ : C) ∈ centralizer (pCore 2 C : Set C) := by
      intro y hy
      exact Subtype.ext (hx.2 y (hcore ▸ mem_map_of_mem C.subtype hy))
    exact hcore ▸ mem_map_of_mem C.subtype (hchar' hcX)
  · exact le_inf (hEB.trans hBC) (le_centralizer_iff_isMulCommutative.mpr instE.toIsMulCommutative)
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion

namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual escaping odd-actor pair, with the full local normalizer and
its module kernel identified in the same Rudvalis marking. -/
theorem unitary_original_oddActorResidual_component_normalizers (s : Context T L V)
    (A : Subgroup G) (hAN : A ≤ normalizer (L : Set G))
    (hcomm : ⁅A,L⁆ ≤ L.pCoreIn 2) (hodd : Odd (Nat.card A))
    (hAV : A ≤ centralizer (V : Set G))
    (hnot : ¬ UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G))) :
    ∃ (J H : Subgroup G)
      (S : Sylow 2 (sectionCentralizerIn (normalizer (L : Set G)) L))
      (c : sectionCentralizerIn (normalizer (L : Set G)) L),
      PushLE L (oddActorResidual L A) J ∧ IsMaximalTwoLocal H ∧ J ≤ H ∧
      H ⊓ normalizer (L : Set G) < H ∧
      let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
      let W := fullModule L ((S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
        (sectionCentralizerIn (normalizer (L : Set G)) L).subtype)
      ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H (H ⊓ normalizer (L : Set G))
        Y (J.pCoreIn 2) W ∧
      ((L ⊔ (T : Subgroup G)).pCoreIn 2).map (MulAut.conj (c : G)).toMonoidHom =
        (S : Subgroup (sectionCentralizerIn (normalizer (L : Set G)) L)).map
          (sectionCentralizerIn (normalizer (L : Set G)) L).subtype ∧
      V.map (MulAut.conj (c : G)).toMonoidHom ≤ W ∧
      ∃ K : Subgroup H, IsComponent H K ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        (Nonempty (K ⧸ center K ≃* Janko4.Model) ∨
          ∃ e : K ⧸ center K ≃* Rudvalis.Model,
            W = V.map (MulAut.conj (c : G)).toMonoidHom ∧
            let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
            let B := ((Y.subgroupOf H).subgroupOf K).map f
            let E := ((W.subgroupOf H).subgroupOf K).map f
            let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
            normalizer (B : Set Rudvalis.Model) = C ∧
              C.pCoreIn 2 = E ∧ C ⊓ centralizer (E : Set Rudvalis.Model) = E) := by
  obtain ⟨J,H,S,hpush,hH,hJH,hlt,hc,_,_,⟨K,hK,hout,n,hn,⟨e⟩⟩,c,hcS,hcV⟩ :=
    unitary_original_oddActorResidual_escaping_component s A hAN hcomm hodd hAV hnot
  refine ⟨J,H,S,c,hpush,hH,hJH,hlt,hc,hcS,hcV,K,hK,hout,?_⟩
  rcases hn with rfl | rfl
  · exact Or.inl ⟨e⟩
  · apply Or.inr
    have hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G) := by
      have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
      obtain ⟨hcover,_,_,_⟩ := chosen_oddActorResidual_cover h12.toHypothesis1221 s.chosen
        A hAN hcomm hodd hAV
      have hi : oddActorResidual L A ≤ J :=
        ((le_inf le_rfl ((oddActorResidual_le L A).trans inf_le_left)).trans hpush.2).trans
          inf_le_left
      exact hcover.subset.trans (Set.mul_subset_mul hi Set.Subset.rfl)
    exact ⟨e,unitary_original_pushingUp_rudvalis_full_module s hcover hJH hc K hK e c hcV,
      unitary_original_pushingUp_rudvalis_normalizer s hcover hJH hc K hK e c hcV⟩
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
