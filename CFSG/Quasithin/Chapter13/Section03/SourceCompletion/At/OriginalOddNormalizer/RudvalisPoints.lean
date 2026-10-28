module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisPoints
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSourceAt
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.At
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalOddNormalizer.RudvalisFusion


/-!
# Original unitary source argument at the same ambient group and Sylow subgroup

This is the ambient-local specialization of `OriginalOddNormalizer.RudvalisPoints`.
Its proof retains the original subgroups, actions, relative Sylow placement,
and quotient maps. Only the earlier 12.2.2 and 12.2.13 inputs are restricted
to the fixed G,T. The universal public API remains in the imported module.
The source argument and reference are recorded there; no additional local
classification or normalizer premise is introduced by this specialization.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Every nonidentity vector in the original module image is a central-class
involution in the same Rudvalis quotient marking. -/
theorem unitary_original_pushingUp_rudvalis_module_and_points (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
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
    B.pCoreIn 2 = E ∧ Nat.card B = 64 * 6048 ∧
    ∀ z : E, z ≠ 1 →
      Nat.card ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf B) = 6144 ∧
      IsConj (z : Rudvalis.Model) (Rudvalis.b ^ 2) ∧
      Nat.card (Rudvalis.InvolutionCentralizers.Centralizer (z : Rudvalis.Model)) = 245760 ∧
      Nat.card (pCore 2 (Rudvalis.InvolutionCentralizers.Centralizer (z : Rudvalis.Model))) = 2048 ∧
      Nonempty ((Rudvalis.InvolutionCentralizers.Centralizer (z : Rudvalis.Model) ⧸
        pCore 2 (Rudvalis.InvolutionCentralizers.Centralizer (z : Rudvalis.Model))) ≃*
          Equiv.Perm (Fin 5)) ∧
      ∃ P : Sylow 2 Rudvalis.Model, (center P).map (P : Subgroup Rudvalis.Model).subtype =
        zpowers (z : Rudvalis.Model) := by
  let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let q := QuotientGroup.mk' (center K)
  let f := e.toMonoidHom.comp q
  let A := (Y.subgroupOf H).subgroupOf K
  let U := (W.subgroupOf H).subgroupOf K
  let B := A.map f
  let E := U.map f
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have hM := h12.source_normalizer_maximal_unique_at s.structural
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
  have hWH : W ≤ H := hWY.trans hYH
  have hWK : W.subgroupOf H ≤ K := (subgroupOf_mono H hWY).trans hYK
  obtain ⟨_,hel,hBE,_,_,hB⟩ := hc.unitary_ordinary_module_image (a.trans s.quotient) K hK
  rw [hspan] at hBE hB
  let : IsElementaryAbelian 2 (U.map q) := hel
  let : IsElementaryAbelian 2 E := by
    let dE : (U.map q).map e.toMonoidHom ≃* E :=
      MulEquiv.subgroupCongr (map_map _ _ _)
    let : IsElementaryAbelian 2 ((U.map q).map e.toMonoidHom) :=
      IsElementaryAbelian.map e.toMonoidHom
    exact IsElementaryAbelian.of_surjective dE.toMonoidHom dE.surjective
  have hBE' : B ≤ normalizer (E : Set Rudvalis.Model) := by
    dsimp only [B,E,f]
    rw [←map_map,←map_map]
    exact (map_mono hBE).trans ((U.map q).le_normalizer_map e.toMonoidHom)
  have hE : Nat.card E = 64 := by
    dsimp only [E,f]
    rw [←map_map,card_map_of_injective e.injective]
    exact hc.unitary_ordinary_rudvalis_module_card (a.trans s.quotient) K hK e
  have hB' : 6048 ∣ Nat.card B := by
    dsimp only [B,f]
    rw [←map_map,card_map_of_injective e.injective]
    exact hB
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
  obtain ⟨b,_⟩ := hc.unitary_ordinary_seed_quotient (a.trans s.quotient) K hK
  let d : A.map q ≃* B := (e.subgroupMap (A.map q)).trans
    (MulEquiv.subgroupCongr (map_map _ _ _))
  let b' : B ⧸ pCore 2 B ≃* Atlas.G2.Natural.BinaryNormalizer.Derived :=
    (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).symm.trans b
  have hEB : E ≤ B := map_mono (subgroupOf_mono K (subgroupOf_mono H hWY))
  have hcore := hc.ordinary_module_image_core_centralizes K hK
  rw [hspan] at hcore
  have hcore' : B.pCoreIn 2 ≤ centralizer (E : Set Rudvalis.Model) := by
    have hk : IsPGroup 2 e.toMonoidHom.ker := by
      rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).mpr e.injective]
      exact IsPGroup.of_subsingleton 2 _
    have hh : ((A.map q).pCoreIn 2).map e.toMonoidHom ≤
        centralizer (((U.map q).map e.toMonoidHom) : Set Rudvalis.Model) :=
      (map_mono (f := e.toMonoidHom) hcore).trans
      (map_centralizer_le_centralizer_image _ _)
    rw [map_pCoreIn_of_ker_isPGroup e.toMonoidHom hk,map_map,map_map] at hh
    exact hh
  obtain ⟨hcoreEq,hBcard⟩ := Rudvalis.transitive_sixtyFour_twoCore B E hEB hBE' hE b' hcore' ht
  refine ⟨hcoreEq,hBcard,fun z hz => ⟨?_,
    Rudvalis.transitive_sixtyFour_involution_class B E hBE' hE hB' ht z hz⟩⟩
  have hh := Theory.GroupAction.centralizer_card_mul_pred_of_transitive B E hBE' ht z hz
  rw [hE,hBcard] at hh
  change Nat.card ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf B) = 6144
  change Nat.card ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf B) * 63 = 387072 at hh
  omega
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At


namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
open CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open scoped Pointwise IsMulCommutative commutatorElement
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- In the actual escaping component, the same quotient marking supplies the
full module, its two-core identity, and every original point centralizer. -/
theorem unitary_original_oddActorResidual_component_points (s : _root_.CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At.OriginalPlaneCentralizers.Context T L V)
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
      (Y.subgroupOf (H ⊓ normalizer (L : Set G))).Normal ∧
      (∃ a : (Y ⧸ pCore 2 Y) ≃* Atlas.G2.Natural.BinaryNormalizer.Derived,
        ∀ y : Y, a (QuotientGroup.mk' (pCore 2 Y) y) =
          s.quotient (QuotientGroup.mk' (pCore 2 L)
            ⟨y.val,((map_subtype_le _).trans inf_le_left) y.property⟩)) ∧
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
            B.pCoreIn 2 = E ∧ Nat.card B = 64 * 6048 ∧
            ∀ z : E, z ≠ 1 →
              Nat.card ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf B) = 6144 ∧
              IsConj (z : Rudvalis.Model) (Rudvalis.b ^ 2) ∧
              Nat.card (Rudvalis.InvolutionCentralizers.Centralizer (z : Rudvalis.Model)) = 245760 ∧
              Nat.card (pCore 2 (Rudvalis.InvolutionCentralizers.Centralizer (z : Rudvalis.Model))) = 2048 ∧
              Nonempty ((Rudvalis.InvolutionCentralizers.Centralizer (z : Rudvalis.Model) ⧸
                pCore 2 (Rudvalis.InvolutionCentralizers.Centralizer (z : Rudvalis.Model))) ≃*
                  Equiv.Perm (Fin 5)) ∧
              ∃ P : Sylow 2 Rudvalis.Model,
                (center P).map (P : Subgroup Rudvalis.Model).subtype = zpowers (z : Rudvalis.Model)) := by
  obtain ⟨J,H,S,hpush,hH,hJH,hlt,hc,hn,ha,⟨K,hK,hout,n,hnn,⟨e⟩⟩,c,hcS,hcV⟩ :=
    unitary_original_oddActorResidual_escaping_component s A hAN hcomm hodd hAV hnot
  refine ⟨J,H,S,c,hpush,hH,hJH,hlt,hc,hn,ha,hcS,hcV,K,hK,hout,?_⟩
  rcases hnn with rfl | rfl
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
      unitary_original_pushingUp_rudvalis_module_and_points s hcover hJH hc K hK e c hcV⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.At
