module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.MarkedAction
/-!
# The original full natural module in the Rudvalis component

The chosen natural module fills the full source module modulo the component
center. Its conjugate is normalized by the intersection residual. Central
factors contribute nothing to commutators, so full movement identifies the
whole source module with this conjugated chosen module before quotienting.

The final theorem applies the equality to the actual escaping component
constructed when odd-residual uniqueness fails. It retains the same relative
Sylow, conjugating element, residual quotient formula and C.2.8 datum. Its
alternatives are an actual J₄ central quotient or an actual Rudvalis central
quotient with the full marked natural module. No general MS classifier,
Rudvalis block recognition or centralizer escape is an assumption.

J₄ exclusion, Rudvalis flag-centralizer escape and the remaining odd-normalizer
argument stay with qt-d-13316-source. The earlier Structural1222 premise has
its final source discharge at qt-theorem-d.
Source: Aschbacher–Smith C.3.1,4.2.12–13,4.4.6, pp.149–151,610–612,620.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open scoped Pointwise IsMulCommutative commutatorElement
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem full_moved_eq_of_same_central_image {F : Type*} [Group F]
    (U W A : Subgroup F) (hUW : U ≤ W) (hAU : A ≤ normalizer (U : Set F))
    (hm : W = ⁅W,A⁆)
    (he : U.map (QuotientGroup.mk' (center F)) =
      W.map (QuotientGroup.mk' (center F))) : U = W := by
  have hW : W ≤ U ⊔ center F := by
    have h := congrArg (comap (QuotientGroup.mk' (center F))) he
    rw [comap_map_eq,comap_map_eq,QuotientGroup.ker_mk'] at h
    exact le_sup_left.trans h.symm.le
  apply le_antisymm hUW
  rw [hm]
  apply (commutator_mono hW le_rfl).trans
  apply commutator_le.mpr
  intro w hw a ha
  obtain ⟨u,hu,z,hz,rfl⟩ := mem_sup_of_normal_right.mp hw
  have hzcomm : ⁅z,a⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    ((mem_center_iff.mp hz a).symm)
  have hucomm := (le_normalizer_iff_commutator_le_left.mp hAU)
    (commutator_mem_commutator hu ha)
  simpa only [commutatorElement_mul_left_eq_conj_mul,hzcomm,mul_one,mul_inv_cancel,
    one_mul] using hucomm

/-- The full Rudvalis source module itself equals the conjugated chosen natural module. -/
theorem unitary_original_pushingUp_rudvalis_full_module (s : Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Rudvalis.Model)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) :
    W = V.map (MulAut.conj (c : G)).toMonoidHom := by
  let U := V.map (MulAut.conj (c : G)).toMonoidHom
  let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let U' := (U.subgroupOf H).subgroupOf K
  let W' := (W.subgroupOf H).subgroupOf K
  let A := (Y.subgroupOf H).subgroupOf K
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have hM := h12.source_normalizer_maximal_unique s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer s.chosen.sylow_normalizes_component,hM.2⟩
  obtain ⟨hn,_,_⟩ := source_intersection_quotient h12.toHypothesis1221 hu hcover hJH
  have hspan : conjugateSpanBy Y (H ⊓ normalizer (L : Set G)) = Y :=
    hc.normalized_span_eq ((normal_subgroupOf_iff_le_normalizer hc.component_le).mp hn)
  have hWY : W ≤ Y := hc.module_le.trans hspan.le
  have hYH : Y ≤ H := hc.component_le.trans hc.local_le
  have hWH : W ≤ H := hWY.trans hYH
  have hYK : Y.subgroupOf H ≤ K := hc.ordinary_component_contains_original K hK
  have hWK : W.subgroupOf H ≤ K := (subgroupOf_mono H hWY).trans hYK
  have hUH : U ≤ H := hVW.trans hWH
  have hUK : U.subgroupOf H ≤ K := (subgroupOf_mono H hVW).trans hWK
  have hLc : L.map (MulAut.conj (c : G)).toMonoidHom = L :=
    mem_normalizer_iff_map_conj_eq.mp c.property.1
  have hLU : L ≤ normalizer (U : Set G) := by
    have ht := (map_mono (f := (MulAut.conj (c : G)).toMonoidHom) s.chosen.normalizes).trans
      (V.le_normalizer_map (MulAut.conj (c : G)).toMonoidHom)
    rwa [hLc] at ht
  have hAU : A ≤ normalizer (U' : Set K) := by
    intro a ha
    apply mem_normalizer_iff.mpr
    intro u
    exact mem_normalizer_iff.mp
      (hLU (((map_subtype_le _).trans inf_le_left) ha)) (u : G)
  have hm : W' = ⁅W',A⁆ := by
    apply map_injective K.subtype_injective
    apply map_injective H.subtype_injective
    rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hWK,
      map_subgroupOf_eq_of_le hYK,map_subgroupOf_eq_of_le hWH,
      map_subgroupOf_eq_of_le hYH]
    exact hc.module_commutator.trans (congrArg (fun X => ⁅W,X⁆) hspan)
  have he := full_moved_eq_of_same_central_image U' W' A
    (subgroupOf_mono K (subgroupOf_mono H hVW)) hAU hm
    (unitary_original_pushingUp_rudvalis_module_image s hcover hJH hc K hK e c hVW)
  have ht := congrArg (fun P : Subgroup K => (P.map K.subtype).map H.subtype) he
  rw [map_subgroupOf_eq_of_le hUK,map_subgroupOf_eq_of_le hWK,
    map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hWH] at ht
  exact ht.symm

/-- Failure of uniqueness gives the original pair; in its Rudvalis branch
its entire source module is the marked chosen natural module. -/
theorem unitary_original_oddActorResidual_marked_component (s : Context T L V)
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
          Nonempty (K ⧸ center K ≃* Rudvalis.Model) ∧
            W = V.map (MulAut.conj (c : G)).toMonoidHom) := by
  obtain ⟨J,H,S,hpush,hH,hJH,hlt,hc,hn,ha,⟨K,hK,hout,n,hnn,⟨e⟩⟩,c,hcS,hcV⟩ :=
    unitary_original_oddActorResidual_escaping_component s A hAN hcomm hodd hAV hnot
  refine ⟨J,H,S,c,hpush,hH,hJH,hlt,hc,hn,ha,hcS,hcV,K,hK,hout,?_⟩
  rcases hnn with rfl | rfl
  · exact Or.inl ⟨e⟩
  · refine Or.inr ⟨⟨e⟩,?_⟩
    have hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G) := by
      have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
      obtain ⟨hcover,_,_,_⟩ := chosen_oddActorResidual_cover h12.toHypothesis1221 s.chosen
        A hAN hcomm hodd hAV
      have hi : oddActorResidual L A ≤ J :=
        ((le_inf le_rfl ((oddActorResidual_le L A).trans inf_le_left)).trans hpush.2).trans
          inf_le_left
      exact hcover.subset.trans (Set.mul_subset_mul hi Set.Subset.rfl)
    exact unitary_original_pushingUp_rudvalis_full_module s hcover hJH hc K hK e c hcV

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
