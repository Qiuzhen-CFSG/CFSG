module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.ComponentEscape
public import CFSG.Quasithin.Chapter4.Section02.Unitary.RudvalisModule
/-!
# The marked unitary module in the actual escaping component

The original conjugated chosen module still has zero component fixed points,
and O₂(L) centralizes it. The intersection residual covers L/O₂(L), so the
chosen module meets the component center trivially. Its literal image has
order 64. In the Rudvalis row the full module image also has order 64, and
therefore equals this marked chosen-module image.

The full module action has kernel exactly the image residual's two-core;
its faithful image retains the original quotient formula. These statements
supply the actual module and action for the remaining Rudvalis flag
calculation. They do not assert residual uniqueness or odd-normalizer control;
those remain with qt-d-13316-source. Structural1222 retains its final
source discharge at qt-theorem-d.
Source: Aschbacher–Smith C.3.1,4.2.12–13,4.4.6, pp.149–151,610–612,620.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual section-centralizer conjugation preserves the required fixed-point data. -/
theorem unitary_original_conjugate_fixed_points (s : Context T L V)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L) :
    V.map (MulAut.conj (c : G)).toMonoidHom ⊓ centralizer (L : Set G) = ⊥ ∧
      L.pCoreIn 2 ≤ centralizer (V.map (MulAut.conj (c : G)).toMonoidHom : Set G) := by
  let f := MulAut.conj (c : G)
  have hLc : L.map f.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp c.property.1
  have hf := congrArg (map f.toMonoidHom)
    (unitary_component_fixed_points_eq_bot L s.actor s.coordinates s.equivariant)
  rw [map_inf _ _ _ f.injective,map_centralizer_equiv,Subgroup.map_bot] at hf
  change V.map f.toMonoidHom ⊓ centralizer (L.map f.toMonoidHom : Set G) = ⊥ at hf
  rw [hLc] at hf
  have hQc : (L.pCoreIn 2).map f.toMonoidHom = L.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L) c.property.1)
  have hcore : L.pCoreIn 2 ≤ centralizer (V : Set G) :=
    (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le L.le_normalizer s.chosen.sylow_normalizes_component)).trans s.chosen.core_centralizes
  have hmap := (map_mono (f := f.toMonoidHom) hcore).trans
    (map_centralizer_le_centralizer_image _ _)
  rw [hQc] at hmap
  exact ⟨hf,hmap⟩

/-- The original natural module survives the selected component's central quotient. -/
theorem unitary_original_pushingUp_chosen_injective (s : Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) :
    let U := V.map (MulAut.conj (c : G)).toMonoidHom
    let P := (U.subgroupOf H).subgroupOf K
    Function.Injective ((QuotientGroup.mk' (center K)).comp P.subtype) ∧
      Nat.card (P.map (QuotientGroup.mk' (center K))) = 64 := by
  let U := V.map (MulAut.conj (c : G)).toMonoidHom
  let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let P := (U.subgroupOf H).subgroupOf K
  let q := QuotientGroup.mk' (center K)
  let f : P →* K ⧸ center K := q.comp P.subtype
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have hM := h12.source_normalizer_maximal_unique s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer s.chosen.sylow_normalizes_component,hM.2⟩
  have hyp := source_hypothesis411 h12.toHypothesis1221 hu
  obtain ⟨hYC,_,hn⟩ := residual_cover_of_containment hyp.plus_le hyp.plus_normal
    hyp.plus_perfect hcover hJH
  rw [chosen_intersection_twoResidual_eq_solvableResidual h12.toHypothesis1221 hcover hJH] at hYC hn
  have hspan : conjugateSpanBy Y (H ⊓ normalizer (L : Set G)) = Y :=
    hc.normalized_span_eq ((normal_subgroupOf_iff_le_normalizer hc.component_le).mp hn)
  have hWY : W ≤ Y := hc.module_le.trans hspan.le
  have hUY : U ≤ Y := hVW.trans hWY
  have hYH : Y ≤ H := hc.component_le.trans hc.local_le
  have hUH : U ≤ H := hUY.trans hYH
  have hYK := hc.ordinary_component_contains_original K hK
  have hUK : U.subgroupOf H ≤ K := (subgroupOf_mono H hUY).trans hYK
  obtain ⟨hfixed,hcore⟩ := unitary_original_conjugate_fixed_points s c
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxZ : (x : K) ∈ center K := (QuotientGroup.eq_one_iff _).mp hx
    have hxY : (x : G) ∈ centralizer (Y : Set G) := by
      intro y hy
      exact congrArg (fun k : K => (k : G))
        (mem_center_iff.mp hxZ ⟨⟨y,hYH hy⟩,hYK hy⟩)
    have hxL : (x : G) ∈ centralizer (L : Set G) := by
      intro l hl
      obtain ⟨y,hy,r,hr,rfl⟩ := hYC ▸ hl
      have hyr := hxY y hy
      have hrr := (hcore hr (x : G) x.property).symm
      calc
        y * r * (x : G) = y * ((x : G) * r) := by rw [mul_assoc,hrr]
        _ = (x : G) * (y * r) := by rw [←mul_assoc,hyr,mul_assoc]
    have hxone : (x : G) = 1 := mem_bot.mp (hfixed ▸ ⟨x.property,hxL⟩)
    exact Subtype.ext (Subtype.ext (Subtype.ext hxone))
  have hP : Nat.card P = 64 := by
    rw [Nat.card_congr ((subgroupOfEquivOfLe hUK).trans (subgroupOfEquivOfLe hUH)).toEquiv,
      card_map_of_injective (MulAut.conj (c : G)).injective]
    have hd : Module.finrank (ZMod 2) (Additive V) = 6 :=
      s.coordinates.finrank_eq.trans (Atlas.G2.Natural.finrank_space (ZMod 2))
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod,hd] at he
    exact he
  refine ⟨hf,?_⟩
  have hs : Function.Surjective (q.subgroupMap P) := q.subgroupMap_surjective P
  have hi : Function.Injective (q.subgroupMap P) := fun x y hxy =>
    hf (congrArg Subtype.val hxy)
  exact (Nat.card_congr (Equiv.ofBijective (q.subgroupMap P) ⟨hi,hs⟩)).symm.trans hP

/-- The actual odd-actor pair inherits the faithful action and original quotient marking. -/
theorem unitary_original_pushingUp_faithful_module_action (s : Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) :
    let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let A := (Y.subgroupOf H).subgroupOf K
    let q := QuotientGroup.mk' (center K)
    let B := A.map q
    let E := ((W.subgroupOf H).subgroupOf K).map q
    ∃ hBE : B ≤ normalizer (E : Set (K ⧸ center K)),
      let ρ := E.normalizerMonoidHom.comp (inclusion hBE)
      ρ.ker = pCore 2 B ∧
      ∃ b : ρ.range ≃* Atlas.G2.Natural.BinaryNormalizer.Derived,
        ∀ x : A, b (ρ.rangeRestrict (q.subgroupMap A x)) =
          s.quotient (QuotientGroup.mk' (pCore 2 L)
            ⟨x.val.val.val,((map_subtype_le _).trans inf_le_left) x.property⟩) := by
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have hM := h12.source_normalizer_maximal_unique s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer s.chosen.sylow_normalizes_component,hM.2⟩
  obtain ⟨hn,a,ha⟩ := source_intersection_quotient h12.toHypothesis1221 hu hcover hJH
  obtain ⟨hBE,hker,b,hb⟩ := hc.unitary_ordinary_faithful_module_action hn
    (a.trans s.quotient) K hK
  refine ⟨hBE,hker,b,?_⟩
  intro x
  rw [hb]
  exact congrArg s.quotient (ha ⟨x.val.val.val,x.property⟩)

/-- In the Rudvalis row the original chosen module fills the full source module image. -/
theorem unitary_original_pushingUp_rudvalis_module_image (s : Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Rudvalis.Model)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W) :
    let q := QuotientGroup.mk' (center K)
    let U := V.map (MulAut.conj (c : G)).toMonoidHom
    ((U.subgroupOf H).subgroupOf K).map q = ((W.subgroupOf H).subgroupOf K).map q := by
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have hM := h12.source_normalizer_maximal_unique s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer s.chosen.sylow_normalizes_component,hM.2⟩
  obtain ⟨_,a,_⟩ := source_intersection_quotient h12.toHypothesis1221 hu hcover hJH
  have hW := hc.unitary_ordinary_rudvalis_module_card (a.trans s.quotient) K hK e
  have hU := (unitary_original_pushingUp_chosen_injective s hcover hJH hc K hK c hVW).2
  exact eq_of_le_of_card_ge (map_mono (subgroupOf_mono K (subgroupOf_mono H hVW)))
    (by rw [hW,hU])

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
