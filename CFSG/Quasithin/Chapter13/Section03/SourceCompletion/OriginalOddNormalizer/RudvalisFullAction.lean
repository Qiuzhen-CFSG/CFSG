module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisRadicalLift

/-!
# The full natural action of the original Rudvalis normalizer

Faithfulness of the central quotient on the source module identifies its
conjugation action with an action on the original chosen six-space. The
radical normalizer lift makes every actor an original ambient automizer.
The natural G₂ normalizer theorem embeds this action in G₂(2); the checked
normalizer and kernel orders make that embedding surjective.

Both the quotient marking and section-centralizer conjugation are retained
in the equivariance and module-identification equations. This supplies the
full actor needed to construct the original point-parabolic quotient.
The flag/quaternion intersection, J₄ exclusion and odd-normalizer conclusion
remain with qt-d-13316-source. Structural1222 retains its final discharge
with qt-theorem-d.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open Atlas.G2.Natural.BinaryNormalizer
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The literal quotient normalizer acts as the full natural G₂(2), with
its E₆₄ kernel and the original section-conjugation coordinates. -/
theorem unitary_original_pushingUp_rudvalis_full_action (s : Context T L V)
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
    let U := (W.subgroupOf H).subgroupOf K
    let E := U.map f
    let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
    ∃ (hCE : C ≤ normalizer (E : Set Rudvalis.Model)) (a : C →* Full) (d : E ≃* V),
      Function.Surjective a ∧ a.ker = E.subgroupOf C ∧
      (∀ u : U, (d (f.subgroupMap U u) : G) = (MulAut.conj (c : G)).symm (u : G)) ∧
      ∀ (x : C) (v : E),
        s.coordinates (Additive.ofMul (d (E.normalizerMonoidHom (inclusion hCE x) v))) =
          Atlas.G2.Natural.action (ZMod 2) (a x) (s.coordinates (Additive.ofMul (d v))) := by
  let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let U := (W.subgroupOf H).subgroupOf K
  let E := U.map f
  let C0 := ((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K
  let C := C0.map f
  have hfull := unitary_original_pushingUp_rudvalis_full_module s hcover hJH hc K hK e c hVW
  have h12 := unitary_original_hypothesis1223 s.hypothesis s.maximal s.quotient
  have hM := h12.source_normalizer_maximal_unique s.structural
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
  have hu : UniqueMaximalOvergroup (L ⊔ (T : Subgroup G)) (normalizer (L : Set G)) :=
    ⟨hM.1,sup_le L.le_normalizer s.chosen.sylow_normalizes_component,hM.2⟩
  obtain ⟨hn,aY,_⟩ := source_intersection_quotient h12.toHypothesis1221 hu hcover hJH
  have hspan : conjugateSpanBy Y (H ⊓ normalizer (L : Set G)) = Y :=
    hc.normalized_span_eq ((normal_subgroupOf_iff_le_normalizer hc.component_le).mp hn)
  have hYH : Y ≤ H := hc.component_le.trans hc.local_le
  have hYK := hc.ordinary_component_contains_original K hK
  have hWY : W ≤ Y := hc.module_le.trans hspan.le
  have hWH := hWY.trans hYH
  have hWK := (subgroupOf_mono H hWY).trans hYK
  have hf : Function.Injective (f.comp U.subtype) := by
    have hi := (unitary_original_pushingUp_chosen_injective s hcover hJH hc K hK c hVW).1
    rw [←hfull] at hi
    exact e.injective.comp hi
  let q : U ≃* E := MulEquiv.ofBijective (f.subgroupMap U)
    ⟨fun x y h => hf (congrArg Subtype.val h), f.subgroupMap_surjective U⟩
  let g := MulAut.conj (c : G)
  let dU : U ≃* V := ((subgroupOfEquivOfLe hWK).trans (subgroupOfEquivOfLe hWH)).trans
    ((MulEquiv.subgroupCongr hfull).trans (g.subgroupMap V).symm)
  let d : E ≃* V := q.symm.trans dU
  have hd (u : U) : (d (f.subgroupMap U u) : G) = g.symm (u : G) := by
    change (dU (q.symm (q u)) : G) = _
    rw [q.symm_apply_apply]
    rfl
  obtain ⟨hNC,hCcard,_⟩ := unitary_original_pushingUp_rudvalis_exact_sizes
    s hcover hJH hc K hK e c hVW
  change normalizer (E : Set Rudvalis.Model) = C at hNC
  change Nat.card C = 64 * 12096 at hCcard
  have hCE : C ≤ normalizer (E : Set Rudvalis.Model) := hNC.ge
  have hCU : C0 ≤ normalizer (U : Set K) :=
    (unitary_original_pushingUp_rudvalis_normalizer_lift s hcover hJH hc K hK e c hVW).1.ge
  let α : C →* MulAut E := E.normalizerMonoidHom.comp (inclusion hCE)
  let β : C →* MulAut V := (MulAut.congr d).toMonoidHom.comp α
  have hβ (x : C) : β x ∈ V.normalizerMonoidHom.range := by
    obtain ⟨k,hk,hkx⟩ := x.property
    let n : G := g.symm (k : G)
    have hnW : (k : G) ∈ normalizer (W : Set G) := by
      have hh := U.le_normalizer_map (H.subtype.comp K.subtype)
        (mem_map_of_mem (H.subtype.comp K.subtype) (hCU hk))
      have hmap : U.map (H.subtype.comp K.subtype) = W := by
        rw [←map_map,map_subgroupOf_eq_of_le hWK,map_subgroupOf_eq_of_le hWH]
      rwa [hmap] at hh
    have hnV : n ∈ normalizer (V : Set G) := by
      rw [hfull,←map_equiv_normalizer_eq] at hnW
      obtain ⟨v,hv,hvEq⟩ := hnW
      have hvn : v = n := by
        exact (g.symm_apply_eq.mpr hvEq.symm).symm
      exact hvn ▸ hv
    refine ⟨⟨n,hnV⟩,?_⟩
    apply MulEquiv.ext
    intro v
    obtain ⟨u,rfl⟩ := dU.surjective v
    apply Subtype.ext
    have hconj : α x (q u) = q (U.normalizerMonoidHom ⟨k,hCU hk⟩ u) := by
      apply Subtype.ext
      change (x : Rudvalis.Model)*f u*(x : Rudvalis.Model)⁻¹ = f (k*u*k⁻¹)
      simp only [map_mul,map_inv,hkx]
    change n*(dU u : G)*n⁻¹ = (d (α x (d.symm (dU u))) : G)
    have hdu : d.symm (dU u) = q u := by
      apply d.injective
      simp only [d,dU,MulEquiv.trans_apply,MulEquiv.apply_symm_apply,
        MulEquiv.symm_apply_apply]
    rw [hdu,hconj]
    change n*(dU u : G)*n⁻¹ = (dU (q.symm (q (U.normalizerMonoidHom ⟨k,hCU hk⟩ u))) : G)
    rw [q.symm_apply_apply]
    change g.symm (k : G)*g.symm (u : G)*(g.symm (k : G))⁻¹ =
      g.symm ((k : G)*(u : G)*(k : G)⁻¹)
    simp only [map_mul,map_inv]
  let b : C →* Automizer V := β.codRestrict _ hβ
  let I := inducedAutomizer V L
  obtain ⟨_,hNL⟩ := unitary_original_module_normalizers s.hypothesis s.maximal
    s.quotient s.chosen s.structural
  let : (L.subgroupOf (normalizer (V : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer s.chosen.normalizes).mpr hNL
  let : I.Normal := Subgroup.Normal.map inferInstance V.normalizerMonoidHom.rangeRestrict
    V.normalizerMonoidHom.rangeRestrict_surjective
  obtain ⟨j,hj,_,heq⟩ := ambient_embedding (automizerRepresentation V) I s.actor
    s.coordinates s.equivariant (automizerRepresentation_injective V)
  let a : C →* Full := j.comp b
  have hcent := (unitary_original_pushingUp_rudvalis_normalizer
    s hcover hJH hc K hK e c hVW).2.2
  change C ⊓ centralizer (E : Set Rudvalis.Model) = E at hcent
  have hker : a.ker = E.subgroupOf C := by
    ext x
    change j (b x) = 1 ↔ (x : Rudvalis.Model) ∈ E
    rw [←map_one j,hj.eq_iff]
    have hb : b x = 1 ↔ α x = 1 := by
      constructor
      · intro hx
        apply (MulAut.congr d).injective
        exact (congrArg Subtype.val hx).trans (map_one (MulAut.congr d)).symm
      · intro hx
        apply Subtype.ext
        change (MulAut.congr d) (α x) = 1
        rw [hx,map_one]
    rw [hb]
    change inclusion hCE x ∈ E.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    change (x : Rudvalis.Model) ∈ centralizer (E : Set Rudvalis.Model) ↔ _
    exact ⟨fun hx => hcent ▸ ⟨x.property,hx⟩,
      fun hx => (show (x : Rudvalis.Model) ∈ C ⊓ centralizer (E : Set Rudvalis.Model)
        from hcent.symm ▸ hx).2⟩
  have hEC : E ≤ C := hcent.ge.trans inf_le_left
  have hE : Nat.card E = 64 := by
    rw [Nat.card_congr d.toEquiv]
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod,s.coordinates.finrank_eq,Atlas.G2.Natural.finrank_space] at hh
    exact hh
  have hsurj : Function.Surjective a := by
    apply MonoidHom.surjective_of_card_ker_le_div
    rw [hker,Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv,hE,hCcard,
      Atlas.G2.OrderChecks.binary_order]
  refine ⟨hCE,a,d,hsurj,hker,hd,?_⟩
  intro x v
  have hh := heq (b x) (Additive.ofMul (d v))
  calc
    _ = s.coordinates (automizerRepresentation V (b x) (Additive.ofMul (d v))) := by
      change s.coordinates (Additive.ofMul (d (α x v))) =
        s.coordinates (Additive.ofMul (d (α x (d.symm (d v)))))
      rw [d.symm_apply_apply]
    _ = _ := hh

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
