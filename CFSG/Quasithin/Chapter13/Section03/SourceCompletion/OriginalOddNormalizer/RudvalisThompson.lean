module

public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalOddNormalizer.RudvalisNormalizerOrder
public import Theory.Representation.G2BinaryImageThompson
public import Theory.GroupTheory.ElementaryThompsonElementaryCore
public import Theory.GroupTheory.ThompsonNormalizerGrowth

/-!
# Thompson subgroups and normalizer growth in the original Rudvalis row

Transport the original natural coordinates through section conjugation and
the literal component quotient. The derived G₂ action has no offenders,
so the elementary Thompson subgroup of every residual subgroup containing
the module equals that module. The ambient Rudvalis Sylow order then forces
strict growth of the module normalizer. When the component is centerless,
C.2.8 lifts module normalization to the original local subgroup, and the
previous two possible orders reduce to 774144, with point stabilizers 12288.

The final theorem applies all these facts to the original escaping odd-actor
pair with the same relative Sylow, entire module and quotient marking.
Centerlessness is explicit only for the exact-order conclusion. Its discharge
or a direct central-kernel lift, the flag/quaternion geometry, J₄ exclusion
and odd-normalizer control remain with qt-d-13316-source. The earlier
Structural1222 premise retains its final discharge with qt-theorem-d.
Source: Aschbacher--Smith B.4.6(13), C.1.37 and 4.2.13, pp.90,141,611--612.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup Theory.GroupTheory Chapter4 Chapter4.Section04 ChapterE Stellmacher
open Chapter4.Section02.Unitary OriginalPlaneCentralizers
open Atlas.G2.Natural.BinaryNormalizer
open scoped Pointwise IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- Every residual subgroup containing the full module has that module as
its elementary Thompson subgroup, through the literal central quotient. -/
theorem unitary_original_pushingUp_rudvalis_thompson (s : Context T L V)
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
    ∀ P : Subgroup B, E.subgroupOf B ≤ P → elementaryAbelianMaxJ P = E.subgroupOf B := by
  let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let A := (Y.subgroupOf H).subgroupOf K
  let U := (W.subgroupOf H).subgroupOf K
  let B := A.map f
  let E := U.map f
  change ∀ P : Subgroup B, E.subgroupOf B ≤ P → elementaryAbelianMaxJ P = E.subgroupOf B
  have hfull := unitary_original_pushingUp_rudvalis_full_module s hcover hJH hc K hK e c hVW
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
  have hYL : Y ≤ L := (map_subtype_le _).trans inf_le_left
  have hYH : Y ≤ H := hc.component_le.trans hc.local_le
  have hYK := hc.ordinary_component_contains_original K hK
  have hWH := hWY.trans hYH
  have hWK := (subgroupOf_mono H hWY).trans hYK
  have hYW : Y ≤ normalizer (W : Set G) := by
    rw [le_normalizer_iff_commutator_le_left]
    exact (hc.module_commutator.trans (congrArg (fun X => ⁅W,X⁆) hspan)).symm.le
  let W0 := W.subgroupOf Y
  let : W0.Normal := normal_subgroupOf_of_le_normalizer hYW
  let : IsElementaryAbelian 2 W := hc.module_elementary
  let : IsElementaryAbelian 2 W0 := IsElementaryAbelian.subgroupOf hWY
  let aY : A ≃* Y := (subgroupOfEquivOfLe hYK).trans (subgroupOfEquivOfLe hYH)
  let t : Y →* B := (f.subgroupMap A).comp aY.symm.toMonoidHom
  have ht : Function.Surjective t := (f.subgroupMap_surjective A).comp aY.symm.surjective
  have htker : t.ker ≤ center Y := by
    intro x hx
    have hfz : f (aY.symm x) = 1 := congrArg Subtype.val hx
    have hz : (aY.symm x : K) ∈ center K := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact e.injective (hfz.trans (map_one e).symm)
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact congrArg (fun k : K => (k : G)) (mem_center_iff.mp hz (aY.symm y : K))
  have hi : Function.Injective (t.comp W0.subtype) := by
    have hinj := (unitary_original_pushingUp_chosen_injective s hcover hJH hc K hK c hVW).1
    rw [←hfull] at hinj
    intro x y hxy
    have hxy' : f (aY.symm x.val) = f (aY.symm y.val) := congrArg Subtype.val hxy
    have heq : (⟨aY.symm x.val,x.property⟩ : U) = ⟨aY.symm y.val,y.property⟩ :=
      hinj (e.injective hxy')
    exact Subtype.ext (Subtype.ext (congrArg (fun u : U => (u : G)) heq))
  have hmap : W0.map t = E.subgroupOf B := by
    apply map_injective B.subtype_injective
    rw [map_subgroupOf_eq_of_le (map_mono (subgroupOf_mono K (subgroupOf_mono H hWY)))]
    ext z
    constructor
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨aY.symm x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      let y : Y := ⟨(x : G),hWY hx⟩
      exact ⟨t y,mem_map_of_mem t (show y ∈ W0 from hx),rfl⟩
  let g := MulAut.conj (c : G)
  have hLc : L.map g.toMonoidHom = L := mem_normalizer_iff_map_conj_eq.mp c.property.1
  have hLci : L.map g.symm.toMonoidHom = L := by
    have hh := congrArg (map g.symm.toMonoidHom) hLc
    have hid : g.symm.toMonoidHom.comp g.toMonoidHom = MonoidHom.id G := by
      ext x
      exact g.symm_apply_apply x
    simpa only [map_map,hid,Subgroup.map_id] using hh.symm
  let j : Y →* L := (g.symm.toMonoidHom.comp Y.subtype).codRestrict L
    (fun x => hLci ▸ mem_map_of_mem g.symm.toMonoidHom (hYL x.property))
  let jN : Y →* normalizer (V : Set G) := (inclusion s.chosen.normalizes).comp j
  let a : Y →* inducedAutomizer V L :=
    (V.normalizerMonoidHom.rangeRestrict.comp jN).codRestrict _
      (fun x => mem_map_of_mem V.normalizerMonoidHom.rangeRestrict (j x).property)
  let q : Y →* Full := Derived.subtype.comp (s.actor.toMonoidHom.comp a)
  let d : W0 ≃* V := (subgroupOfEquivOfLe hWY).trans
    ((MulEquiv.subgroupCongr hfull).trans (g.subgroupMap V).symm)
  let ed : Additive W0 ≃ₗ[ZMod 2] Additive V :=
    { d.toAdditive with map_smul' := ZMod.map_smul d.toAdditive }
  have he (x : Y) (v : W0) :
      (ed.trans s.coordinates) (Additive.ofMul (MulAut.conjNormal x v)) =
        Atlas.G2.Natural.action (ZMod 2) (q x)
          ((ed.trans s.coordinates) (Additive.ofMul v)) := by
    have hh := s.equivariant (a x) (ed (Additive.ofMul v))
    change s.coordinates (automizerRepresentation V (a x) (ed (Additive.ofMul v))) =
      Atlas.G2.Natural.action (ZMod 2) (q x) (s.coordinates (ed (Additive.ofMul v))) at hh
    change s.coordinates (ed (Additive.ofMul (MulAut.conjNormal x v))) =
      Atlas.G2.Natural.action (ZMod 2) (q x) (s.coordinates (ed (Additive.ofMul v)))
    rw [←hh]
    apply congrArg s.coordinates
    apply Additive.toMul.injective
    apply Subtype.ext
    change g.symm ((x : G) * (v : G) * (x : G)⁻¹) =
      g.symm (x : G) * g.symm (v : G) * (g.symm (x : G))⁻¹
    simp only [map_mul,map_inv]
  intro P hEP
  have hJ := image_thompson_centralizes W0 q (ed.trans s.coordinates) he
    (by rintro _ ⟨x,rfl⟩; exact (s.actor (a x)).property) t ht htker hi P (hmap.symm ▸ hEP)
  rw [hmap] at hJ
  have hcentral : centralizer (E.subgroupOf B : Set B) ≤ E.subgroupOf B := by
    obtain ⟨hNC,_,hcent⟩ := unitary_original_pushingUp_rudvalis_normalizer
      s hcover hJH hc K hK e c hVW
    let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
    change normalizer (B : Set Rudvalis.Model) = C at hNC
    change C ⊓ centralizer (E : Set Rudvalis.Model) = E at hcent
    have hBC : B ≤ C := hNC ▸ B.le_normalizer
    have hEB : E ≤ B := map_mono (subgroupOf_mono K (subgroupOf_mono H hWY))
    intro b hb
    apply hcent.le
    refine ⟨hBC b.property,?_⟩
    intro z hz
    exact congrArg B.subtype (hb ⟨z,hEB hz⟩ hz)
  let : IsElementaryAbelian 2 (E.subgroupOf B) := by
    rw [←hmap]
    exact IsElementaryAbelian.map _
  exact elementaryAbelianMaxJ_eq_of_elementary_overgroup P (E.subgroupOf B)
    (hJ.trans hcentral) hEP inferInstance
/-- The full module-image normalizer strictly contains the residual image.
This does not yet identify it with the original local intersection. -/
theorem unitary_original_pushingUp_rudvalis_module_normalizer_growth (s : Context T L V)
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
    B < normalizer (E : Set Rudvalis.Model) := by
  let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let B := ((Y.subgroupOf H).subgroupOf K).map f
  let E := ((W.subgroupOf H).subgroupOf K).map f
  obtain ⟨hcore,hcard,_⟩ := unitary_original_pushingUp_rudvalis_module_and_points
    s hcover hJH hc K hK e c hVW
  change B.pCoreIn 2 = E at hcore
  change Nat.card B = 64 * 6048 at hcard
  have hEB : E ≤ B := hcore ▸ pCoreIn_le 2 B
  have hBE : B ≤ normalizer (E : Set Rudvalis.Model) := by
    rw [←hcore]
    exact B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  obtain ⟨S⟩ := Sylow.nonempty (p := 2) (G := B)
  have hES : E.subgroupOf B ≤ (S : Subgroup B) := by
    have hh : E ≤ (S : Subgroup B).map B.subtype := hcore ▸ B.pCoreIn_le_sylow S
    intro x hx
    obtain ⟨y,hy,he⟩ := hh hx
    exact B.subtype_injective he ▸ hy
  have hJ := unitary_original_pushingUp_rudvalis_thompson
    s hcover hJH hc K hK e c hVW (S : Subgroup B) hES
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup B)).map B.subtype = E := by
    rw [hJ,map_subgroupOf_eq_of_le hEB]
  obtain ⟨P,hP⟩ := (S.isPGroup'.map B.subtype).exists_le_sylow
  have hproper : (S : Subgroup B).map B.subtype < (P : Subgroup Rudvalis.Model) := by
    apply lt_of_le_of_ne hP
    intro he
    have hd := card_dvd_of_le (map_subtype_le (S : Subgroup B))
    rw [he,Rudvalis.InvolutionCentralizers.sylow_card P,hcard] at hd
    norm_num at hd
  exact lt_normalizer_of_sylow_thompson B E hBE S hJmap P hproper

/-- For a centerless component, module normalization lifts to the original
module, and the source local normalizer and all point stabilizers have exact orders. -/
theorem unitary_original_pushingUp_rudvalis_centerless_sizes (s : Context T L V)
    {J H W : Subgroup G}
    (hcover : (L : Set G) ⊆ (J : Set G) * (L.pCoreIn 2 : Set G)) (hJH : J ≤ H)
    (hc : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H
      (H ⊓ normalizer (L : Set G))
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype)
      (J.pCoreIn 2) W)
    (K : Subgroup H) (hK : IsComponent H K) (e : K ⧸ center K ≃* Rudvalis.Model)
    (c : sectionCentralizerIn (normalizer (L : Set G)) L)
    (hVW : V.map (MulAut.conj (c : G)).toMonoidHom ≤ W)
    (hZ : center K = ⊥) :
    let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
    let E := ((W.subgroupOf H).subgroupOf K).map f
    let C := (((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K).map f
    normalizer (E : Set Rudvalis.Model) = C ∧ Nat.card C = 64 * 12096 ∧
      ∀ z : E, z ≠ 1 →
        Nat.card ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf C) = 12288 := by
  let Y := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  let B := ((Y.subgroupOf H).subgroupOf K).map f
  let U := (W.subgroupOf H).subgroupOf K
  let E := U.map f
  let C0 := ((H ⊓ normalizer (L : Set G)).subgroupOf H).subgroupOf K
  let C := C0.map f
  change normalizer (E : Set Rudvalis.Model) = C ∧ Nat.card C = 64 * 12096 ∧
    ∀ z : E, z ≠ 1 →
      Nat.card ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf C) = 12288
  have hfi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro x hx
    apply hZ.le
    apply (QuotientGroup.eq_one_iff _).mp
    exact e.injective (hx.trans (map_one e).symm)
  have hfs : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hspanH : conjugateSpanBy Y (H ⊓ normalizer (L : Set G)) ≤ H :=
    (conjugateSpanBy_le_self hc.component_le).trans hc.local_le
  have hWH : W ≤ H := hc.module_le.trans hspanH
  have hWK : W.subgroupOf H ≤ K :=
    (subgroupOf_mono H hc.module_le).trans (hc.ordinary_span_le K hK)
  have hUC : normalizer (U : Set K) ≤ C0 := by
    rw [←subgroupOf_normalizer_eq hWK,←subgroupOf_normalizer_eq hWH]
    intro x hx
    exact hc.module_normalizer ⟨x.val.property,hx⟩
  obtain ⟨hNC,hcore,_⟩ := unitary_original_pushingUp_rudvalis_normalizer
    s hcover hJH hc K hK e c hVW
  change normalizer (B : Set Rudvalis.Model) = C at hNC
  change C.pCoreIn 2 = E at hcore
  have hEN : normalizer (E : Set Rudvalis.Model) = C := by
    apply le_antisymm
    · rw [show E = U.map f from rfl,←map_normalizer_eq_of_bijective U ⟨hfi,hfs⟩]
      exact map_mono hUC
    · rw [←hcore]
      exact C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hlt := unitary_original_pushingUp_rudvalis_module_normalizer_growth
    s hcover hJH hc K hK e c hVW
  change B < normalizer (E : Set Rudvalis.Model) at hlt
  rw [hEN] at hlt
  have hB := (unitary_original_pushingUp_rudvalis_module_and_points
    s hcover hJH hc K hK e c hVW).2.1
  change Nat.card B = 64 * 6048 at hB
  have hsizes := unitary_original_pushingUp_rudvalis_normalizer_sizes
    s hcover hJH hc K hK e c hVW
  dsimp only at hsizes
  rw [hNC] at hsizes
  obtain ⟨n,hn,hncard,hnpoints⟩ := hsizes
  have hn2 : n = 2 := by
    rcases hn with hn | hn
    · subst n
      exfalso
      apply hlt.ne
      apply eq_of_le_of_card_ge hlt.le
      rw [hB,hncard]
    · exact hn
  subst n
  exact ⟨hEN,by simpa only [Nat.reduceMul] using hncard,
    by simpa only [Nat.reduceMul] using hnpoints⟩

/-- The actual escaping pair retains the relative Sylow and the whole module.
In the Rudvalis branch its elementary Thompson subgroups recover the module
and its module normalizer strictly contains the residual. If the component
is centerless, this is the original local normalizer and its order is exact. -/
theorem unitary_original_oddActorResidual_thompson_normalizer (s : Context T L V)
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
            B < normalizer (E : Set Rudvalis.Model) ∧
            (∀ P : Subgroup B, E.subgroupOf B ≤ P →
              elementaryAbelianMaxJ P = E.subgroupOf B) ∧
            (center K = ⊥ →
              normalizer (E : Set Rudvalis.Model) = C ∧ Nat.card C = 64 * 12096 ∧
              ∀ z : E, z ≠ 1 →
                Nat.card ((centralizer ({(z : Rudvalis.Model)} : Set Rudvalis.Model)).subgroupOf C) =
                  12288)) := by
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
      unitary_original_pushingUp_rudvalis_module_normalizer_growth s hcover hJH hc K hK e c hcV,
      unitary_original_pushingUp_rudvalis_thompson s hcover hJH hc K hK e c hcV,
      unitary_original_pushingUp_rudvalis_centerless_sizes s hcover hJH hc K hK e c hcV⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
