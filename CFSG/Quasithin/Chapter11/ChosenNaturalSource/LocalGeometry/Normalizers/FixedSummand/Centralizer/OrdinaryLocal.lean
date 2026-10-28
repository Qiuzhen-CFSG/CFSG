module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer.Rudvalis
public import Theory.GroupTheory.PerfectCentralQuotientNormalizer

/-!
# The actual ordinary local geometry after central projection

The intersection of the original radical with K contains Z(K), since the
center is a two-group. Its image remains a nontrivial radical subgroup of
K/Z(K). Perfectness reflects normalization of the covering residual across
the central kernel, identifying its full projected normalizer with the image
of the original M intersection.

The full C.2.8 module W remains elementary, nonzero, moved by that residual
and central in the projected radical. Its original normalizer control is
transported without asserting that every normalizer of its image lifts.
The shared field-four application retains the actual natural-action marking
and the inclusion-compatible quotient map. No shortness or W=V is used.

The remaining J4 local inspection and degree-two 11.1.5 assembly belong to
qt-d-1222-natural-point-fixed-summand. Earlier-source discharge remains with
qt-d-1222-natural-normalizer-source; the odd-normalizer owner consumes the
same covering-residual geometry.

Source: Aschbacher--Smith C.2.9--12 and C.3.2--5, printed pp.147--150;
the ordinary local inspections in 4.2.13 and 4.4.12, pp.611--612 and622.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
variable {G : Type*} [Group G] [Finite G] {H M B R W : Subgroup G}

/-- The original residual, local subgroup, radical and full module inside K. -/
abbrev ordinaryComponentSubgroup (B : Subgroup G) (K : Subgroup H) : Subgroup K :=
  (B.subgroupOf H).subgroupOf K

private def componentInclusion (K : Subgroup H) : K →* G := H.subtype.comp K.subtype

omit [Finite G] in
private theorem componentInclusion_injective (K : Subgroup H) :
    Function.Injective (componentInclusion K) :=
  H.subtype_injective.comp K.subtype_injective

omit [Finite G] in
private theorem map_ordinaryComponentSubgroup (A : Subgroup G) (K : Subgroup H)
    (hAH : A ≤ H) (hAK : A.subgroupOf H ≤ K) :
    (ordinaryComponentSubgroup A K).map (componentInclusion K) = A := by
  rw [componentInclusion, ← map_map, map_subgroupOf_eq_of_le hAK,
    map_subgroupOf_eq_of_le hAH]

private theorem ordinaryComponentSubgroup_perfect
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hn : (B.subgroupOf M).Normal) (K : Subgroup H) (hK : IsComponent H K) :
    Group.IsPerfect (ordinaryComponentSubgroup B K) := by
  have hs := h.normalized_span_eq
    ((normal_subgroupOf_iff_le_normalizer h.component_le).mp hn)
  have hb : Group.IsPerfect B := hs ▸ h.span_perfect
  let := hb
  let e := (subgroupOfEquivOfLe (h.ordinary_component_contains_original K hK)).trans
    (subgroupOfEquivOfLe (h.component_le.trans h.local_le))
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- The normalizer of the original residual inside K is the original M intersection. -/
theorem ordinary_component_normalizer
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hn : (B.subgroupOf M).Normal) (K : Subgroup H) (hK : IsComponent H K) :
    normalizer (ordinaryComponentSubgroup B K : Set K) = ordinaryComponentSubgroup M K := by
  have hs := h.normalized_span_eq
    ((normal_subgroupOf_iff_le_normalizer h.component_le).mp hn)
  have he := h.normalizer_span_eq
  rw [hs] at he
  rw [← subgroupOf_normalizer_eq (h.ordinary_component_contains_original K hK),
    ← subgroupOf_normalizer_eq (h.component_le.trans h.local_le)]
  ext k
  exact Iff.intro
    (fun hk => he.le ⟨k.val.property,hk⟩)
    (fun hk => (he.ge hk).2)

/-- The projected residual is the range of the unchanged ambient inclusion. -/
theorem ordinary_component_cover_image
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : IsComponent H K) :
    (ordinaryComponentSubgroup B K).map (QuotientGroup.mk' (center K)) =
      (ordinaryCoverProjection h K hK).range := by
  ext x
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact ⟨⟨b.val.val,hb⟩,rfl⟩
  · rintro ⟨b,rfl⟩
    exact ⟨ordinaryCoverInclusion h K hK b,b.property,rfl⟩

/-- Central projection preserves the entire residual normalizer, not only B. -/
theorem ordinary_projected_normalizer
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hn : (B.subgroupOf M).Normal) (K : Subgroup H) (hK : IsComponent H K) :
    normalizer ((ordinaryCoverProjection h K hK).range : Set (K ⧸ center K)) =
      (ordinaryComponentSubgroup M K).map (QuotientGroup.mk' (center K)) := by
  let := ordinaryComponentSubgroup_perfect h hn K hK
  have he := comap_normalizer_map_eq_of_perfect (QuotientGroup.mk' (center K))
    (by rw [QuotientGroup.ker_mk']) (ordinaryComponentSubgroup B K)
  rw [ordinary_component_normalizer h hn K hK] at he
  have hm := congrArg (map (QuotientGroup.mk' (center K))) he
  rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective (center K)),
    ordinary_component_cover_image h K hK] at hm
  exact hm

/-- The radical intersection survives as a nontrivial radical subgroup of K/Z(K). -/
theorem ordinary_projected_radical
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (K : Subgroup H) (hK : IsComponent H K) :
    IsPRadical 2 ((ordinaryComponentSubgroup R K).map (QuotientGroup.mk' (center K))) := by
  have hr := h.ordinary_radical_intersection_isRadical K hK
  let := hK.2
  have hz : center K = pCore 2 K :=
    IsQuasisimple.center_eq_pCore (hK.1.pPrimeCore_eq_bot h.oddCore_eq_bot K)
  have hc : center K ≤ ordinaryComponentSubgroup R K := by
    rw [hz]
    exact pCore_le_of_pCore_normalizer_le _ hr.isPGroup hr.2.le
  refine ⟨(h.ordinary_quotient_local_data K hK).2.2.1, ?_⟩
  exact map_normalizer_core_of_p_kernel _ hr.isPGroup hr.2
    (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
    (by rwa [QuotientGroup.ker_mk'])

/-- The full C.2.8 module retains its moved action in the central quotient.
This statement makes no identification with the original chosen seed. -/
theorem ordinary_projected_module
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hn : (B.subgroupOf M).Normal) (K : Subgroup H) (hK : IsComponent H K) :
    let q := QuotientGroup.mk' (center K)
    let X := (ordinaryCoverProjection h K hK).range
    let P := (ordinaryComponentSubgroup R K).map q
    let U := (ordinaryComponentSubgroup W K).map q
    IsElementaryAbelian 2 U ∧ U ≠ ⊥ ∧ U ≤ X ∧
      U ≤ P ⊓ centralizer (P : Set (K ⧸ center K)) ∧ U = ⁅U,X⁆ := by
  let q := QuotientGroup.mk' (center K)
  let A := ordinaryComponentSubgroup B K
  let E := ordinaryComponentSubgroup W K
  let P := ordinaryComponentSubgroup R K
  have hs := h.normalized_span_eq
    ((normal_subgroupOf_iff_le_normalizer h.component_le).mp hn)
  have hWB : W ≤ B := hs ▸ h.module_le
  have hWH := hWB.trans (h.component_le.trans h.local_le)
  have hWK := (h.ordinary_module_placement K hK).1.trans inf_le_right
  have hWR := h.module_le_center_radical.trans (map_subtype_le _)
  have hmove : E = ⁅E,A⁆ := by
    apply map_injective (componentInclusion_injective K)
    rw [map_commutator, map_ordinaryComponentSubgroup W K hWH hWK,
      map_ordinaryComponentSubgroup B K (h.component_le.trans h.local_le)
        (h.ordinary_component_contains_original K hK)]
    exact hs ▸ h.module_commutator
  have hEP : E ≤ P := fun _ hw => hWR hw
  have hEC : E ≤ centralizer (P : Set K) := by
    intro w hw r hr
    obtain ⟨w',hw',he⟩ := h.module_le_center_radical hw
    apply (componentInclusion_injective K)
    change ((r : H) : G) * ((w : H) : G) = ((w : H) : G) * ((r : H) : G)
    change (w' : G) = ((w : H) : G) at he
    rw [←he]
    exact congrArg Subtype.val (mem_center_iff.mp hw' ⟨r.val.val,hr⟩)
  have hcomm : ⁅E.map q,P.map q⁆ = ⊥ := by
    rw [←map_commutator,commutator_eq_bot_iff_le_centralizer.mpr hEC,Subgroup.map_bot]
  have hE : IsElementaryAbelian 2 E := by
    let := h.module_elementary
    let e := (subgroupOfEquivOfLe hWK).trans (subgroupOfEquivOfLe hWH)
    exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective
  refine ⟨?_,?_,?_,le_inf (map_mono hEP)
    (commutator_eq_bot_iff_le_centralizer.mp hcomm),?_⟩
  · let := hE
    exact IsElementaryAbelian.map q
  · intro he
    have hc : E ≤ center K := by
      simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff E).mp he
    apply (h.ordinary_module_placement K hK).2
    intro w hw k hk
    exact congrArg K.subtype
      (mem_center_iff.mp (hc (show (⟨w,hWK hw⟩ : K) ∈ E from hw)) ⟨k,hk⟩)
  · rw [←ordinary_component_cover_image h K hK]
    exact map_mono (fun _ hw => hWB hw)
  · rw [←ordinary_component_cover_image h K hK,←map_commutator,←hmove]

/-- Projecting the original W-normalizer preserves the source control.
No equality with the full normalizer of its projected image is asserted. -/
theorem ordinary_projected_module_normalizer_control
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hn : (B.subgroupOf M).Normal) (K : Subgroup H) (hK : IsComponent H K) :
    (normalizer (ordinaryComponentSubgroup W K : Set K)).map (QuotientGroup.mk' (center K)) ≤
      normalizer ((ordinaryCoverProjection h K hK).range : Set (K ⧸ center K)) := by
  rw [ordinary_projected_normalizer h hn K hK]
  apply map_mono
  have hWH := h.module_le.trans ((conjugateSpanBy_le_self h.component_le).trans h.local_le)
  have hWK := (h.ordinary_module_placement K hK).1.trans inf_le_right
  rw [←subgroupOf_normalizer_eq hWK,←subgroupOf_normalizer_eq hWH]
  intro k hk
  exact h.module_normalizer ⟨k.val.property,hk⟩

/-- The same projected residual normalizes the unchanged projected radical. -/
theorem ordinary_projected_cover_normalizes_radical
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hn : (B.subgroupOf M).Normal) (K : Subgroup H) (hK : IsComponent H K) :
    (ordinaryCoverProjection h K hK).range ≤
      normalizer ((ordinaryComponentSubgroup R K).map (QuotientGroup.mk' (center K)) :
        Set (K ⧸ center K)) := by
  rw [←ordinary_component_cover_image h K hK]
  apply le_trans (map_mono (f := QuotientGroup.mk' (center K)) ?_)
    ((ordinaryComponentSubgroup R K).le_normalizer_map _)
  have hs := h.normalized_span_eq
    ((normal_subgroupOf_iff_le_normalizer h.component_le).mp hn)
  intro b hb r
  exact (hs ▸ h.span_normalizes_radical) hb r.val.val

/-- The full projected C.2.8 geometry, with the same residual, radical and W.
The last containment projects the original W-normalizer; it does not
replace it by the possibly larger normalizer of the image. -/
theorem ordinary_projected_geometry
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hn : (B.subgroupOf M).Normal) (K : Subgroup H) (hK : IsComponent H K) :
    let q := QuotientGroup.mk' (center K)
    let X := (ordinaryCoverProjection h K hK).range
    let P := (ordinaryComponentSubgroup R K).map q
    let U := (ordinaryComponentSubgroup W K).map q
    Group.IsPerfect X ∧ IsPRadical 2 P ∧
      normalizer (X : Set (K ⧸ center K)) = (ordinaryComponentSubgroup M K).map q ∧
      X ≤ normalizer (P : Set (K ⧸ center K)) ∧
      IsElementaryAbelian 2 U ∧ U ≠ ⊥ ∧ U ≤ X ∧
      U ≤ P ⊓ centralizer (P : Set (K ⧸ center K)) ∧ U = ⁅U,X⁆ ∧
      (normalizer (ordinaryComponentSubgroup W K : Set K)).map q ≤
        normalizer (X : Set (K ⧸ center K)) := by
  have hperfect : Group.IsPerfect (ordinaryCoverProjection h K hK).range := by
    rw [←ordinary_component_cover_image h K hK]
    let := ordinaryComponentSubgroup_perfect h hn K hK
    exact Group.IsPerfect.map _
  obtain ⟨he,hne,hUX,hUP,hm⟩ := ordinary_projected_module h hn K hK
  exact ⟨hperfect,ordinary_projected_radical h K hK,
    ordinary_projected_normalizer h hn K hK,
    ordinary_projected_cover_normalizes_radical h hn K hK,
    he,hne,hUX,hUP,hm,ordinary_projected_module_normalizer_control h hn K hK⟩

/-- Compatibility with the original L quotient is preserved on representatives. -/
theorem ordinary_projected_quotient_compatible
    {L : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hBL : B ≤ L) (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (he : ∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
      QuotientGroup.mk' (pCore 2 L) (inclusion hBL b))
    (K : Subgroup H) (hK : IsComponent H K) (b : B) :
    ((ordinaryCoverQuotient h K hK).symm.trans e)
      (QuotientGroup.mk' (pCore 2 (ordinaryCoverProjection h K hK).range)
        ((ordinaryCoverProjection h K hK).rangeRestrict b)) =
      QuotientGroup.mk' (pCore 2 L) (inclusion hBL b) := by
  rw [←ordinaryCoverQuotient_mk h K hK b, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply]
  exact he b

open Representation CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped Pointwise MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open WeakClosure.Generation

/-- The ordinary field-four local reduction for the common covering residual.
The original quotient comparison remains compatible with inclusion, and the
radical and full residual normalizer are the literal component images.
The J4 model inspection and its final source discharge remain with this owner. -/
theorem c28_covering_jankoFour_local
    {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (_hstrict : M < H) (hn : (B.subgroupOf M).Normal)
    (hBL : B ≤ L) (hc : (L : Set G) = (B : Set G) * (L.pCoreIn 2 : Set G))
    (hVB : V ≤ B.pCoreIn 2)
    (e : (B ⧸ pCore 2 B) ≃* (L ⧸ pCore 2 L))
    (he : ∀ b : B, e (QuotientGroup.mk' (pCore 2 B) b) =
      QuotientGroup.mk' (pCore 2 L) (inclusion hBL b))
    (K : Subgroup H) (hK : IsComponent H K) :
    let q := QuotientGroup.mk' (center K)
    let X := (ordinaryCoverProjection h K hK).range
    Nonempty (K ⧸ center K ≃* Janko4.Model) ∧ S.field.degree = 2 ∧
      IsPRadical 2 ((ordinaryComponentSubgroup R K).map q) ∧
      normalizer (X : Set (K ⧸ center K)) = (ordinaryComponentSubgroup M K).map q ∧
      ∃ a : (X ⧸ pCore 2 X) ≃* SL(3,S.field.Carrier),
        ∃ m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3),
          ∀ b : B, a (QuotientGroup.mk' (pCore 2 X)
              ((ordinaryCoverProjection h K hK).rangeRestrict b)) =
            m.groupEquiv (QuotientGroup.mk' (pCore 2 L) (inclusion hBL b)) := by
  obtain ⟨hk,hf,⟨a⟩,_⟩ := c28_covering_ordinary_jankoFour D S h hBL hc hVB e K hK
  obtain ⟨m⟩ := OddNormalizer.linear_marking_of_field_four D S hf a
  refine ⟨hk,hf,ordinary_projected_radical h K hK,
    ordinary_projected_normalizer h hn K hK,
    ((ordinaryCoverQuotient h K hK).symm.trans e).trans m.groupEquiv,m,?_⟩
  intro b
  exact congrArg m.groupEquiv (ordinary_projected_quotient_compatible h hBL e he K hK b)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Centralizer
