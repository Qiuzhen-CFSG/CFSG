module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.ClassifiedSections
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Projection
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.ModelSelection.Exceptional
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BorelInner.AutomorphismCollapse.TorusControl

/-!
# Borel control from the solvable contained-offender base

Universal (j) places the solvable join B(Y₀T) in M ∩ H. The theta identity
and the intrinsic cubic quotient then make B prime to three under
noncontainment. Thus only Y₀T needs to be solvable. The normality used in
this argument is relative to H.

The exceptional exclusions apply the intrinsic A₇ and actual hexacode-cover
order-three theorems to the original relative component. The universal
B.5.5 component-section implication is applied by `Input.component_sections`;
no stronger source record or component-generation premise is introduced.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.49(k), printed pp.1143–1144; A.3.18, pp.51–52; B.5.5, pp.104–105.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Containment
open Subgroup ComponentReduction ModelReduction BorelInner
open AutomorphismCollapse ModelSelection
open scoped IsMulCommutative

universe u
variable {G : Type u} [Group G] [Finite G]
variable {κ : GroupClass.{u}} {H M Y V Y0 L ZS Z E upper : Subgroup G}
    {T : Sylow 2 G} [IsElementaryAbelian 2 (localSpan ZS H)]
    (d : Input κ H M Y V Y0 T ZS Z E L upper)

include d

omit [Finite G] in
/-- Every conjugate retains the source commutator identity. -/
theorem conjugate_commutator_eq (t : G) (ht : t ∈ (T : Subgroup G)) :
    L.map (MulAut.conj t).toMonoidHom = ⁅L.map (MulAut.conj t).toMonoidHom, Y0⁆ := by
  have hYmap : Y0.map (MulAut.conj t).toMonoidHom = Y0 :=
    mem_normalizer_iff_map_conj_eq.mp (d.normalizes ht)
  conv_lhs => rw [d.component.commutator_eq]
  rw [map_commutator, hYmap]

/-- The actor fixes each component individually, without an orbit collapse. -/
theorem conjugate_star_normalized (t : G) (ht : t ∈ (T : Subgroup G)) :
    starImage H Y0 ≤ normalizer
      (starImage H (L.map (MulAut.conj t).toMonoidHom) : Set (H ⧸ pCore 2 H)) := by
  have hCH : L.map (MulAut.conj t).toMonoidHom ≤ H := by
    rintro x ⟨l, hl, rfl⟩
    exact d.closure_le (subset_closure ⟨t, ht, l, hl, rfl⟩)
  apply le_normalizer_iff_commutator_le_left.mpr
  rw [← starImage_commutator H _ Y0 hCH d.y_le, ← conjugate_commutator_eq d t ht]

/-- Noncontainment identifies and normalizes the actual Sylow intersection. -/
theorem sylow_intersection (hout : ¬ Y0 ≤ localSpan L T) :
    (Y0 ⊔ (T : Subgroup G)) ⊓ localSpan L T = sylowIntersection L T ∧
    Y0 ⊔ (T : Subgroup G) ≤ normalizer (sylowIntersection L T : Set G) :=
  replacement_sylow_intersection H M Y0 L T d.replacement d.placed.t_le_m
    d.placed.theta_eq d.normalizes d.component.commutator_eq d.quotient_card_in hout

private theorem three_free (hout : ¬ Y0 ≤ localSpan L T) (B : Subgroup G)
    (hBM : B ≤ M ⊓ H) (hBL : B ≤ localSpan L T) : ¬ 3 ∣ Nat.card B := by
  intro hd
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 hd
  have hb3 : orderOf (b : G) = 3 := (Subgroup.orderOf_coe b).trans hb
  have hbY : (b : G) ∈ Y0 := d.placed.theta_eq ▸ subset_closure ⟨hBM b.property, hb3⟩
  let L' := (localSpan L T).subgroupOf H
  let Y' := Y0.subgroupOf H
  let _ : L'.Normal := d.closure_normal
  let _ : (L'.map (MonoidHom.id H)).Normal := by
    simpa only [Subgroup.map_id] using d.closure_normal
  have hY : IsPPerfect 2 Y' :=
    d.placed.toLocalInput.twoPerfect.of_surjective
      (subgroupOfEquivOfLe d.y_le).symm.toMonoidHom
      (subgroupOfEquivOfLe d.y_le).symm.surjective
  have hy : Y' ≤ L' := by
    apply pPerfect_le_of_cubic_image_intersection (MonoidHom.id H)
      (IsPGroup.ker_isPGroup_of_injective Function.injective_id) Y' L' hY d.quotient_card_in
    simp only [Subgroup.map_id]
    exact ⟨⟨b, (hBM b.property).2⟩, ⟨hbY, hBL b.property⟩,
      (Subgroup.orderOf_mk _ _).trans hb3⟩
  exact hout (fun x hx => hy (show (⟨x, d.y_le hx⟩ : H) ∈ Y' from hx))

/-- All local Borel control, using only solvability of the base Y₀T. -/
theorem borel_control [Group.IsSolvable (relativeBorel L T)]
    (hout : ¬ Y0 ≤ localSpan L T) :
    (Y0 ⊔ (T : Subgroup G)) ⊓ localSpan L T = sylowIntersection L T ∧
    Y0 ⊔ (T : Subgroup G) ≤ normalizer (relativeBorel L T : Set G) ∧
    relativeBorel L T ≤ M ⊓ H ∧ ¬ 3 ∣ Nat.card (relativeBorel L T) ∧
    relativeBorel L T ≤ normalizer (Y0 : Set G) ∧
    ⁅relativeBorel L T, Y0⁆ ≤ sylowIntersection L T := by
  obtain ⟨hi, hn⟩ := sylow_intersection d hout
  have hNN : Y0 ⊔ (T : Subgroup G) ≤
      normalizer (normalizer (sylowIntersection L T : Set G) : Set G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (normalizer (sylowIntersection L T : Set G)).map (MulAut.conj s).toMonoidHom = _
    rw [map_equiv_normalizer_eq]
    have he : (sylowIntersection L T).map (MulAut.conj s).toMonoidHom =
        sylowIntersection L T := mem_normalizer_iff_map_conj_eq.mp (hn hs)
    rw [he]
  have hB : Y0 ⊔ (T : Subgroup G) ≤ normalizer (relativeBorel L T : Set G) :=
    (le_inf ((sup_le d.y_le d.t_le).trans d.closure_normalized) hNN).trans
      inf_normalizer_le_normalizer_inf
  have hBM : relativeBorel L T ≤ M ⊓ H := by
    let _ := d.base_solvable
    let _ := solvable_normalized_join (relativeBorel L T) (Y0 ⊔ (T : Subgroup G)) hB
    exact le_sup_left.trans (d.overgroups _ inferInstance le_sup_right
      (sup_le (inf_le_left.trans d.closure_le) (sup_le d.y_le d.t_le)))
  have hBY : relativeBorel L T ≤ normalizer (Y0 : Set G) :=
    (hBM.trans inf_le_left).trans_eq d.placed.normalizer_eq.symm
  exact ⟨hi, hB, hBM, three_free d hout _ hBM inf_le_left, hBY,
    borel_commutator_le_sylow_intersection Y0 T (localSpan L T) (relativeBorel L T)
      inf_le_left hBY (le_sup_left.trans hB) hi⟩

/-- The component's intrinsic quotient, keeping the inclusion into H explicit. -/
noncomputable def relativeStarEquiv :
    ((L.subgroupOf H) ⧸ pCore 2 (L.subgroupOf H)) ≃* starImage H L :=
  (QuotientGroup.congr _ _ (subgroupOfEquivOfLe d.l_le)
    (pCore_map_iso 2 _)).trans (starQuotientEquiv H L d.l_le d.component_in_H.subnormal)

/-- A₇'s two independent cubic cycles force each theta generator into L. -/
theorem y_le_of_seven (e : starImage H L ≃* alternatingGroup (Fin 7)) : Y0 ≤ L := by
  rw [← d.placed.theta_eq]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨hx, hx3⟩
  have hxY : x ∈ Y0 := d.placed.theta_eq ▸ (subset_closure ⟨hx, hx3⟩)
  have hxN : x ∈ normalizer (L : Set G) :=
    (le_normalizer_iff_commutator_le_left.mpr d.component.commutator_eq.ge) hxY
  exact alternatingGroup.SevenComponent.order_three_mem (L.subgroupOf H)
    d.component_in_H ((relativeStarEquiv d).trans e)
    (d.placed.sqtk.stronglyQuasithin 3 (by decide) (by decide))
    (x := ⟨x, hx.2⟩) (by simpa using hx3) (by
      rw [← subgroupOf_normalizer_eq d.l_le]
      exact hxN)

/-- The actual triple cover retains its central three-subgroup in this argument. -/
theorem y_le_of_cover (e : starImage H L ≃* Atlas.Codes.HexEvenAutomorphisms) : Y0 ≤ L := by
  rw [← d.placed.theta_eq]
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨hx, hx3⟩
  have hxY : x ∈ Y0 := d.placed.theta_eq ▸ (subset_closure ⟨hx, hx3⟩)
  have hxN : x ∈ normalizer (L : Set G) :=
    (le_normalizer_iff_commutator_le_left.mpr d.component.commutator_eq.ge) hxY
  exact Theory.GroupTheory.HexacodeTheta.order_three_mem (L.subgroupOf H)
    d.component_in_H ((relativeStarEquiv d).trans e)
    (d.placed.sqtk.stronglyQuasithin 3 (by decide) (by decide))
    (x := ⟨x, hx.2⟩) (by simpa using hx3) (by
      rw [← subgroupOf_normalizer_eq d.l_le]
      exact hxN)

/-- Apply B.5.5 on the genuine contained actor, then exclude both exceptional cases. -/
theorem lie_model (sections : EarlierComponentSections κ) (hout : ¬ Y0 ≤ localSpan L T) :
    ∃ e, LieComponentModel (starImage H L) e := by
  cases (d.component_sections sections).componentModel with
  | lie e model => exact ⟨e, model⟩
  | alternating_seven model =>
    exact (hout ((y_le_of_seven d model.some).trans (le_conjugateSpanBy L T))).elim
  | triple_alternating_six model =>
    exact (hout ((y_le_of_cover d model.some).trans (le_conjugateSpanBy L T))).elim

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.ReducedModels.Containment
