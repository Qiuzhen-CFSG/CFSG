module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.FixedSpaces
public import Theory.Representation.BinaryOffender.GeneratedLayerQuotient
public import Theory.Representation.BinaryOffender.NormalizerExtension

/-!
# The full automizer on the actual natural quotient

The image of L in Aut_G(V) is identified with the same marked L/O₂(L).
Its normality follows from N_G(V) ≤ N_G(L). The original identity V=[V,L]
then makes the quotient by C_V(L) faithful for the entire automizer, including
outer actors. The literal coordinate projection intertwines this action and
embeds it into the full binary normalizer of the marked natural module.
No splitting or vanishing of the central attachment is assumed.

Source: Aschbacher--Smith, 11.0.4 and 11.2.2(1--4), printed pp.760,767--768.
The involution calculations in Involutions use this faithful quotient.
-/

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (c : Coordinates D S.field)

/-- The given faithful central quotient makes the marked model action faithful. -/
theorem model_faithful : Function.Injective c.modelAction := by
  intro a b hab
  obtain ⟨a, rfl⟩ := c.groupEquiv.surjective a
  obtain ⟨b, rfl⟩ := c.groupEquiv.surjective b
  apply congrArg c.groupEquiv
  apply S.faithful
  apply LinearMap.ext
  intro v
  apply c.linearEquiv.injective
  rw [c.intertwines, c.intertwines, hab]

/-- The original component maps onto its literal image in Aut_G(V). -/
def layerAction : L →* inducedAutomizer V L :=
  ((V.normalizerMonoidHom.rangeRestrict).comp (inclusion D.normalizes)).codRestrict _
    (fun l => ⟨⟨l, D.normalizes l.property⟩, l.property, rfl⟩)

omit [Finite G] in
theorem layerAction_surjective : Function.Surjective (layerAction D) := by
  rintro ⟨a, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

theorem layerAction_eq_one_iff (l : L) :
    layerAction D l = 1 ↔ c.quotientMap l = 1 := by
  constructor
  · intro hl
    apply model_faithful D S c
    rw [map_one]
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := c.projection_surjective (Multiplicative.ofAdd w)
    have he := congrArg
      (fun a : inducedAutomizer V L => ((a.val.val) v : G)) hl
    have hc : (l : G) * (v : G) = (v : G) * (l : G) :=
      mul_inv_eq_iff_eq_mul.mp he
    exact (NaturalFixedSpaces.centralizes_vector_iff D S c l v).mp hc
  · intro hl
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change (l : G) * (v : G) * (l : G)⁻¹ = v
    apply mul_inv_eq_iff_eq_mul.mpr
    apply (NaturalFixedSpaces.centralizes_vector_iff D S c l v).mpr
    rw [hl, map_one, Module.End.one_apply]

/-- The image marking retains the full L/O₂(L), including its center. -/
def layerEquiv : inducedAutomizer V L ≃* c.ModelGroup :=
  (QuotientGroup.quotientKerEquivOfSurjective (layerAction D)
    (layerAction_surjective D)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (show (layerAction D).ker = c.quotientMap.ker by
        ext l
        exact layerAction_eq_one_iff D S c l)).trans
          (QuotientGroup.quotientKerEquivOfSurjective c.quotientMap c.quotientMap_surjective))

theorem layerEquiv_apply (l : L) :
    layerEquiv D S c (layerAction D l) = c.quotientMap l := by
  change layerEquiv D S c
    ((QuotientGroup.quotientKerEquivOfSurjective (layerAction D)
      (layerAction_surjective D)) (QuotientGroup.mk' _ l)) = _
  simp only [layerEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

include D S in
/-- Normality is in the actual automizer, derived from N_G(V) ≤ N_G(L). -/
theorem layer_normal : (inducedAutomizer V L).Normal := by
  let : (L.subgroupOf (normalizer (V : Set G))).Normal :=
    normal_subgroupOf_of_le_normalizer (seed_normalizer_le D S)
  exact Subgroup.Normal.map inferInstance _ V.normalizerMonoidHom.rangeRestrict_surjective

variable [IsElementaryAbelian 2 V]

include D in
omit [Finite G] in
/-- The original commutator generation is generation by the component image. -/
theorem moved_eq_top :
    subspaceCommutator (automizerRepresentation V) ⊤ (inducedAutomizer V L) = ⊤ := by
  let W := subspaceCommutator (automizerRepresentation V) ⊤ (inducedAutomizer V L)
  let C := W.toAddSubgroup.toSubgroup'.map V.subtype
  have hcomm : ⁅V,L⁆ ≤ C := by
    apply commutator_le.mpr
    intro v hv l hl
    let v' : Additive V := Additive.ofMul ⟨v,hv⟩
    let a : inducedAutomizer V L := layerAction D ⟨l,hl⟩
    have hdisp : automizerRepresentation V a v' - v' ∈ W :=
      Submodule.subset_span ⟨a, a.property, v', Submodule.mem_top, rfl⟩
    refine ⟨(v' - automizerRepresentation V a v').toMul, ?_, ?_⟩
    · change v' - automizerRepresentation V a v' ∈ W
      simpa only [neg_sub] using W.neg_mem hdisp
    · rw [toMul_sub, div_eq_mul_inv]
      change v * (l * v * l⁻¹)⁻¹ = ⁅v,l⁆
      simp only [commutatorElement_def, mul_inv_rev, inv_inv, mul_assoc]
  apply top_unique
  intro v _
  have hv : (v.toMul : G) ∈ C := hcomm (D.eq_commutator ▸ v.toMul.property)
  obtain ⟨w, hw, he⟩ := hv
  have he' : w = v.toMul := Subtype.ext he
  change Additive.ofMul w ∈ W at hw
  simpa only [he', ofMul_toMul] using hw

/-- The coordinate projection, now as a binary linear map. -/
def projectionLinear : Additive V →ₗ[ZMod 2] c.Space :=
  c.projection.toAdditiveLeft.toZModLinearMap 2

theorem projectionLinear_surjective : Function.Surjective (projectionLinear D S c) :=
  c.projection_surjective

theorem projectionLinear_kernel :
    (projectionLinear D S c).ker = fixedSpace (automizerRepresentation V) (inducedAutomizer V L) := by
  ext v
  change c.projection v.toMul = 1 ↔ _
  rw [c.projection_eq_one_iff]
  constructor
  · intro hv a
    obtain ⟨l, rfl⟩ := layerAction_surjective D a
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G) * (v.toMul : G) * (l : G)⁻¹ = v.toMul
    exact mul_inv_eq_iff_eq_mul.mpr (hv l l.property)
  · intro hv l hl
    have he := congrArg (fun w : Additive V => (w.toMul : G))
      (hv (layerAction D ⟨l,hl⟩))
    exact mul_inv_eq_iff_eq_mul.mp he

/-- The faithful action of the full automizer on the original marked quotient.
No complement to its central kernel is used. -/
theorem exists_faithful_quotient_action :
    ∃ ρ : Representation (ZMod 2) (Automizer V) c.Space, Function.Injective ρ ∧
      (∀ a v, projectionLinear D S c (automizerRepresentation V a v) =
        ρ a (projectionLinear D S c v)) ∧
      ∀ (a : inducedAutomizer V L) v,
        ρ (a : Automizer V) v = c.modelAction (layerEquiv D S c a) v := by
  let := layer_normal D S
  let τ := (restrictScalars (k := ZMod 2) c.modelAction).comp
    (layerEquiv D S c).toMonoidHom
  have hτ : Function.Injective τ := by
    intro a b h
    apply (layerEquiv D S c).injective
    apply model_faithful D S c
    exact LinearMap.ext (fun v => LinearMap.congr_fun h v)
  apply exists_faithful_action_of_generated_layer_quotient
    (automizerRepresentation V) (automizerRepresentation_injective V)
    (inducedAutomizer V L) τ hτ (projectionLinear D S c)
    (projectionLinear_surjective D S c) (projectionLinear_kernel D S c) _ (moved_eq_top D)
  intro a v
  obtain ⟨l, rfl⟩ := layerAction_surjective D a
  change (c.projection (V.normalizerMonoidHom (inclusion D.normalizes l) v.toMul)).toAdd =
    c.modelAction (layerEquiv D S c (layerAction D l)) (c.projection v.toMul).toAdd
  rw [layerEquiv_apply]
  exact c.projection_component_conjugation l v.toMul

/-- Embed every actual automizer actor in the full binary normalizer of the
same marked natural action, retaining the literal coordinate projection. -/
theorem exists_normalizer_embedding :
    ∃ ι : Automizer V →* linearNormalizer (restrictScalars (k := ZMod 2) c.modelAction),
      Function.Injective ι ∧
      ∀ a v, projectionLinear D S c (automizerRepresentation V a v) =
        normalizerRepresentation (restrictScalars (k := ZMod 2) c.modelAction)
          (ι a) (projectionLinear D S c v) := by
  obtain ⟨ρ, hρ, he, hres⟩ := exists_faithful_quotient_action D S c
  let := layer_normal D S
  have him : actionImage (ρ.comp (inducedAutomizer V L).subtype) =
      actionImage (restrictScalars (k := ZMod 2) c.modelAction) := by
    ext u
    constructor
    · rintro ⟨a,rfl⟩
      refine ⟨layerEquiv D S c a, ?_⟩
      apply Units.ext
      exact (LinearMap.ext (hres a)).symm
    · rintro ⟨g,rfl⟩
      obtain ⟨a,rfl⟩ := (layerEquiv D S c).surjective g
      refine ⟨a, ?_⟩
      apply Units.ext
      exact LinearMap.ext (hres a)
  have hn (a : Automizer V) : ρ.asGroupHom a ∈
      linearNormalizer (restrictScalars (k := ZMod 2) c.modelAction) := by
    have hh := actionImage_le_linearNormalizer ρ (inducedAutomizer V L)
      (show ρ.asGroupHom a ∈ actionImage ρ from ⟨a,rfl⟩)
    change ρ.asGroupHom a ∈ normalizer (actionImage (ρ.comp
      (inducedAutomizer V L).subtype) : Set _) at hh
    rwa [him] at hh
  let ι := ρ.asGroupHom.codRestrict _ hn
  refine ⟨ι, ?_, he⟩
  intro a b hab
  exact hρ (congrArg (fun u : linearNormalizer
    (restrictScalars (k := ZMod 2) c.modelAction) => u.val.val) hab)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
