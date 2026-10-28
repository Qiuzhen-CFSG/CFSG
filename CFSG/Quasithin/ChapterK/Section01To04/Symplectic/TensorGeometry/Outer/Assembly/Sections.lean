module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.Assembly.Fixed
public import Theory.Representation.BinaryOffender.InvolutionHomology

/-!
# The original field involution and its faithful sections

Transport transposition to an actual involution of the original binary module.
For every outer involution it is the given representation operator. Explicit
fixed and displacement equivalences preserve the original component marking.
The actual component centralizer acts faithfully both on the displacement
space and on the literal fixed/displacement quotient: any kernel element
would act trivially on the corresponding faithful Hermitian section.

The section dimensions are 6s and 4s; the fixed space has dimension 10s.
These results use the coefficient-twisted tensor identification and the genuine
source hypotheses, with no added representation estimates.

Source: Aschbacher–Smith, K.3.4.2, printed p.457, following H.4.4(6).
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
namespace CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Assembly
open Model.Geometry
noncomputable section
variable {G V F : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
  (L : Subgroup G) [L.Normal] [IsIrreducible (ρ.comp L.subtype)]
  [Field F] [Algebra (SchurField (ρ.comp L.subtype)) F] [Finite F]
  [Algebra (ZMod 2) F]

variable {ρ L}
def movedEquiv {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (c : Sp F)
    (hc : ∀ v : V, normalizedEquiv ρ L h c (ρ t v) =
      Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v)) :
    LinearMap.range (ρ t - LinearMap.id) ≃ₗ[ZMod 2] Model.fieldMoved h.sigma h.sigma_involutive where
  toFun v := ⟨normalizedEquiv ρ L h c v.val, by
    obtain ⟨w, hw⟩ := v.property
    rw [← hw]
    refine ⟨normalizedEquiv ρ L h c w, ?_⟩
    change Model.fieldSwap h.sigma h.sigma_involutive _ - _ =
      normalizedEquiv ρ L h c (ρ t w - w)
    rw [map_sub, hc, LinearMap.id_apply]⟩
  invFun X := ⟨(normalizedEquiv ρ L h c).symm X.val, by
    obtain ⟨Y, hY⟩ := X.property
    refine ⟨(normalizedEquiv ρ L h c).symm Y, ?_⟩
    apply (normalizedEquiv ρ L h c).injective
    change normalizedEquiv ρ L h c
      (ρ t ((normalizedEquiv ρ L h c).symm Y) - (normalizedEquiv ρ L h c).symm Y) =
      normalizedEquiv ρ L h c ((normalizedEquiv ρ L h c).symm X.val)
    rw [map_sub, hc, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    exact hY⟩
  left_inv v := Subtype.ext ((normalizedEquiv ρ L h c).symm_apply_apply v.val)
  right_inv X := Subtype.ext ((normalizedEquiv ρ L h c).apply_symm_apply X.val)
  map_add' _ _ := Subtype.ext (map_add _ _ _)
  map_smul' _ _ := Subtype.ext (map_smul _ _ _)

variable (ρ L)
abbrev componentCentralizer (t : G) : Subgroup G := L ⊓ Subgroup.centralizer {t}

def centralizerMark {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (c : Sp F)
    (hc : ∀ v : V, normalizedEquiv ρ L h c (ρ t v) =
      Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v)) :
    componentCentralizer L t →* centralizer h.sigma :=
  ((nativeMark ρ L h c).toMonoidHom.comp (Subgroup.inclusion inf_le_left)).codRestrict _
    (fun g => normalized_centralizer ρ L hS h t c hc ⟨g.val, g.property.1⟩
      (Subgroup.mem_centralizer_singleton_iff.mp g.property.2))

omit [Finite G] [L.Normal] in
lemma centralizerMark_injective {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (c : Sp F)
    (hc : ∀ v : V, normalizedEquiv ρ L h c (ρ t v) =
      Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v)) :
    Function.Injective (centralizerMark ρ L hS h t c hc) := by
  intro a b hab
  apply Subtype.ext
  have he := (nativeMark ρ L h c).injective (congrArg Subtype.val hab)
  exact congrArg (fun x : L => x.val) he

omit [Finite G] [L.Normal] in
lemma normalizedEquiv_centralizer {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (c : Sp F)
    (hc : ∀ v : V, normalizedEquiv ρ L h c (ρ t v) =
      Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v))
    (g : componentCentralizer L t) (v : V) :
    normalizedEquiv ρ L h c (ρ g.val v) =
      Model.action h.sigma h.sigma_involutive (centralizerMark ρ L hS h t c hc g).val
        (normalizedEquiv ρ L h c v) := by
  change normalizedEquiv ρ L h c (ρ g.val v) =
    Model.action h.sigma h.sigma_involutive
      (c⁻¹ * h.groupEquiv ⟨g.val, g.property.1⟩ * (c⁻¹)⁻¹)
      (normalizedEquiv ρ L h c v)
  simpa only [inv_inv] using normalizedEquiv_component ρ L h c ⟨g.val, g.property.1⟩ v


variable [CharP F 2]

omit [Finite G] [L.Normal] in
theorem moved_action_faithful {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (c : Sp F)
    (hc : ∀ v : V, normalizedEquiv ρ L h c (ρ t v) =
      Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v)) :
    Function.Injective (InvolutionHomology.moved ρ t (componentCentralizer L t) inf_le_right).toRepresentation := by
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  apply centralizerMark_injective ρ L hS h t c hc
  rw [map_one]
  apply Model.Geometry.movedAction_faithful h.sigma h.sigma_involutive h.extension_degree h.sigma_ne
  rw [map_one]
  apply LinearMap.ext
  intro X
  obtain ⟨v, rfl⟩ := (movedEquiv h t c hc).surjective X
  apply Subtype.ext
  change Model.action h.sigma h.sigma_involutive (centralizerMark ρ L hS h t c hc g).val
    (normalizedEquiv ρ L h c v.val) = normalizedEquiv ρ L h c v.val
  rw [← normalizedEquiv_centralizer]
  congr 1
  exact congrArg Subtype.val (DFunLike.congr_fun hg v)

omit [Finite G] [L.Normal] [CharP F 2] in
private lemma normalized_mem_moved {s : ℕ}
    (h : TensorIdentification (ρ.comp L.subtype) F s) (t : G) (c : Sp F)
    (hc : ∀ v : V, normalizedEquiv ρ L h c (ρ t v) =
      Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v))
    (v : V) (hv : v ∈ LinearMap.range (ρ t - LinearMap.id)) :
    normalizedEquiv ρ L h c v ∈ Model.fieldMoved h.sigma h.sigma_involutive := by
  obtain ⟨w, hw⟩ := hv
  refine ⟨normalizedEquiv ρ L h c w, ?_⟩
  change Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c w) -
    normalizedEquiv ρ L h c w = normalizedEquiv ρ L h c v
  rw [← hc, ← map_sub]
  exact congrArg (normalizedEquiv ρ L h c) hw

omit [Finite G] [L.Normal] [CharP F 2] in
private lemma middle_trivial_of_displacement {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (c : Sp F)
    (hc : ∀ v : V, normalizedEquiv ρ L h c (ρ t v) =
      Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v))
    (g : componentCentralizer L t)
    (hdisp : ∀ v ∈ fixedSpace ρ (zpowers t),
      ρ g.val v - v ∈ LinearMap.range (ρ t - LinearMap.id)) :
    middleAction h.sigma h.sigma_involutive (centralizerMark ρ L hS h t c hc g) = 1 := by
  apply LinearMap.ext
  intro X
  induction X using Submodule.Quotient.induction_on with
  | _ X =>
    change (movedInFixed h.sigma h.sigma_involutive).mkQ
      (fixedAction h.sigma h.sigma_involutive (centralizerMark ρ L hS h t c hc g) X) =
      (movedInFixed h.sigma h.sigma_involutive).mkQ X
    apply (Submodule.Quotient.eq _).mpr
    let v := (normalizedEquiv ρ L h c).symm X.val
    have he : normalizedEquiv ρ L h c v = X.val :=
      (normalizedEquiv ρ L h c).apply_symm_apply X.val
    have hv : v ∈ fixedSpace ρ (zpowers t) := by
      rw [mem_fixedSpace_zpowers_iff]
      apply (normalizedEquiv ρ L h c).injective
      rw [hc, he]
      exact sub_eq_zero.mp X.property
    have hh := normalized_mem_moved ρ L h t c hc _ (hdisp v hv)
    rw [map_sub, normalizedEquiv_centralizer ρ L hS h t c hc g v, he] at hh
    exact hh

omit [Finite G] [L.Normal] in
theorem middle_action_faithful {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (c : Sp F)
    (hc : ∀ v : V, normalizedEquiv ρ L h c (ρ t v) =
      Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v)) :
    Function.Injective (InvolutionHomology.homology ρ t (componentCentralizer L t) inf_le_right) := by
  let : CharP (SchurField (ρ.comp L.subtype)) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (SchurField (ρ.comp L.subtype))).injective 2
  apply (injective_iff_map_eq_one _).mpr
  intro g hg
  apply centralizerMark_injective ρ L hS h t c hc
  rw [map_one]
  apply Model.Geometry.middleAction_faithful h.sigma h.sigma_involutive h.extension_degree h.sigma_ne
  rw [map_one]
  have hdisp : ∀ v ∈ fixedSpace ρ (zpowers t), ρ g.val v - v ∈ LinearMap.range (ρ t - LinearMap.id) := by
    apply (sectionRepresentation_trivial_iff (ρ.comp (componentCentralizer L t).subtype)
      (InvolutionHomology.moved ρ t _ inf_le_right)
      (InvolutionHomology.fixed ρ t _ inf_le_right) g).mp
    intro x
    exact DFunLike.congr_fun hg x
  exact middle_trivial_of_displacement ρ L hS h t c hc g hdisp

/-- The field involution constructed on the original binary module. -/
def descendedSwap {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (c : Sp F) : V ≃ₗ[ZMod 2] V :=
  (normalizedEquiv ρ L h c).trans
    (((Model.fieldSwap h.sigma h.sigma_involutive).restrictScalars (ZMod 2)).trans
      (normalizedEquiv ρ L h c).symm)

omit [Finite G] [L.Normal] [CharP F 2] in
theorem descendedSwap_involutive {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (c : Sp F) : Function.Involutive (descendedSwap ρ L h c) := by
  intro v
  change (normalizedEquiv ρ L h c).symm (Model.fieldSwap h.sigma h.sigma_involutive
    (normalizedEquiv ρ L h c ((normalizedEquiv ρ L h c).symm
      (Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v))))) = v
  rw [LinearEquiv.apply_symm_apply]
  have he := DFunLike.congr_fun (Model.fieldSwap_sq h.sigma h.sigma_involutive)
    (normalizedEquiv ρ L h c v)
  change Model.fieldSwap h.sigma h.sigma_involutive
    (Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v)) =
    normalizedEquiv ρ L h c v at he
  rw [he, LinearEquiv.symm_apply_apply]

omit [CharP F 2] in
theorem outer_eq_descendedSwap {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (ht : orderOf t = 2) (hout : t ∉ L) :
    ∃ c : Sp F, ∀ v : V, ρ t v = descendedSwap ρ L h c v := by
  obtain ⟨c, hc⟩ := exists_normalized ρ L hS hs h t ht hout
  refine ⟨c, fun v => ?_⟩
  apply (normalizedEquiv ρ L h c).injective
  change normalizedEquiv ρ L h c (ρ t v) =
    normalizedEquiv ρ L h c ((normalizedEquiv ρ L h c).symm
      (Model.fieldSwap h.sigma h.sigma_involutive (normalizedEquiv ρ L h c v)))
  rw [LinearEquiv.apply_symm_apply, hc]

/-- Faithfulness on both literal original-module sections. -/
theorem outer_sections_faithful {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (ht : orderOf t = 2) (hout : t ∉ L) :
    Function.Injective (InvolutionHomology.moved ρ t (componentCentralizer L t) inf_le_right).toRepresentation ∧
    Function.Injective (InvolutionHomology.homology ρ t (componentCentralizer L t) inf_le_right) := by
  obtain ⟨c, hc⟩ := exists_normalized ρ L hS hs h t ht hout
  exact ⟨moved_action_faithful ρ L hS h t c hc, middle_action_faithful ρ L hS h t c hc⟩

omit [CharP F 2] in
/-- The displacement and fixed/displacement dimensions on the original module. -/
theorem outer_section_finranks {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (hs : 0 < s) (h : TensorIdentification (ρ.comp L.subtype) F s)
    (t : G) (ht : orderOf t = 2) (hout : t ∉ L) :
    Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) = 6 * s ∧
    Module.finrank (ZMod 2)
      ((fixedSpace ρ (zpowers t)) ⧸
        (LinearMap.range (ρ t - LinearMap.id)).comap (fixedSpace ρ (zpowers t)).subtype) = 4 * s := by
  obtain ⟨c, hc⟩ := exists_normalized ρ L hS hs h t ht hout
  have hm : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) = 6 * s := by
    rw [(movedEquiv h t c hc).finrank_eq]
    exact finrank_fieldMoved_binary h.sigma h.sigma_involutive
      h.extension_degree h.sigma_ne h.schur_card
  refine ⟨hm, ?_⟩
  have ht2 : t ^ 2 = 1 := by rw [← ht]; exact pow_orderOf_eq_one t
  have hle : LinearMap.range (ρ t - LinearMap.id) ≤ fixedSpace ρ (zpowers t) :=
    InvolutionHomology.moved_le_fixed ρ t (componentCentralizer L t) inf_le_right ht2
  have he := (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have hq := ((LinearMap.range (ρ t - LinearMap.id)).comap
    (fixedSpace ρ (zpowers t)).subtype).finrank_quotient_add_finrank
  have hf := outer_fixed_finrank ρ L hS hs h t ht hout
  omega

end
end CFSG.Quasithin.ChapterK.Symplectic.TensorGeometry.Outer.Assembly
