module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products.Selection
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Theory.Representation.BinaryOffender.IrreducibleTransport

/-!
# Natural component sections from the selected product rows

The ordinary B.5.6(3a) row identifies the image of [V,C] modulo C_V(D)
with the natural module. Since that module has no fixed vectors, the
projection kernel on [V,C] is exactly C_[V,C](C). The induced coordinates
therefore identify the literal component-fixed quotient.

For B.5.6(3c), perfectness gives [[V,C],C] = [V,C], hence [U,C] = [V,C]
for the specified upper space U. Equivariance of the actual projection
identifies its moved-space image with the natural moved submodule of the
four-dimensional quotient action. The same kernel argument then applies.
Both recoveries include commutator generation and require only the selected
row, the normal component, and its given PSL₃(2) isomorphism.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.6(3a,c), printed p.105, B.4.8(3), printed p.91, and the module
alternatives in 13.6.20, printed p.931.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products.NaturalSections
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {C : Subgroup D}

/-- Perfectness removes the central quotient of the second commutator space. -/
private theorem moved_generated [C.Normal] [Group.IsPerfect C] :
    subspaceCommutator ρ (moved ρ C) C = moved ρ C := by
  let J := (MovedSection.ofNormal ρ C).space
  let N := subspaceCommutator ρ J.toSubmodule C
  have hJstab : C ≤ subspaceStabilizer ρ J.toSubmodule := by
    apply le_subspaceStabilizer
    intro k hk v hv
    exact J.apply_mem_toSubmodule k hv
  have hNstab : C ≤ subspaceStabilizer ρ N :=
    subspaceCommutator_invariant_normalizer ρ hJstab C.le_normalizer
  have hNle : N ≤ J.toSubmodule := subspaceCommutator_le_of_invariant ρ hJstab
  let Nrep : Subrepresentation (ρ.comp C.subtype) :=
    ⟨N, by intro k v hv; exact (hNstab k.property v).2 hv⟩
  let qρ := Nrep.quotientRepresentation
  have hqC : subspaceCommutator qρ ⊤ (⊤ : Subgroup C) ≤ fixedSpace qρ ⊤ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, _, v, _, rfl⟩
    intro k
    induction v using Submodule.Quotient.induction_on with
    | _ w =>
      change qρ k (qρ x (Nrep.toSubmodule.mkQ w) - Nrep.toSubmodule.mkQ w) =
        qρ x (Nrep.toSubmodule.mkQ w) - Nrep.toSubmodule.mkQ w
      rw [map_sub, Subrepresentation.quotientRepresentation_mk,
        Subrepresentation.quotientRepresentation_mk]
      apply (Submodule.Quotient.eq N).mpr
      have hdJ : ρ x.val w - w ∈ J.toSubmodule :=
        Submodule.subset_span ⟨x.val, x.property, w, Submodule.mem_top, rfl⟩
      exact Submodule.subset_span
        ⟨k.val, k.val.property, ρ x.val w - w, hdJ, by
          simp only [map_sub, ← Module.End.mul_apply]
          rfl⟩
  have hqfix : (⊤ : Submodule (ZMod 2) (V ⧸ N)) ≤ fixedSpace qρ (⊤ : Subgroup C) :=
    le_fixedSpace_of_commutator_le_fixedSpace qρ (⊤ : Subgroup C) ⊤
      (le_subspaceStabilizer qρ ⊤ (by simp)) hqC
  have hJleN : J.toSubmodule ≤ N := by
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, v, _, rfl⟩
    have hfix := hqfix (show Nrep.toSubmodule.mkQ v ∈
      (⊤ : Submodule (ZMod 2) (V ⧸ N)) from by trivial)
    have hfixx := hfix ⟨⟨x, hx⟩, by simp⟩
    change Nrep.toSubmodule.mkQ (ρ x v) = Nrep.toSubmodule.mkQ v at hfixx
    apply (Submodule.Quotient.mk_eq_zero N).mp
    change Nrep.toSubmodule.mkQ (ρ x v - v) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hfixx
  exact le_antisymm hNle hJleN

/-- The natural image has no fixed vectors, so the projection kills precisely
the component-fixed vectors in the moved space. -/
private theorem natural_of_projection [C.Normal] [Group.IsPerfect C]
    (s : MovedSection ρ C)
    (E : C ≃* BinaryLinearThree.Group)
    (f : s.space.toSubmodule →ₗ[ZMod 2] BinaryLinearThree.Vector)
    (hf : Function.Surjective f)
    (hact : ∀ (g : C) v, f (s.space.toRepresentation g v) = BinaryLinearThree.W (E g) (f v))
    (hker : ∀ v, f v = 0 ↔ (v : V) ∈ ρ.invariants) : LinearThreeModuleCase ρ C := by
  have hk : s.central.toSubmodule = f.ker := by
    ext v
    rw [s.central_eq]
    change (∀ g : C, s.space.toRepresentation g v = v) ↔ f v = 0
    constructor
    · intro hv
      have hm : f v ∈ BinaryLinearThree.W.invariants := by
        intro g
        obtain ⟨g, rfl⟩ := E.surjective g
        rw [← hact, hv g]
      have hz : BinaryLinearThree.W.invariants = ⊥ :=
        ExtensionConsequences.linearNatural_invariants BinaryField.two (by decide)
      rw [hz] at hm
      exact hm
    · intro hv g
      exact Subtype.ext ((hker v).mp hv g)
  let q := s.central.toSubmodule.liftQ f hk.le
  have hq : Function.Bijective q := by
    constructor
    · apply (injective_iff_map_eq_zero _).mpr
      intro v hv
      induction v using Submodule.Quotient.induction_on with
      | _ v => exact (Submodule.Quotient.mk_eq_zero _).mpr (hk.symm ▸ hv)
    · intro w
      obtain ⟨v, rfl⟩ := hf w
      exact ⟨s.central.toSubmodule.mkQ v, rfl⟩
  refine .natural s ?_ ⟨E, LinearEquiv.ofBijective q hq, ?_⟩
  · rw [s.space_eq]
    exact moved_generated
  · intro g v
    induction v using Submodule.Quotient.induction_on with
    | _ v => exact hact g v

private noncomputable def movedProjection (s : MovedSection ρ C) (U : Subrepresentation ρ)
    (hm : moved ρ C ≤ U.toSubmodule) :
    s.space.toSubmodule →ₗ[ZMod 2] ((fixed ρ).quotientImage U).toSubmodule where
  toFun v := ⟨ρ.invariants.mkQ v, ⟨v, hm (s.space_eq ▸ v.property), rfl⟩⟩
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

private theorem movedProjection_kernel (s : MovedSection ρ C) (U : Subrepresentation ρ)
    (hm : moved ρ C ≤ U.toSubmodule) (v : s.space.toSubmodule) :
    movedProjection s U hm v = 0 ↔ (v : V) ∈ ρ.invariants := by
  constructor
  · intro h
    exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr h)

/-- The ordinary selected natural row recovers the literal component-fixed quotient. -/
theorem natural [C.Normal] (e : C ≃* Matrix.PSL3Two.PSL)
    (c : SelectedTwoFactorCase ρ C) (hm : c.space.toSubmodule = moved ρ C)
    (a : ActionEquiv (((fixed ρ).quotientImage c.space).toRepresentation.comp C.subtype)
      BinaryLinearThree.W) : LinearThreeModuleCase ρ C := by
  let : IsQuasisimple C := component_quasisimple e
  let s := MovedSection.ofNormal ρ C
  let p := movedProjection s c.space hm.ge
  have hp : Function.Surjective p := by
    rintro ⟨w, v, hv, rfl⟩
    exact ⟨⟨v, s.space_eq.symm ▸ (hm ▸ hv)⟩, rfl⟩
  apply natural_of_projection s a.groupEquiv (a.linearEquiv.toLinearMap.comp p)
    (a.linearEquiv.surjective.comp hp)
  · intro g v
    exact a.intertwines g (p v)
  · intro v
    exact (a.linearEquiv.map_eq_zero_iff).trans (movedProjection_kernel s c.space hm.ge v)

/-- Commutator transport computes the image inside the specified quotient summand. -/
private theorem movedProjection_range [C.Normal] [Group.IsPerfect C]
    (s : MovedSection ρ C) (U : Subrepresentation ρ)
    (hm : moved ρ C ≤ U.toSubmodule) :
    (movedProjection s U hm).range =
      moved (((fixed ρ).quotientImage U).toRepresentation.comp C.subtype) ⊤ := by
  let B := (fixed ρ).quotientImage U
  let Q := B.toRepresentation.comp C.subtype
  let τ := (fixed ρ).quotientRepresentation.comp C.subtype
  have hmU : subspaceCommutator ρ U.toSubmodule C = moved ρ C := by
    apply le_antisymm (subspaceCommutator_mono_left ρ le_top C)
    exact (moved_generated (ρ := ρ) (C := C)).ge.trans
      (subspaceCommutator_mono_left ρ hm C)
  have he := subspaceCommutator_map_embedding τ ρ C.subtype ρ.invariants.mkQ
    (fun _ _ => rfl) ⊤ U.toSubmodule
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype, hmU] at he
  have hb := subspaceCommutator_map_embedding τ Q (MonoidHom.id C) B.toSubmodule.subtype
    (fun _ _ => rfl) ⊤ ⊤
  rw [Submodule.map_top, Submodule.range_subtype, Subgroup.map_id] at hb
  apply Submodule.map_injective_of_injective B.toSubmodule.subtype_injective
  change (movedProjection s U hm).range.map B.toSubmodule.subtype =
    (moved Q ⊤).map B.toSubmodule.subtype
  have hh : (movedProjection s U hm).range.map B.toSubmodule.subtype =
      (moved ρ C).map ρ.invariants.mkQ := by
    rw [← Submodule.map_top (movedProjection s U hm), ← Submodule.map_comp]
    change (⊤ : Submodule (ZMod 2) s.space.toSubmodule).map
      (ρ.invariants.mkQ.comp s.space.toSubmodule.subtype) = _
    rw [Submodule.map_comp, Submodule.map_top, Submodule.range_subtype, s.space_eq]
  exact hh.trans (he.symm.trans hb)

/-- In the exceptional row the projection of the actual moved space is precisely
its natural three-dimensional submodule. -/
theorem exceptional_image [C.Normal] (e : C ≃* Matrix.PSL3Two.PSL)
    (c : SelectedTwoFactorCase ρ C)
    (hm : moved ρ C ≤ c.space.toSubmodule)
    (extension : FourDimensionalSource
      (((fixed ρ).quotientImage c.space).toRepresentation.comp C.subtype)) :
    (moved ρ C).map ρ.invariants.mkQ =
      extension.space.toSubmodule.map ((fixed ρ).quotientImage c.space).toSubmodule.subtype := by
  let : IsQuasisimple C := component_quasisimple e
  let s := MovedSection.ofNormal ρ C
  have h := congrArg
    (Submodule.map ((fixed ρ).quotientImage c.space).toSubmodule.subtype)
    (movedProjection_range s c.space hm)
  rw [← extension.space_eq] at h
  rw [← Submodule.map_top (movedProjection s c.space hm), ← Submodule.map_comp] at h
  change (⊤ : Submodule (ZMod 2) s.space.toSubmodule).map
    (ρ.invariants.mkQ.comp s.space.toSubmodule.subtype) = _ at h
  rw [Submodule.map_comp, Submodule.map_top, Submodule.range_subtype, s.space_eq] at h
  exact h

/-- B.5.6(3c) recovers the natural quotient by the component's own fixed space. -/
theorem exceptional [C.Normal] (e : C ≃* Matrix.PSL3Two.PSL)
    (c : SelectedTwoFactorCase ρ C) (hm : moved ρ C ≤ c.space.toSubmodule)
    (extension : FourDimensionalSource
      (((fixed ρ).quotientImage c.space).toRepresentation.comp C.subtype)) :
    LinearThreeModuleCase ρ C := by
  let : IsQuasisimple C := component_quasisimple e
  let s := MovedSection.ofNormal ρ C
  let p := movedProjection s c.space hm
  have hr : p.range = extension.space.toSubmodule :=
    (movedProjection_range s c.space hm).trans extension.space_eq.symm
  let f : s.space.toSubmodule →ₗ[ZMod 2] extension.space.toSubmodule :=
    p.codRestrict extension.space.toSubmodule (fun v => hr ▸ p.mem_range_self v)
  have hf : Function.Surjective f := by
    intro w
    have hw : (w : ((fixed ρ).quotientImage c.space).toSubmodule) ∈ p.range := by
      rw [hr]
      exact w.property
    obtain ⟨v, hv⟩ := hw
    exact ⟨v, Subtype.ext hv⟩
  let a : ActionEquiv extension.space.toRepresentation BinaryLinearThree.W :=
    ⟨extension.natural.groupEquiv, extension.natural.linearEquiv,
      fun g v => extension.natural.intertwines g v⟩
  apply natural_of_projection s a.groupEquiv
    (a.linearEquiv.toLinearMap.comp f)
    (a.linearEquiv.surjective.comp hf)
  · intro g v
    exact a.intertwines g (f v)
  · intro v
    change a.linearEquiv (f v) = 0 ↔ _
    rw [a.linearEquiv.map_eq_zero_iff]
    exact ⟨fun h => (movedProjection_kernel s c.space hm v).mp (congrArg Subtype.val h),
      fun h => Subtype.ext ((movedProjection_kernel s c.space hm v).mpr h)⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.LinearThree.CentralAction.ModuleAlternatives.Classifier.Products.NaturalSections
