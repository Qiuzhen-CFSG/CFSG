module

public import CFSG.Quasithin.ChapterH.Section13To16.CodeLocal.CentralizerGeometry.SectionAction
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.CentralizerGeometry.SectionAction.Kernels

/-!
# Faithfulness and the octad part of the section kernels

The native octad stabilizer acts faithfully on the five-dimensional moved
space: a pointwise fixer commutes with its self-centralizing octad two-core,
then faithfulness of the center action makes it trivial. Binary common-center
rigidity also computes the kernel of KO on Vz as precisely the cyclic group
of z. These are native action calculations used in the remaining full
centralizer-kernel identifications; they do not assert those identifications.

The literal V/V5 action and the image of W are exposed below with their
quotient equations and dimensions. Their invariant self-perpendicular form
and the full octad quotient-kernel identification imply the required
W/Vz-kernel containment. These native geometry premises remain unproved
inputs here. The Kernels owner retains their discharge and the identification
of the full Vz-kernel with an arbitrary group-theoretic supplement.

Source: Aschbacher--Smith, H.16.2, printed pp.402--403.
-/

@[expose] public section
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterH.Section13To16

/-- The actual five-space is invariant under the native octad stabilizer. -/
theorem codeOctadMoved_stable (O : Octad) :
    octadStabilizer O ≤ subspaceStabilizer MathieuCode.codeRepresentation (codeOctadMoved O) := by
  apply subspaceCommutator_invariant_normalizer MathieuCode.codeRepresentation
    (D := ⊤) (le_subspaceStabilizer _ _ (fun _ _ _ _ => Submodule.mem_top))
  rw [octadKernel, MathieuCode.octad_core_map_eq_pointwise]
  exact MathieuCode.octad_stabilizer_le_normalizer_pointwiseKernel O

/-- Faithfulness on KO extends to the entire octad stabilizer. -/
theorem codeOctadMoved_stabilizer_kernel (O : Octad) (h : CodeOctadCenterAction O) :
    subspaceKernel MathieuCode.codeRepresentation (codeOctadMoved O) (octadStabilizer O) = ⊥ := by
  apply le_antisymm _ bot_le
  intro g hg
  have hgi (v : MathieuCode.Code) (hv : v ∈ codeOctadMoved O) :
      MathieuCode.codeRepresentation g⁻¹ v = v := by
    rw [← hg.2 v hv]
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply]
    exact (hg.2 v hv).symm
  have hn : g ∈ Subgroup.normalizer (octadKernel O) := by
    rw [octadKernel, MathieuCode.octad_core_map_eq_pointwise]
    exact MathieuCode.octad_stabilizer_le_normalizer_pointwiseKernel O hg.1
  have hc (a : M24) (ha : a ∈ octadKernel O) : a * g = g * a := by
    have hast : a ∈ octadStabilizer O := by
      obtain ⟨a, _, rfl⟩ := ha
      exact a.property
    have ht : a⁻¹ * (g * a * g⁻¹) ∈
        subspaceKernel MathieuCode.codeRepresentation (codeOctadMoved O) (octadKernel O) := by
      refine ⟨(octadKernel O).mul_mem ((octadKernel O).inv_mem ha)
        ((Subgroup.mem_normalizer_iff.mp hn a).mp ha), ?_⟩
      intro v hv
      simp only [map_mul, Module.End.mul_apply]
      rw [hgi v hv, hg.2 _ ((codeOctadMoved_stable O hast v).mpr hv)]
      simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_apply]
    rw [h.faithful, Subgroup.mem_bot, inv_mul_eq_one] at ht
    exact (eq_mul_inv_iff_mul_eq.mp ht)
  have hgK : g ∈ octadKernel O := by
    change g ∈ (pCore 2 (octadStabilizer O)).map (octadStabilizer O).subtype
    let gs : octadStabilizer O := ⟨g, hg.1⟩
    have hgs : gs ∈ pCore 2 (octadStabilizer O) := by
      apply LinearFourCore.octad_core_selfCentralizing O
      intro a ha
      exact Subtype.ext (hc a.val (Subgroup.mem_map_of_mem _ ha))
    exact Subgroup.mem_map_of_mem _ hgs
  have hm : g ∈ subspaceKernel MathieuCode.codeRepresentation (codeOctadMoved O)
      (octadKernel O) := ⟨hgK, hg.2⟩
  simpa only [h.faithful] using hm

/-- The native octad kernel fixes Vz pointwise precisely through the actor z. -/
theorem codeOctadInvolutionFixed_octadKernel (O : Octad) (h : CodeOctadCenterAction O)
    (z : M24) (hz : z ∈ octadKernel O) (_hne : z ≠ 1) :
    subspaceKernel MathieuCode.codeRepresentation (codeOctadInvolutionFixed O z)
      (octadKernel O) = Subgroup.zpowers z := by
  apply le_antisymm
  · intro a ha
    by_cases ha1 : a = 1
    · exact ha1 ▸ (Subgroup.zpowers z).one_mem
    have hline : Module.finrank (ZMod 2)
        (fixedSpace MathieuCode.codeRepresentation (octadKernel O)) = 1 := by
      rw [octadKernel, MathieuCode.octad_core_map_eq_pointwise]
      exact MathieuCode.octad_fixedSpace_finrank O
    have he : z = a := by
      apply binary_center_action_eq_of_fixed_le MathieuCode.codeRepresentation (octadKernel O)
        (codeOctadMoved O) (fixedSpace MathieuCode.codeRepresentation (octadKernel O))
        hline h.displacement h.faithful z a hz ha.1 ha1
        (by intro v hv; exact ⟨hv.1, (mem_fixedSpace_zpowers_iff _ a v).mpr (ha.2 v hv)⟩)
    exact he ▸ Subgroup.mem_zpowers z
  · intro a ha
    exact ⟨Subgroup.zpowers_le.mpr hz ha, fun v hv => hv.2 ⟨a, ha⟩⟩

end CFSG.Quasithin.ChapterH.Section13To16

namespace CFSG.Quasithin.ChapterH.Section13To16

/-- The actual action of the octad stabilizer on the five-space. -/
noncomputable def codeOctadMovedLinearAction (O : Octad) :
    octadStabilizer O →* ((codeOctadMoved O) ≃ₗ[ZMod 2] (codeOctadMoved O)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (codeOctadMoved O)).toMonoidHom.comp
    ((stabilizerRepresentation MathieuCode.codeRepresentation (codeOctadMoved O)).asGroupHom.comp
      (Subgroup.inclusion (codeOctadMoved_stable O)))

/-- The linear action retains the literal native code operator. -/
theorem codeOctadMovedLinearAction_apply (O : Octad) (g : octadStabilizer O)
    (v : codeOctadMoved O) :
    (codeOctadMovedLinearAction O g v).val = MathieuCode.codeRepresentation g.val v.val := rfl

/-- Consumer: the actual linear action on V5 is faithful. -/
theorem codeOctadMovedLinearAction_injective (O : Octad) (h : CodeOctadCenterAction O) :
    Function.Injective (codeOctadMovedLinearAction O) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro g hg
  have hfix : g.val ∈ subspaceKernel MathieuCode.codeRepresentation
      (codeOctadMoved O) (octadStabilizer O) := by
    refine ⟨g.property, ?_⟩
    intro v hv
    exact congrArg Subtype.val (LinearEquiv.congr_fun (show codeOctadMovedLinearAction O g = 1 from hg)
      ⟨v, hv⟩)
  rw [codeOctadMoved_stabilizer_kernel O h, Subgroup.mem_bot] at hfix
  exact Subtype.ext hfix

/-- Consumer: the octad part of the full ambient Vz centralizer is already exact. -/
theorem codeOctadInvolutionCentralizer_inf_octadKernel
    (O : Octad) (h : CodeOctadCenterAction O) (z : M24)
    (hz : z ∈ octadKernel O) (hne : z ≠ 1) :
    octadKernel O ⊓ codeOctadInvolutionCentralizer O z = Subgroup.zpowers z := by
  rw [← codeOctadInvolutionFixed_octadKernel O h z hz hne]
  ext g
  exact ⟨fun hg => ⟨hg.1, hg.2.2⟩, fun hg => ⟨hg.1, Subgroup.mem_top _, hg.2⟩⟩

end CFSG.Quasithin.ChapterH.Section13To16

namespace CFSG.Quasithin.ChapterH.Section13To16

/-- The octad fixed line, as a subspace of its five-dimensional moved space. -/
noncomputable def codeOctadMovedLine (O : Octad) : Submodule (ZMod 2) (codeOctadMoved O) :=
  (fixedSpace MathieuCode.codeRepresentation (octadKernel O)).comap (codeOctadMoved O).subtype

/-- The five-space image is contained in the pointwise stabilizer of its fixed line. -/
theorem codeOctadMovedLinearAction_range_le (O : Octad) :
    (codeOctadMovedLinearAction O).range ≤
      fixingSubgroup ((codeOctadMoved O) ≃ₗ[ZMod 2] (codeOctadMoved O))
        (codeOctadMovedLine O : Set (codeOctadMoved O)) := by
  rintro _ ⟨g, rfl⟩
  apply (mem_fixingSubgroup_iff _).mpr
  intro v hv
  apply Subtype.ext
  change (codeOctadMovedLinearAction O g v).val = v.val
  rw [codeOctadMovedLinearAction_apply]
  have hv' : v.val ∈ fixedSpace MathieuCode.codeRepresentation (MathieuCode.octadPointwiseKernel O) := by
    change v.val ∈ fixedSpace MathieuCode.codeRepresentation (octadKernel O) at hv
    simpa only [octadKernel,
      MathieuCode.octad_core_map_eq_pointwise] using hv
  exact MathieuCode.octad_fixedSpace_le_stabilizer_fixedSpace O hv' g

theorem codeOctadMovedLine_finrank (O : Octad) (h : CodeOctadCenterAction O)
    (z : M24) (hz : z ∈ octadKernel O) (hne : z ≠ 1) :
    Module.finrank (ZMod 2) (codeOctadMovedLine O) = 1 := by
  have hle := (codeOctad_line_le_involutionFixed O h z hz hne).trans inf_le_left
  change Module.finrank (ZMod 2)
    ((fixedSpace MathieuCode.codeRepresentation (octadKernel O)).comap (codeOctadMoved O).subtype) = 1
  rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq,
    octadKernel, MathieuCode.octad_core_map_eq_pointwise]
  exact MathieuCode.octad_fixedSpace_finrank O

end CFSG.Quasithin.ChapterH.Section13To16

namespace CFSG.Quasithin.ChapterH.Section13To16

/-- The faithful five-space image has the full native octad stabilizer order. -/
theorem codeOctadMovedLinearAction_range_card (O : Octad) (h : CodeOctadCenterAction O) :
    Nat.card (codeOctadMovedLinearAction O).range = 322560 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (codeOctadMovedLinearAction_injective O h)).toEquiv]
  exact octadStabilizer_card O

end CFSG.Quasithin.ChapterH.Section13To16

namespace CFSG.Quasithin.ChapterH.Section13To16

/-- The literal octad commutator subrepresentation. -/
noncomputable def codeOctadMovedSubrepresentation (O : Octad) :
    Subrepresentation (MathieuCode.codeRepresentation.comp (octadStabilizer O).subtype) where
  toSubmodule := codeOctadMoved O
  apply_mem_toSubmodule g v hv := (codeOctadMoved_stable O g.property v).mpr hv

/-- The octad action on the literal quotient V/V5. -/
noncomputable def codeOctadQuotientRepresentation (O : Octad) :
    Representation (ZMod 2) (octadStabilizer O) (MathieuCode.Code ⧸ codeOctadMoved O) :=
  (codeOctadMovedSubrepresentation O).quotientRepresentation

/-- The same quotient acted on by the actual involution centralizer. -/
noncomputable def codeInvolutionOctadQuotientRepresentation (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hne : z ≠ 1) :
    Representation (ZMod 2) (Subgroup.centralizer ({z} : Set M24))
      (MathieuCode.Code ⧸ codeOctadMoved O) :=
  (codeOctadQuotientRepresentation O).comp
    (Subgroup.inclusion (codeInvolution_centralizer_le_octadStabilizer O z hz hne))

/-- The source three-space as the image of W in V/V5. -/
noncomputable def codeInvolutionQuotientImage (O : Octad) (z : M24) :
    Submodule (ZMod 2) (MathieuCode.Code ⧸ codeOctadMoved O) :=
  (codeInvolutionFixed z).map (codeOctadMoved O).mkQ

theorem codeOctadQuotientRepresentation_mk (O : Octad) (g : octadStabilizer O)
    (v : MathieuCode.Code) :
    codeOctadQuotientRepresentation O g ((codeOctadMoved O).mkQ v) =
      (codeOctadMoved O).mkQ (MathieuCode.codeRepresentation g.val v) := rfl

theorem codeInvolutionOctadQuotientRepresentation_mk (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hne : z ≠ 1)
    (g : Subgroup.centralizer ({z} : Set M24)) (v : MathieuCode.Code) :
    codeInvolutionOctadQuotientRepresentation O z hz hne g ((codeOctadMoved O).mkQ v) =
      (codeOctadMoved O).mkQ (MathieuCode.codeRepresentation g.val v) := rfl

/-- The three-space is invariant under the actual centralizer's quotient action. -/
theorem codeInvolutionQuotientImage_stable (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hne : z ≠ 1)
    (g : Subgroup.centralizer ({z} : Set M24))
    (v : MathieuCode.Code ⧸ codeOctadMoved O) (hv : v ∈ codeInvolutionQuotientImage O z) :
    codeInvolutionOctadQuotientRepresentation O z hz hne g v ∈ codeInvolutionQuotientImage O z := by
  obtain ⟨w, hw, rfl⟩ := hv
  exact ⟨MathieuCode.codeRepresentation g.val w,
    (codeInvolutionFixed_stable z g.property w).mpr hw, rfl⟩

/-- Literal quotient comparison: fixing the image of W is exactly displacement into Vz. -/
theorem codeInvolutionQuotientImage_fixed_iff (O : Octad) (z : M24)
    (hz : z ∈ octadKernel O) (hne : z ≠ 1)
    (g : Subgroup.centralizer ({z} : Set M24)) :
    (∀ v ∈ codeInvolutionQuotientImage O z,
      codeInvolutionOctadQuotientRepresentation O z hz hne g v = v) ↔
    ∀ w ∈ codeInvolutionFixed z,
      MathieuCode.codeRepresentation g.val w - w ∈ codeOctadInvolutionFixed O z := by
  constructor
  · intro hg w hw
    refine ⟨?_, (codeInvolutionFixed z).sub_mem
      ((codeInvolutionFixed_stable z g.property w).mpr hw) hw⟩
    exact (Submodule.Quotient.eq _).mp (hg _ ⟨w, hw, rfl⟩)
  · intro hg v hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact (Submodule.Quotient.eq _).mpr (hg w hw).1

/-- The orthogonal route to the section-kernel containment. The invariant form,
self-perpendicular image and the octad quotient-kernel identification are
explicit earlier-source premises here, to be established on the native quotient. -/
theorem codeInvolution_quotientKernel_le_core_of_orthogonal
    (O : Octad) (z : M24) (hz : z ∈ octadKernel O) (hne : z ≠ 1)
    (B : LinearMap.BilinForm (ZMod 2) (MathieuCode.Code ⧸ codeOctadMoved O))
    (hB : ∀ (g : octadStabilizer O) x y,
      B (codeOctadQuotientRepresentation O g x) (codeOctadQuotientRepresentation O g y) = B x y)
    (hI : B.orthogonal (codeInvolutionQuotientImage O z) = codeInvolutionQuotientImage O z)
    (hker : (codeOctadQuotientRepresentation O).ker = pCore 2 (octadStabilizer O))
    (g : M24) (hg : g ∈ Subgroup.centralizer ({z} : Set M24))
    (hd : ∀ w ∈ codeInvolutionFixed z,
      MathieuCode.codeRepresentation g w - w ∈ codeOctadInvolutionFixed O z) :
    g ∈ codeInvolutionCore z := by
  let C := Subgroup.centralizer ({z} : Set M24)
  let ι := Subgroup.inclusion (codeInvolution_centralizer_le_octadStabilizer O z hz hne)
  have hk : IsPGroup 2 (codeInvolutionOctadQuotientRepresentation O z hz hne).ker := by
    change IsPGroup 2 ((codeOctadQuotientRepresentation O).ker.comap ι)
    rw [hker]
    exact pCore_isPGroup.comap_of_injective ι (Subgroup.inclusion_injective _)
  have hm : (⟨g, hg⟩ : C) ∈ pCore 2 C := by
    apply pointwise_self_perp_le_pCore
      (codeInvolutionOctadQuotientRepresentation O z hz hne) B
      (codeInvolutionQuotientImage O z) hI (fun a => hB (ι a))
      (codeInvolutionQuotientImage_stable O z hz hne) hk
    exact (codeInvolutionQuotientImage_fixed_iff O z hz hne ⟨g, hg⟩).mpr hd
  exact Subgroup.mem_map_of_mem C.subtype hm

end CFSG.Quasithin.ChapterH.Section13To16

namespace CFSG.Quasithin.ChapterH.Section13To16

/-- The literal orthogonal quotient has the source dimension six. -/
theorem codeOctadQuotient_finrank (O : Octad) (h : CodeOctadCenterAction O) :
    Module.finrank (ZMod 2) (MathieuCode.Code ⧸ codeOctadMoved O) = 6 := by
  have hd := (codeOctadMoved O).finrank_quotient_add_finrank
  rw [h.moved_finrank, MathieuCode.finrank_code] at hd
  omega

/-- The actual image of W in the quotient has the source dimension three. -/
theorem codeInvolutionQuotientImage_finrank (O : Octad) (h : CodeOctadCenterAction O)
    (z : M24) (hz : z ∈ octadKernel O) (hne : z ≠ 1) :
    Module.finrank (ZMod 2) (codeInvolutionQuotientImage O z) = 3 := by
  let f : codeInvolutionFixed z →ₗ[ZMod 2] (MathieuCode.Code ⧸ codeOctadMoved O) :=
    (codeOctadMoved O).mkQ.comp (codeInvolutionFixed z).subtype
  have hr : f.range = codeInvolutionQuotientImage O z := by
    ext x
    exact ⟨fun ⟨v, hv⟩ => ⟨v.val, v.property, hv⟩,
      fun ⟨v, hv, he⟩ => ⟨⟨v, hv⟩, he⟩⟩
  have hk : f.ker = (codeOctadInvolutionFixed O z).comap (codeInvolutionFixed z).subtype := by
    ext v
    change (codeOctadMoved O).mkQ v.val = 0 ↔
      v.val ∈ codeOctadMoved O ∧ v.val ∈ codeInvolutionFixed z
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨fun hv => ⟨hv, v.property⟩, And.left⟩
  have he := (Submodule.comapSubtypeEquivOfLe
    (show codeOctadInvolutionFixed O z ≤ codeInvolutionFixed z from inf_le_right)).finrank_eq
  have hd := f.finrank_range_add_finrank_ker
  rw [hr, hk, he, codeOctadInvolutionFixed_finrank O h z hz hne,
    codeInvolutionFixed_finrank O z hz hne] at hd
  omega

end CFSG.Quasithin.ChapterH.Section13To16
