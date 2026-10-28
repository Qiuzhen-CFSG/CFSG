module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Involutions.AmbientContainment.ScalarExtension
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Involutions.AmbientContainment.TensorRigidity
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Involutions.Native
public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.TensorGeometry.Outer.Bounds

/-!
# Ambient tensor displacement fixers belong to the component

Fixing a nonzero component-involution displacement forces an ambient actor to
be linear over the actual Schur field. Extend this operator through the given
tensor identification and apply tensor normalizer rigidity. Its action on the
component is inner, and the source generalized-Fitting hypothesis with the
centerless symplectic model forces the ambient element into the component.

This proves containment for every ambient pointwise fixer, hence for the
specified Sylow fixer. For non-b₁ involutions, native freeness identifies the
fixed-space and displacement fixers in the original binary representation.
Diagram preservation is the permitted explicit premise; no component-fixer
order calculation is used.

Source: Aschbacher–Smith, K.3.4.2, printed p.457 (PDF p.468).
-/

public section
open Representation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterK.Symplectic
open Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open TensorGeometry.AmbientContainment
variable {G V F : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  [IsIrreducible (ρ.comp L.subtype)] [Field F]
  [Algebra (SchurField (ρ.comp L.subtype)) F]

/-- Ambient pointwise fixers of component-involution displacements belong to the
component. Normality is derived from the genuine generalized-Fitting hypothesis. -/
theorem TensorIdentification.displacement_fixer_mem_component
    {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s)
    (hdiagram :
      letI : L.Normal := by
        let : Finite G := hS.finite_group
        rw [← hS.fitting]
        infer_instance
      ∀ g : G, PreservesDiagram (extensionAction L h.groupEquiv.symm g))
    (j : G) (hjL : j ∈ L) (hj : orderOf j = 2) (g : G)
    (hfix : ∀ v, ρ g (displacement ρ j v) = displacement ρ j v) : g ∈ L := by
  let : Finite G := hS.finite_group
  let : L.Normal := by rw [← hS.fitting]; infer_instance
  let : Finite F := Nat.finite_of_card_ne_zero (h.field_card ▸ pow_ne_zero _ (by decide))
  let : CharP (SchurField (ρ.comp L.subtype)) 2 := charP_of_injective_algebraMap
    (algebraMap (ZMod 2) (SchurField (ρ.comp L.subtype))).injective 2
  let : CharP F 2 := charP_of_injective_algebraMap
    (algebraMap (SchurField (ρ.comp L.subtype)) F).injective 2
  have hlin : Representation.IsSchurLinear ρ L g :=
    displacement_fixer_isSchurLinear ρ L hS.faithful j hjL
      (by intro he; simp [he] at hj) g hfix
  have hin : extensionAction L h.groupEquiv.symm g ∈ MulAut.innerSubgroup (Sp F) := by
    apply tensor_fixer_inner (ρ.comp L.subtype) h _ (hdiagram g)
      (tensorActor ρ L h g hlin) (tensorActor_intertwines ρ L h g hlin)
      (h.groupEquiv ⟨j, hjL⟩)
    · exact (h.groupEquiv.orderOf_eq _).trans
        ((Subgroup.orderOf_coe (⟨j, hjL⟩ : L)).symm.trans hj)
    · exact tensorActor_fixes_displacement ρ L h ⟨j, hjL⟩ g hlin hfix
  exact (TensorGeometry.Outer.extensionAction_mem_inner_iff L h.groupEquiv.symm
    (TensorGeometry.Outer.component_centralizer_eq_bot ρ L hS h.groupEquiv.symm) g).mp hin

/-- The literal Sylow pointwise displacement fixer in K.3.4.2 lies in L.
This needs neither a numerical fixer bound nor the component-fixer calculation. -/
theorem TensorIdentification.component_displacementKernel_le
    {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s) (_hs : 0 < s)
    (hdiagram :
      letI : L.Normal := by
        let : Finite G := hS.finite_group
        rw [← hS.fitting]
        infer_instance
      ∀ g : G, PreservesDiagram (extensionAction L h.groupEquiv.symm g))
    (T : Sylow 2 G) (j : G) (_hjT : j ∈ T) (hjL : j ∈ L) (hj : orderOf j = 2) :
    subspaceKernel ρ (LinearMap.range (displacement ρ j)) T ≤ L := by
  intro g hg
  apply h.displacement_fixer_mem_component hS hdiagram j hjL hj g
  intro v
  exact hg.2 _ ⟨v, rfl⟩

/-- For a₂ and c₂ the intrinsic freeness equality identifies fixed-space and
displacement fixers, on the original binary representation. -/
theorem TensorIdentification.component_nonB1_fixedKernel_le
    {K : GroupClass} (hS : SourceHypothesis K ρ L)
    {s : ℕ} (h : TensorIdentification (ρ.comp L.subtype) F s) (hs : 0 < s)
    (hdiagram :
      letI : L.Normal := by
        let : Finite G := hS.finite_group
        rw [← hS.fitting]
        infer_instance
      ∀ g : G, PreservesDiagram (extensionAction L h.groupEquiv.symm g))
    (T : Sylow 2 G) (j : G) (hjT : j ∈ T) (hjL : j ∈ L) (hj : orderOf j = 2)
    (hB : ¬ InvolutionTypes.IsB1 (h.groupEquiv ⟨j, hjL⟩)) :
    subspaceKernel ρ (fixedSpace ρ (Subgroup.zpowers j)) T ≤ L := by
  let : Finite G := hS.finite_group
  rw [h.component_nonB1_fixedSpace_eq_displacement ρ L j hjL hj hB]
  exact h.component_displacementKernel_le hS hs hdiagram T j hjT hjL hj
end CFSG.Quasithin.ChapterK.Symplectic
