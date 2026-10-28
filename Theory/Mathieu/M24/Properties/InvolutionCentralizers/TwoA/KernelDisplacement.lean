module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.Quotient
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Displacement of the literal Mathieu two-central kernel

The original octad coordinates identify conjugation on the translation
four-space. The point radical therefore moves translations only along the
marked involution line. This is a structural fact about the actual native
kernel, before proving that its entire central quotient is elementary.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
open Sporadic.Mathieu.M24ChapterHStabilizers
namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoA

private def marked : centralizer2A :=
  ⟨involution2A,mem_centralizer_singleton_iff.mpr rfl⟩

private theorem marked_mem : marked∈translationKernel := markedElement_mem_core

private theorem coordinates_marked :
    (translationCoordinates (⟨marked,marked_mem⟩:translationKernel)).toAdd=markedVector := rfl

public theorem translationCoordinates_conjugation (g : centralizer2A) (u : translationKernel) :
    (translationCoordinates (MulAut.conjNormal g u)).toAdd=
      linearAction g (translationCoordinates u).toAdd := by
  have hh := OctadAction.coreCoordinates_conjugation fixedOctad (toOctad g)
    (translationEquiv.symm u)
  rw [OctadAction.naturalAction_quotientEquiv] at hh
  have he : OctadAction.coreConjugate fixedOctad (toOctad g) (translationEquiv.symm u)=
      translationEquiv.symm (MulAut.conjNormal g u) := by
    apply Subtype.ext
    rw [OctadAction.coreConjugate_coe]
    rfl
  rw [he] at hh
  exact hh

private theorem translation_mem_line (u : translationKernel)
    (hu : (translationCoordinates u).toAdd∈Submodule.span (ZMod 2) {markedVector}) :
    u.val∈zpowers marked := by
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hu
  have hc2 : c=0 ∨ c=1 := by exact (by decide : ∀c:ZMod 2,c=0∨c=1) c
  rcases hc2 with rfl | rfl
  · have he : u=1 := translationCoordinates.injective (by
      apply Multiplicative.toAdd.injective
      rw [map_one]
      change (translationCoordinates u).toAdd=0
      simpa only [zero_smul] using hc.symm)
    rw [he]
    exact one_mem _
  · have he : u=⟨marked,marked_mem⟩ := translationCoordinates.injective (by
      apply Multiplicative.toAdd.injective
      simpa only [one_smul,coordinates_marked] using hc.symm)
    rw [he]
    exact mem_zpowers _

public theorem kernel_translation_commutator_le_marked :
    ⁅kernel,translationKernel⁆≤zpowers (⟨involution2A,mem_centralizer_singleton_iff.mpr rfl⟩ : centralizer2A) := by
  apply commutator_le.mpr
  intro q hq u hu
  let u₀ : translationKernel := ⟨u,hu⟩
  let v : translationKernel := MulAut.conjNormal q u₀*u₀⁻¹
  have hv : (translationCoordinates v).toAdd∈Submodule.span (ZMod 2) {markedVector} := by
    change (translationCoordinates (MulAut.conjNormal q u₀*u₀⁻¹)).toAdd∈
      Submodule.span (ZMod 2) {markedVector}
    rw [map_mul,map_inv]
    change (translationCoordinates (MulAut.conjNormal q u₀)).toAdd+
      -(translationCoordinates u₀).toAdd∈Submodule.span (ZMod 2) {markedVector}
    rw [←sub_eq_add_neg]
    rw [translationCoordinates_conjugation]
    exact hq.2 _
  exact translation_mem_line v hv

public theorem kernel_square_mem_translation (q : kernel) :
    (q.val)^2∈translationKernel := by
  rw [←pointAction_ker,MonoidHom.mem_ker,map_pow]
  have hq : pointAction q.val∈Theory.LinearAlgebra.BinaryFivePointStabilizer.kernel markedVector := by
    apply (Theory.LinearAlgebra.BinaryFivePointStabilizer.mem_kernel_iff markedVector _).mpr
    exact q.property.2
  exact congrArg Subtype.val
    (Theory.LinearAlgebra.BinaryFivePointStabilizer.kernel_sq markedVector ⟨pointAction q.val,hq⟩)

end Sporadic.Mathieu.M24InvolutionCentralizers.TwoA
