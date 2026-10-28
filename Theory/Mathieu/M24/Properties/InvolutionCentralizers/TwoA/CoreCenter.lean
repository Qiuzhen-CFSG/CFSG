module
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.Quotient

/-!
# The center of the intrinsic M₂₄ two-central core

A central element of the actual two-core centralizes the octad translation
kernel and therefore belongs to that kernel. Its translation coordinate is
fixed by the entire point radical, hence lies on the marked involution line.
This gives an injection of the core center into a binary line and bounds its
order by two, without a presentation or splitting assumption.

Source: GLS3 Table 5.3e. The irreducible-section comparison in the original
Aschbacher--Smith 10.2.9, printed pp.750--751, consumes this bound.
-/

public section
open Subgroup
open Sporadic.Mathieu.M24ChapterHStabilizers
namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoA
noncomputable section
private def centerTranslation (z : center kernel) : translationKernel :=
  ⟨z.val.val, translationKernel_selfCentralizing (by
    intro u hu
    exact congrArg Subtype.val (mem_center_iff.mp z.property
      ⟨u,translationKernel_le_kernel hu⟩))⟩
private theorem centerTranslation_fixed (z : center kernel) (g : kernel) :
    linearAction g.val (translationCoordinates (centerTranslation z)).toAdd =
      (translationCoordinates (centerTranslation z)).toAdd := by
  let a := translationEquiv.symm (centerTranslation z)
  have he : OctadAction.coreConjugate fixedOctad (toOctad g.val) a = a := by
    apply Subtype.ext
    rw [OctadAction.coreConjugate_coe]
    apply Subtype.ext
    change g.val.val * z.val.val.val * g.val.val⁻¹ = z.val.val.val
    exact mul_inv_eq_iff_eq_mul.mpr
      (congrArg (fun u : kernel => u.val.val) (mem_center_iff.mp z.property g))
  have hh := OctadAction.coreCoordinates_conjugation fixedOctad (toOctad g.val) a
  rw [he,OctadAction.naturalAction_quotientEquiv] at hh
  exact hh.symm
private theorem centerTranslation_mem_line (z : center kernel) :
    (translationCoordinates (centerTranslation z)).toAdd ∈
      Submodule.span (ZMod 2) {markedVector} := by
  apply (BinaryLinear.mem_iff_fixed_radical (by
    intro h
    apply markedVector_ne_zero
    exact (Submodule.span_singleton_eq_bot (R := ZMod 2) (x := markedVector)).mp h) _).mpr
  intro r hr
  have hrfix : r markedVector = markedVector :=
    hr.1 _ (Submodule.mem_span_singleton_self _)
  have hrange : r ∈ linearAction.range := by
    rw [linearAction_range]
    exact hrfix
  obtain ⟨g,hg⟩ := hrange
  have hgk : g ∈ kernel := by change linearAction g ∈ BinaryLinear.radical _; rwa [hg]
  simpa only [hg] using centerTranslation_fixed z ⟨g,hgk⟩
private def centerLine (z : center kernel) : Submodule.span (ZMod 2) {markedVector} :=
  ⟨(translationCoordinates (centerTranslation z)).toAdd,centerTranslation_mem_line z⟩
attribute [local irreducible] translationCoordinates markedVector
private theorem centerLine_injective : Function.Injective centerLine := by
  intro x y h
  have hv : (translationCoordinates (centerTranslation x)).toAdd =
      (translationCoordinates (centerTranslation y)).toAdd := congrArg (fun z : Submodule.span (ZMod 2) {markedVector} => (z : OctadAction.Space)) h
  have hm : translationCoordinates (centerTranslation x) =
      translationCoordinates (centerTranslation y) := Multiplicative.toAdd.injective hv
  have ht : centerTranslation x = centerTranslation y := translationCoordinates.injective hm
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : translationKernel => (z : centralizer2A)) ht

theorem core_center_card_le_two : Nat.card (center (pCore 2 centralizer2A)) ≤ 2 := by
  rw [←kernel_eq_twoCore]
  let coeff : Submodule.span (ZMod 2) {markedVector} → ZMod 2 := fun z =>
    Classical.choose (Submodule.mem_span_singleton.mp z.property)
  have coeff_spec (z : Submodule.span (ZMod 2) {markedVector}) :
      coeff z • markedVector = z := Classical.choose_spec (Submodule.mem_span_singleton.mp z.property)
  have coeff_inj : Function.Injective coeff := by
    intro x y hxy
    apply Subtype.ext
    rw [← coeff_spec x, ← coeff_spec y, hxy]
  have hline : Nat.card (Submodule.span (ZMod 2) {markedVector}) ≤ 2 := by
    have hh := Nat.card_le_card_of_injective coeff coeff_inj
    simpa only [Nat.card_zmod] using hh
  exact (Nat.card_le_card_of_injective centerLine centerLine_injective).trans hline
end
end Sporadic.Mathieu.M24InvolutionCentralizers.TwoA
