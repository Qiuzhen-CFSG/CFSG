module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Defs
public import Theory.Mathieu.M24.ChapterHStabilizers.OctadAction
public import Theory.SpecificGroups.BinaryLinear.Parabolics

/-!
# The marked 2A centralizer and its binary point radical

The fixed octad of the marked involution places its full centralizer inside
an octad stabilizer. The pointwise octad kernel is a normal elementary group
of order sixteen, and remains self-centralizing after this restriction.
The octad conjugation coordinates identify the centralizer image with the
full stabilizer of the nonzero vector representing the involution.
Pulling back the radical of that vector's line gives a specified normal,
self-centralizing two-subgroup of the actual centralizer.

The dihedral central-product structure of this larger kernel and its
PSL3(2) quotient are separate obligations; neither follows from the kernel
properties proved here.

Source: Aschbacher–Smith, 16.1.5(7), printed p.1171, and GLS3 Table 5.3e.
-/

@[expose] public section
noncomputable section

open Subgroup
open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Sporadic.Mathieu.M24ChapterHStabilizers
open MathieuCode
open scoped Pointwise IsMulCommutative

namespace Sporadic.Mathieu.M24InvolutionCentralizers.TwoA

/-- The actual octad fixed pointwise by the marked 2A involution. -/
def fixedOctad : Octad := ⟨m24BlockAt 0,
  Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩

theorem fixed_iff (a : Fin 24) : involution2A • a = a ↔ a ∈ fixedOctad.val := by
  revert a
  decide +kernel

/-- Every element of the full centralizer preserves its fixed octad. -/
theorem centralizer_le_octad : centralizer2A ≤ octadStabilizer fixedOctad := by
  intro g hg
  apply MulAction.mem_stabilizer_finset'.mpr
  intro a ha
  apply (fixed_iff _).mp
  have hc := congrArg (fun x : M24 => x • a) (mem_centralizer_singleton_iff.mp hg)
  simpa only [mul_smul, (fixed_iff a).mpr ha] using hc.symm

/-- Inclusion of the literal centralizer into its octad stabilizer. -/
def toOctad : centralizer2A →* octadStabilizer fixedOctad :=
  inclusion centralizer_le_octad

/-- The marked involution as an element of the octad stabilizer. -/
def markedElement : octadStabilizer fixedOctad :=
  ⟨involution2A, centralizer_le_octad (mem_centralizer_singleton_iff.mpr rfl)⟩

theorem markedElement_mem_core : markedElement ∈ OctadAction.Core fixedOctad := by
  rw [OctadAction.Core, CocodeOctad.core_eq_coordinateKernel,
    CocodeOctad.mem_coordinateAction_ker]
  exact fun a ha => (fixed_iff a).mpr ha

/-- The involution in the genuine elementary octad kernel. -/
def markedTranslation : OctadAction.Core fixedOctad :=
  ⟨markedElement, markedElement_mem_core⟩

/-- Restrict the intrinsic octad kernel to the actual centralizer. -/
abbrev translationKernel : Subgroup centralizer2A :=
  (OctadAction.Core fixedOctad).comap toOctad

/-- All octad translations centralize the marked translation. -/
def translationInclusion : OctadAction.Core fixedOctad →* centralizer2A where
  toFun u := ⟨u.val.val, mem_centralizer_singleton_iff.mpr (by
    let : IsElementaryAbelian 2 (OctadAction.Core fixedOctad) :=
      (LinearFourCore.octad_core_structure fixedOctad).2
    exact congrArg (fun a : OctadAction.Core fixedOctad => a.val.val)
      (mul_comm u markedTranslation))⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Restriction loses none of the order-sixteen kernel. -/
def translationEquiv : OctadAction.Core fixedOctad ≃* translationKernel where
  toFun u := ⟨translationInclusion u, u.property⟩
  invFun u := ⟨toOctad u.val, u.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- Explicit binary additive coordinates on this subgroup of the centralizer. -/
def translationCoordinates : translationKernel ≃* Multiplicative OctadAction.Space :=
  translationEquiv.symm.trans (OctadAction.coreCoordinates fixedOctad)

theorem translationKernel_card : Nat.card translationKernel = 16 :=
  (Nat.card_congr translationEquiv.symm.toEquiv).trans (OctadAction.core_card fixedOctad)

theorem translationKernel_isTwoGroup : IsPGroup 2 translationKernel :=
  pCore_isPGroup.of_surjective translationEquiv.toMonoidHom translationEquiv.surjective

theorem translationKernel_selfCentralizing :
    centralizer (translationKernel : Set centralizer2A) ≤ translationKernel := by
  intro g hg
  apply LinearFourCore.octad_core_selfCentralizing fixedOctad
  intro u hu
  exact congrArg toOctad
    (hg (translationInclusion ⟨u, hu⟩)
      (show translationInclusion ⟨u, hu⟩ ∈ translationKernel from hu))

/-- The marked involution in the natural binary four-space. -/
def markedVector : OctadAction.Space :=
  (OctadAction.coreCoordinates fixedOctad markedTranslation).toAdd

theorem markedVector_ne_zero : markedVector ≠ 0 := by
  intro h
  have h1 : markedTranslation = 1 := (OctadAction.coreCoordinates fixedOctad).injective
    (show OctadAction.coreCoordinates fixedOctad markedTranslation =
      OctadAction.coreCoordinates fixedOctad 1 by
        rw [map_one]; exact h)
  have he : involution2A = 1 := congrArg
    (fun a : OctadAction.Core fixedOctad => a.val.val) h1
  have ho := involution2A_order
  rw [he, orderOf_one] at ho
  omega

/-- Conjugation on the order-sixteen kernel, in the existing natural coordinates. -/
def linearAction : centralizer2A →* BinaryLinear.GL OctadAction.Space :=
  (OctadAction.linearAction fixedOctad).comp toOctad

theorem linearAction_ker : linearAction.ker = translationKernel := by
  change (OctadAction.linearAction fixedOctad).ker.comap toOctad = _
  rw [OctadAction.linearAction_ker]

/-- The marked vector is fixed exactly by elements centralizing the involution. -/
theorem fixes_markedVector_iff (g : octadStabilizer fixedOctad) :
    OctadAction.linearAction fixedOctad g markedVector = markedVector ↔
      g.val ∈ centralizer2A := by
  have h := OctadAction.coreCoordinates_conjugation fixedOctad g markedTranslation
  rw [OctadAction.naturalAction_quotientEquiv] at h
  change OctadAction.linearAction fixedOctad g
    (OctadAction.coreCoordinates fixedOctad markedTranslation).toAdd = _ ↔ _
  rw [← h]
  change (OctadAction.coreCoordinates fixedOctad _).toAdd =
    (OctadAction.coreCoordinates fixedOctad markedTranslation).toAdd ↔ _
  rw [Multiplicative.toAdd.injective.eq_iff,
    (OctadAction.coreCoordinates fixedOctad).injective.eq_iff]
  constructor
  · intro he
    have hc := congrArg (fun a : OctadAction.Core fixedOctad => a.val) he
    rw [OctadAction.coreConjugate_coe] at hc
    have hm : g.val * involution2A * g.val⁻¹ = involution2A := congrArg Subtype.val hc
    exact mem_centralizer_singleton_iff.mpr ((mul_inv_eq_iff_eq_mul).mp hm)
  · intro hg
    apply Subtype.ext
    rw [OctadAction.coreConjugate_coe]
    apply Subtype.ext
    exact (mul_inv_eq_iff_eq_mul).mpr (mem_centralizer_singleton_iff.mp hg)

/-- The full vector stabilizer is attained, not merely a subgroup of its order. -/
theorem linearAction_range :
    linearAction.range = MulAction.stabilizer (BinaryLinear.GL OctadAction.Space) markedVector := by
  ext a
  constructor
  · rintro ⟨g, rfl⟩
    exact (fixes_markedVector_iff (toOctad g)).mpr g.property
  · intro ha
    obtain ⟨g, rfl⟩ := OctadAction.linearAction_surjective fixedOctad a
    exact ⟨⟨g.val, (fixes_markedVector_iff g).mp ha⟩, rfl⟩

/-- The source kernel is specified as the preimage of the marked point radical. -/
def kernel : Subgroup centralizer2A :=
  (BinaryLinear.radical (Submodule.span (ZMod 2) {markedVector})).comap linearAction

theorem translationKernel_le_kernel : translationKernel ≤ kernel := by
  rw [← linearAction_ker]
  intro g hg
  change linearAction g ∈ BinaryLinear.radical _
  rw [MonoidHom.mem_ker.mp hg]
  exact one_mem _

theorem kernel_isTwoGroup : IsPGroup 2 kernel :=
  (BinaryLinear.radical_two _).comap_of_ker_isPGroup linearAction
    (linearAction_ker.symm ▸ translationKernel_isTwoGroup)

theorem linearAction_mem_parabolic (g : centralizer2A) :
    linearAction g ∈ BinaryLinear.parabolic (Submodule.span (ZMod 2) {markedVector}) := by
  have h : linearAction g markedVector = markedVector :=
    (fixes_markedVector_iff (toOctad g)).mpr g.property
  have hf (a : BinaryLinear.GL OctadAction.Space) (ha : a markedVector = markedVector)
      (v : OctadAction.Space) (hv : v ∈ Submodule.span (ZMod 2) {markedVector}) :
      a v ∈ Submodule.span (ZMod 2) {markedVector} := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, ha]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  intro v
  constructor
  · intro hv
    have hi : (linearAction g)⁻¹ markedVector = markedVector := by
      apply (linearAction g).injective
      simpa using h.symm
    simpa using hf (linearAction g)⁻¹ hi _ hv
  · exact hf (linearAction g) h v

instance kernel_normal : kernel.Normal where
  conj_mem n hn g := by
    change linearAction (g * n * g⁻¹) ∈ BinaryLinear.radical _
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.mp
      (BinaryLinear.parabolic_le_normalizer _ (linearAction_mem_parabolic g)) _).mp hn

/-- The specified larger two-kernel is self-centralizing in the actual centralizer. -/
theorem kernel_selfCentralizing : centralizer (kernel : Set centralizer2A) ≤ kernel :=
  (centralizer_le translationKernel_le_kernel).trans
    (translationKernel_selfCentralizing.trans translationKernel_le_kernel)

/-- The representative satisfies the exact kernel-action input of the M24 table. -/
theorem exists_normal_selfCentralizing_twoKernel :
    ∃ Q : Subgroup centralizer2A,
      Q.Normal ∧ IsPGroup 2 Q ∧ centralizer (Q : Set centralizer2A) ≤ Q :=
  ⟨kernel, inferInstance, kernel_isTwoGroup, kernel_selfCentralizing⟩

end Sporadic.Mathieu.M24InvolutionCentralizers.TwoA
