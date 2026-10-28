module
public import Theory.Mathieu.M22.Properties.HexadSplitCoordinates.Splitting
public import Theory.Mathieu.M22.ChapterHLocalClassification.HexadAction

/-!
# Marked natural coordinates for native degree-22 hexad kernels

The Chapter H source octad is exactly the augmentation of the native hexad
`m22Hexad24Ten`. The original M22 embedding therefore identifies their actual
stabilizers and kernels. Conjugating any hexad to this marked one transports
the proved natural coordinates and their conjugation equation.

The natural quotient marking and the original six-point quotient marking
are compared by an explicit automorphism of A6. The map `comparison` retains
both literal quotient equivalences; no abstract identification from orders
or an unmarked representation comparison is used.

Source: Aschbacher--Smith, I.2.2(6), printed p.412 (PDF p.423), using the
native hexad natural action H.14.3(3), printed p.397 (PDF p.408).
-/

@[expose] public section
noncomputable section
namespace Sporadic.Mathieu.M22HexadCoordinates
open scoped Pointwise
open MathieuCode M22ChapterH.Hexad
open MathieuCode.Hexad.CocodeAction.SixPointModel

/-- The degree-22 hexad underlying the source octad used for the natural action. -/
abbrev base := m22Hexad24Ten

theorem base_augmented : m22AugmentedOctad base = O.val := by
  rw [m22AugmentedOctad_eq]
  decide +kernel

private theorem coordinate_ne_pair (a : Fin 22) :
    m22Coordinates a ≠ 0 ∧ m22Coordinates a ≠ 9 := by
  revert a
  decide +kernel

theorem mem_augmented_coordinate (B : Finset (Fin 22)) (a : Fin 22) :
    m22Coordinates a ∈ m22AugmentedOctad B ↔ a ∈ B := by
  rw [mem_m22AugmentedOctad]
  simp only [(coordinate_ne_pair a).1, (coordinate_ne_pair a).2, false_or,
    m22Coordinates.injective.eq_iff, exists_eq_right]

theorem augmented_injective : Function.Injective m22AugmentedOctad := by
  intro B C h
  ext a
  rw [← mem_augmented_coordinate B a, h, mem_augmented_coordinate]

/-- Equality of the literal stabilizers, via the native M22 embedding in M24. -/
theorem base_stabilizer : MulAction.stabilizer M22 base = Action.Inner := by
  ext g
  change g • base = base ↔ m22Embedding g • O.val = O.val
  rw [← base_augmented, ← m22AugmentedOctad_smul, augmented_injective.eq_iff]

/-- The ambient pointwise kernel is the already identified intrinsic inner core. -/
theorem base_kernel : m22HexadPointwiseKernel base = m22InnerHexadKernel O := by
  ext g
  constructor
  · intro hg
    have hi : m22Embedding g ∈ octadPointwiseKernel O := by
      have ho : m22Octad m22Hexad24Ten_mem = O := Subtype.ext base_augmented
      rw [← ho, ← m22HexadPointwiseKernel_map m22Hexad24Ten_mem]
      exact Subgroup.mem_map_of_mem _ hg
    rw [← inner_kernel_image] at hi
    obtain ⟨u, hu, he⟩ := hi
    exact m22Embedding_injective he ▸ hu
  · intro hg
    have hi : m22Embedding g ∈ octadPointwiseKernel (m22Octad m22Hexad24Ten_mem) := by
      have ho : m22Octad m22Hexad24Ten_mem = O := Subtype.ext base_augmented
      rw [ho, ← inner_kernel_image]
      exact Subgroup.mem_map_of_mem _ hg
    rw [← m22HexadPointwiseKernel_map m22Hexad24Ten_mem] at hi
    obtain ⟨u, hu, he⟩ := hi
    exact m22Embedding_injective he ▸ hu

/-- Every native hexad is a translate of the marked base hexad. -/
theorem exists_base_conjugator {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    ∃ g : M22, g • base = B := by
  obtain ⟨u, hu⟩ := exists_smul_m22Hexad123_eq m22Hexad24Ten_mem
  obtain ⟨v, hv⟩ := exists_smul_m22Hexad123_eq hB
  refine ⟨v * u⁻¹, ?_⟩
  rw [mul_smul, show base = u • m22Hexad123 from hu.symm, inv_smul_smul, hv]

/-- Actual conjugation transporting a native hexad stabilizer to the marked one. -/
def stabilizerEquiv {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    MulAction.stabilizer M22 B ≃* Action.Inner :=
  (MulAction.stabilizerEquivStabilizer
    (Classical.choose_spec (exists_base_conjugator hB)).symm).symm.trans
      (MulEquiv.subgroupCongr base_stabilizer)

/-- This transport is literal ambient conjugation. -/
theorem stabilizerEquiv_coe {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (x : MulAction.stabilizer M22 B) :
    (stabilizerEquiv hB x).val =
      MulAut.conj (Classical.choose (exists_base_conjugator hB))⁻¹ x.val := rfl

/-- The actual pointwise kernel transports to the intrinsic two-core. -/
theorem kernel_iff {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (x : MulAction.stabilizer M22 B) :
    x ∈ (m22SetAction B).ker ↔ stabilizerEquiv hB x ∈ pCore 2 Action.Inner := by
  rw [← inner_kernel_eq_core, innerCoordinateAction_ker inner_kernel_image]
  change x ∈ (m22SetAction B).ker ↔ (stabilizerEquiv hB x).val ∈ m22InnerHexadKernel O
  rw [← base_kernel, mem_m22HexadPointwiseKernel, mem_m22SetAction_ker, stabilizerEquiv_coe]
  let g := Classical.choose (exists_base_conjugator hB)
  have hg : g • base = B := Classical.choose_spec (exists_base_conjugator hB)
  constructor
  · intro hx a ha
    have hf := hx (g • a) (hg ▸ Finset.smul_mem_smul_finset ha)
    change (g⁻¹ * x.val * (g⁻¹)⁻¹) • a = a
    simp only [mul_smul, inv_inv, hf, inv_smul_smul]
  · intro hx a ha
    have ha' : g⁻¹ • a ∈ base := by
      have : a ∈ g • base := hg ▸ ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_smul_finset.mp this
      simpa only [inv_smul_smul] using hb
    have hf := congrArg (fun b : Fin 22 => g • b) (hx (g⁻¹ • a) ha')
    simpa only [g, MulAut.conj_apply, mul_smul, inv_inv, smul_inv_smul] using hf

/-- Natural marking on the actual stabilizer, through the established native bridge. -/
def naturalMap {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    MulAction.stabilizer M22 B →* alternatingGroup (Fin 6) :=
  Action.Natural.innerMap.comp (stabilizerEquiv hB).toMonoidHom

theorem naturalMap_surjective {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Function.Surjective (naturalMap hB) :=
  Action.Natural.innerMap_surjective.comp (stabilizerEquiv hB).surjective

theorem naturalMap_ker {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (naturalMap hB).ker = (m22SetAction B).ker := by
  ext g
  change Action.Natural.innerMap (stabilizerEquiv hB g) = 1 ↔ _
  rw [← MonoidHom.mem_ker, Action.Natural.innerMap_ker, ← kernel_iff hB]

/-- Coordinates on the literal kernel, before the natural-module comparison. -/
def coreEquiv {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (m22SetAction B).ker ≃* pCore 2 Action.Inner where
  toFun u := ⟨stabilizerEquiv hB u.val, (kernel_iff hB u.val).mp u.property⟩
  invFun u := ⟨(stabilizerEquiv hB).symm u.val, (kernel_iff hB _).mpr
    (by simpa only [MulEquiv.apply_symm_apply] using u.property)⟩
  left_inv u := Subtype.ext ((stabilizerEquiv hB).symm_apply_apply u.val)
  right_inv u := Subtype.ext ((stabilizerEquiv hB).apply_symm_apply u.val)
  map_mul' u v := Subtype.ext ((stabilizerEquiv hB).map_mul u.val v.val)

/-- Native kernel coordinates in the four-dimensional natural six-letter module. -/
def coordinates {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (m22SetAction B).ker ≃* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
  (coreEquiv hB).trans Action.Natural.innerCore

/-- The full stabilizer action, before expressing the comparison with the original labels. -/
theorem coordinates_conjugation {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : MulAction.stabilizer M22 B) (u : (m22SetAction B).ker) :
    (coordinates hB (MulAut.conjNormal g u)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (naturalMap hB g).val
        (coordinates hB u).toAdd := by
  have he : coreEquiv hB (MulAut.conjNormal g u) =
      MulAut.conjNormal (stabilizerEquiv hB g) (coreEquiv hB u) := by
    apply Subtype.ext
    change stabilizerEquiv hB (g * u.val * g⁻¹) = _
    simp only [map_mul, map_inv]
    rfl
  change (Action.Natural.innerCore (coreEquiv hB (MulAut.conjNormal g u))).toAdd = _
  rw [he]
  exact Action.Natural.innerCore_conjugation (stabilizerEquiv hB g) (coreEquiv hB u)

/-- Natural marking of the same literal quotient as the original six-point action. -/
def quotientEquiv {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    (MulAction.stabilizer M22 B ⧸ (m22SetAction B).ker) ≃* alternatingGroup (Fin 6) :=
  (QuotientGroup.quotientMulEquivOfEq (naturalMap_ker hB).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (naturalMap hB) (naturalMap_surjective hB))

@[simp] theorem quotientEquiv_mk {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : MulAction.stabilizer M22 B) :
    quotientEquiv hB (QuotientGroup.mk g) = naturalMap hB g := rfl

/-- The displayed automorphism comparing the natural marking to the actual hexad labels. -/
def comparison {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    alternatingGroup (Fin 6) ≃* alternatingGroup (Fin 6) :=
  (quotientEquiv hB).symm.trans (m22HexadQuotientAlternatingEquiv hB)

/-- No six-point marking is discarded: the native quotient is the compared natural map. -/
theorem comparison_naturalMap {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : MulAction.stabilizer M22 B) :
    comparison hB (naturalMap hB g) = m22HexadSixMap hB g := by
  rw [← quotientEquiv_mk hB g]
  exact congrArg (m22HexadQuotientAlternatingEquiv hB)
    ((quotientEquiv hB).symm_apply_apply (QuotientGroup.mk g))

/-- The comparison formula in the direction needed to describe conjugation. -/
theorem naturalMap_eq {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (g : MulAction.stabilizer M22 B) :
    naturalMap hB g = (comparison hB).symm (m22HexadSixMap hB g) := by
  rw [← comparison_naturalMap, MulEquiv.symm_apply_apply]

end Sporadic.Mathieu.M22HexadCoordinates
end
