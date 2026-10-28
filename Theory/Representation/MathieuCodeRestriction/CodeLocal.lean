module

public import Theory.Representation.MathieuCodeRestriction.M22
public import Theory.Mathieu.M24.LocalGeometry.OctadCharacteristicTwo

/-!
# The native Mathieu octad fixed line

The octad pointwise kernel acts transitively on the sixteen complementary
points, by the existing native heptad translation construction. A fixed class
in the Golay quotient has a fixed representative: evaluation at any octad
point kills the possible constant difference. Subtracting its constant value
on the complement gives a Golay word supported on the octad. The certified
minimum weight forces this word to be zero or the octad word. Thus the fixed
space is exactly the nonzero octad line.

Conjugacy also identifies every pointwise octad kernel with the intrinsic
two-core of its stabilizer, mapped into M24. This retains relative normality
and supplies the precise fixed-line premise of the native M22 restriction.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), H.16.2(1),
printed p.402. This proves the fixed-line clause, not the entire chief flag.
The proof uses the literal native Golay code and no module classification.
-/

public section
noncomputable section

open Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry
open Representation.BinaryOffender
open scoped Pointwise
namespace MathieuCode

/-- Every vector in the native Golay span is one of the certified binary words. -/
theorem golay_exists_word {v : Full} (hv : v ∈ golay) :
    ∃ u : Fin 4096, v = wordOfMask (m24GolayCode u) := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i, rfl⟩ := hv
    exact ⟨rowMessage i, (row_eq_word i).trans (wordOfSet_golayWord _)⟩
  | zero => exact ⟨0, by rw [m24GolayCode_zero, wordOfMask_zero]⟩
  | add v w hv hw ihv ihw =>
    obtain ⟨u, rfl⟩ := ihv
    obtain ⟨t, rfl⟩ := ihw
    exact ⟨m24GolayMessageXor u t, by rw [m24GolayCode_xor, wordOfMask_xor]⟩
  | smul c v hv ih =>
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · exact ⟨0, by simp only [zero_smul, m24GolayCode_zero, wordOfMask_zero]⟩
    · simpa only [one_smul] using ih

/-- Minimum weight leaves only zero and the octad word on an octad support. -/
theorem golay_supported_octad (O : Octad) {v : Full} (hv : v ∈ golay)
    (hs : ∀ i, i ∉ O.val → v i = 0) : v = 0 ∨ v = wordOfSet O.val := by
  obtain ⟨u, rfl⟩ := golay_exists_word hv
  by_cases hu : u = 0
  · left; rw [hu, m24GolayCode_zero, wordOfMask_zero]
  right
  have hsub : m24GolayWord u ⊆ O.val := by
    intro i hi
    by_contra hio
    have hzero := hs i hio
    rw [← wordOfSet_golayWord] at hzero
    simp [wordOfSet, hi] at hzero
  have he : m24GolayWord u = O.val := Finset.eq_of_subset_of_card_le hsub (by
    rw [m24Blocks_card _ O.property]
    exact m24Golay_minWeight u hu)
  rw [← wordOfSet_golayWord, he]

end MathieuCode

namespace MathieuCode
open Sporadic.Mathieu.M23Geometry
open Sporadic.Mathieu.M24LocalGeometry.LinearFourCore

private theorem seed_complement_lift (x : Fin 24) (hx : x ∉ seedOctad.val) :
    ∃ i : Fin 23, i ∉ omega ∧ m23PointEmbedding i = x := by
  have hzero : x ≠ (24 : Fin 24) := by
    intro he
    subst x
    exact hx ((mem_seedOctad _).mpr (Or.inl rfl))
  obtain ⟨i, hi⟩ := m23PointEquiv.surjective ⟨x, hzero⟩
  have he : m23PointEmbedding i = x := congrArg Subtype.val hi
  refine ⟨i, ?_, he⟩
  intro himem
  exact hx ((mem_seedOctad _).mpr (Or.inr ⟨i, himem, he⟩))

/-- The native translation kernel is transitive on the complementary sixteen points. -/
theorem seed_kernel_transitive (x y : Fin 24)
    (hx : x ∉ seedOctad.val) (hy : y ∉ seedOctad.val) :
    ∃ g : octadPointwiseKernel seedOctad, g.val • x = y := by
  obtain ⟨i, hi, rfl⟩ := seed_complement_lift x hx
  obtain ⟨j, hj, rfl⟩ := seed_complement_lift y hy
  obtain ⟨g, hg, _⟩ := heptadKernelComplementAction_regular
    ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩⟩
    ⟨j, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hj⟩⟩
  refine ⟨⟨(kernelLift g).val.val, Subgroup.mem_map_of_mem _ (kernelLift g).property⟩, ?_⟩
  have he := congrArg Subtype.val hg
  rw [heptadKernelComplementAction_apply] at he
  change (kernelLift g).val.val • m23PointEmbedding i = m23PointEmbedding j
  rw [kernelLift_coe]
  change (heptadLift g.val).val.val (m23PointEmbedding i) = _
  rw [heptadLift_coe, m23ExtendHom_apply_embedded]
  exact congrArg m23PointEmbedding he

/-- Conjugating the actual octad conjugates its pointwise kernel. -/
theorem octad_kernel_map (O P : Octad) (g : M24) (h : g • O.val = P.val) :
    (octadPointwiseKernel O).map (MulAut.conj g).toMonoidHom =
      octadPointwiseKernel P := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    apply (mem_octadPointwiseKernel _ _).mpr
    intro i hi
    rw [← h] at hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_smul_finset.mp hi
    change (g * b * g⁻¹) • (g • j) = g • j
    simp only [mul_smul, inv_smul_smul, (mem_octadPointwiseKernel O b).mp hb j hj]
  · intro ha
    refine ⟨g⁻¹ * a * g, (mem_octadPointwiseKernel _ _).mpr ?_, ?_⟩
    · intro i hi
      have hgi : g • i ∈ P.val := h ▸ Finset.smul_mem_smul_finset hi
      simp only [mul_smul, (mem_octadPointwiseKernel P a).mp ha _ hgi, inv_smul_smul]
    · change g * (g⁻¹ * a * g) * g⁻¹ = a
      group

/-- Every native pointwise octad kernel is transitive on its complement. -/
theorem octad_kernel_transitive (O : Octad) (x y : Fin 24)
    (hx : x ∉ O.val) (hy : y ∉ O.val) :
    ∃ g : octadPointwiseKernel O, g.val • x = y := by
  obtain ⟨a, ha⟩ := exists_smul_octad_eq seedOctad O
  have hx' : a⁻¹ • x ∉ seedOctad.val := by
    intro hm
    apply hx
    rw [← ha]
    exact Finset.mem_smul_finset.mpr ⟨_, hm, smul_inv_smul a x⟩
  have hy' : a⁻¹ • y ∉ seedOctad.val := by
    intro hm
    apply hy
    rw [← ha]
    exact Finset.mem_smul_finset.mpr ⟨_, hm, smul_inv_smul a y⟩
  obtain ⟨b, hb⟩ := seed_kernel_transitive _ _ hx' hy'
  refine ⟨⟨a * b.val * a⁻¹, ?_⟩, ?_⟩
  · rw [← octad_kernel_map seedOctad O a ha]
    exact Subgroup.mem_map_of_mem _ b.property
  · change (a * b.val * a⁻¹) • x = y
    rw [mul_smul, mul_smul, hb, smul_inv_smul]

/-- A fixed quotient class has a fixed Golay representative because the kernel fixes a point. -/
theorem octad_fixed_lift (O : Octad) (v : golay)
    (hv : codeLine.mkQ v ∈ fixedSpace codeRepresentation (octadPointwiseKernel O))
    (g : octadPointwiseKernel O) : golayRepresentation g.val v = v := by
  have he := hv g
  change codeRepresentation g.val (codeLine.mkQ v) = codeLine.mkQ v at he
  rw [codeRepresentation_mk] at he
  have hc := (Submodule.Quotient.eq codeLine).mp he
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hc
  change c • BinaryPermutation.allOne (Fin 24) =
    (golayRepresentation g.val v).val - v.val at hc
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (by rw [m24Blocks_card _ O.property]; decide)
  have hfix := (mem_octadPointwiseKernel O g.val⁻¹).mp
    ((octadPointwiseKernel O).inv_mem g.property) i hi
  have hci := congrFun hc i
  change c * 1 = v.val (g.val⁻¹ • i) - v.val i at hci
  rw [hfix, sub_self, mul_one] at hci
  rw [hci, zero_smul] at hc
  exact Subtype.ext (sub_eq_zero.mp hc.symm)

/-- The entire octad fixed space is the line of the literal octad word. -/
theorem octad_fixedSpace_eq_span (O : Octad) :
    fixedSpace codeRepresentation (octadPointwiseKernel O) =
      Submodule.span (ZMod 2) {octadVector O} := by
  apply le_antisymm
  · intro q hq
    obtain ⟨v, rfl⟩ := codeLine.mkQ_surjective q
    obtain ⟨j, _, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (show O.val.card < (Finset.univ : Finset (Fin 24)).card by
        rw [m24Blocks_card _ O.property]; decide)
    let w : golay := v - v.val j • ⟨BinaryPermutation.allOne (Fin 24), allOne_mem⟩
    have hw : ∀ i, i ∉ O.val → w.val i = 0 := by
      intro i hi
      obtain ⟨g, hg⟩ := octad_kernel_transitive O i j hi hj
      have he := congrArg (fun u : golay => u.val (g.val • i)) (octad_fixed_lift O v hq g)
      change v.val (g.val⁻¹ • (g.val • i)) = v.val (g.val • i) at he
      rw [inv_smul_smul, hg] at he
      change v.val i - v.val j * 1 = 0
      rw [he, mul_one, sub_self]
    have hwq : codeLine.mkQ w = codeLine.mkQ v := by
      have hz : codeLine.mkQ (⟨BinaryPermutation.allOne (Fin 24), allOne_mem⟩ : golay) = 0 := by
        apply (Submodule.Quotient.mk_eq_zero codeLine).mpr
        exact Submodule.subset_span (Set.mem_singleton _)
      change codeLine.mkQ (v - v.val j • _) = _
      rw [map_sub, map_smul, hz, smul_zero, sub_zero]
    rcases golay_supported_octad O w.property hw with hw | hw
    · have hw0 : w = 0 := Subtype.ext hw
      rw [← hwq, hw0, map_zero]
      exact Submodule.zero_mem _
    · have hwO : codeLine.mkQ w = octadVector O := by
        unfold octadVector
        exact congrArg codeLine.mkQ (Subtype.ext hw)
      rw [← hwq, hwO]
      exact Submodule.subset_span (Set.mem_singleton _)
  · exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (octadVector_fixed O))

/-- The fixed-line assertion of H.16.2(1) on the actual eleven-dimensional code. -/
theorem octad_fixedSpace_finrank (O : Octad) :
    Module.finrank (ZMod 2) (fixedSpace codeRepresentation (octadPointwiseKernel O)) = 1 := by
  rw [octad_fixedSpace_eq_span]
  exact finrank_span_singleton (octadVector_ne_zero O)

/-- Discharge the earlier fixed-line input of the native M22 restriction theorems. -/
theorem m24OctadFixedLine : M24OctadFixedLine := octad_fixedSpace_finrank

/-- The mapped intrinsic two-core equals the actual pointwise octad kernel. -/
theorem octad_core_map_eq_pointwise (O : Octad) :
    (pCore 2 (octadStabilizer O)).map (octadStabilizer O).subtype =
      octadPointwiseKernel O := by
  obtain ⟨g, hg⟩ := exists_smul_octad_eq seedOctad O
  have hs : octadStabilizer O =
      (octadStabilizer seedOctad).map (MulAut.conj g).toMonoidHom := by
    change MulAction.stabilizer M24 O.val =
      (MulAction.stabilizer M24 seedOctad.val).map _
    rw [← hg, MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  let e : octadStabilizer seedOctad ≃* octadStabilizer O :=
    ((MulAut.conj g).subgroupMap _).trans (MulEquiv.subgroupCongr hs.symm)
  have he : (octadStabilizer O).subtype.comp e.toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (octadStabilizer seedOctad).subtype := by
    ext a
    rfl
  rw [← pCore_map_iso 2 e, Subgroup.map_map, he, ← Subgroup.map_map,
    seed_core_eq_kernel]
  exact octad_kernel_map seedOctad O g hg


/-- The M22 hexad fixed-line dimension, with its M24 premise now discharged. -/
theorem m22Hexad_fixedSpace_finrank_native {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    Module.finrank (ZMod 2)
      (fixedSpace m22CodeRepresentation (m22HexadPointwiseKernel B)) = 1 :=
  m22Hexad_fixedSpace_finrank_of_M24 m24OctadFixedLine hB

/-- The fixed line in the M22 hyperplane is generated by its actual marked hexad vector. -/
theorem m22Hexad_fixedSpace_eq_span_native {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) :
    fixedSpace m22CodeRepresentation (m22HexadPointwiseKernel B) =
      Submodule.span (ZMod 2) {m22HexadVector hB} :=
  m22Hexad_fixedSpace_eq_span hB (m24OctadFixedLine (m22Octad hB))

end MathieuCode
