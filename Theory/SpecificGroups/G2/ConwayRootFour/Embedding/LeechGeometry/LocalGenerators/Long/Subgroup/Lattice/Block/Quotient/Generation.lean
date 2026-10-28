module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.MatrixData
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
/-!
# Generation of the restricted three-dimensional image

The two literal matrices `threeA` and `threeB` generate SL₃(GF(4)). A small
word certificate supplies a coordinate three-cycle and the elementary matrix
with entry 1 in position (0,1). Conjugation and a commutator supply entry 1
in position (0,2); removing that factor from `threeA` supplies entry τ in
position (0,1). Addition, cyclic conjugation, and elementary commutators then
give every elementary matrix. Elementary generation finishes the proof.

The certificate has 44 explicit intermediate matrices and 43 multiplication
identities. Each determinant and multiplication is checked in Lean's kernel;
no enumeration or order of the generated group is used in the proof.
The intermediate matrices shorten kernel computations of two words of length
24. The numerical generators are John Bray's ATLAS `6L34G1-Ar6aB0.M`,
restricted to the rows recorded in `MatrixData`. The elementary-generation
API is the attributed ATLAS port `ExceptionalIsomorphisms.Elementary`.
-/

public section
open Atlas.Algebra Matrix
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block
private def cycle : SL(3,GoldenFour) := ⟨!![0,1,0;0,0,1;1,0,0], by decide +kernel⟩
private def rootOne : SL(3,GoldenFour) := ⟨!![1,1,0;0,1,0;0,0,1], by decide +kernel⟩
private def rootTau : SL(3,GoldenFour) := ⟨!![1,goldenFourTau,0;0,1,0;0,0,1], by decide +kernel⟩
private def stage0 : SL(3,GoldenFour) :=
  ⟨!![1,0,0; 0,1,0; 0,0,1], by decide +kernel⟩
private def stage1 : SL(3,GoldenFour) :=
  ⟨!![1,goldenFourTau,1; 0,1,0; 0,0,1], by decide +kernel⟩
private def stage2 : SL(3,GoldenFour) :=
  ⟨!![0,goldenFourTau+1,goldenFourTau; 0,1,1; 1,1,1], by decide +kernel⟩
private def stage3 : SL(3,GoldenFour) :=
  ⟨!![0,goldenFourTau+1,goldenFourTau; 0,1,1; 1,goldenFourTau+1,0], by decide +kernel⟩
private def stage4 : SL(3,GoldenFour) :=
  ⟨!![goldenFourTau,1,1; 1,0,0; 1,goldenFourTau+1,goldenFourTau], by decide +kernel⟩
private def stage5 : SL(3,GoldenFour) :=
  ⟨!![goldenFourTau,goldenFourTau,goldenFourTau+1; 1,goldenFourTau,1; 1,1,goldenFourTau+1], by decide +kernel⟩
private def stage6 : SL(3,GoldenFour) :=
  ⟨!![1,1,goldenFourTau+1; goldenFourTau+1,0,goldenFourTau; goldenFourTau,goldenFourTau,goldenFourTau+1], by decide +kernel⟩
private def stage7 : SL(3,GoldenFour) :=
  ⟨!![1,goldenFourTau+1,goldenFourTau; goldenFourTau+1,1,1; goldenFourTau,1,1], by decide +kernel⟩
private def stage8 : SL(3,GoldenFour) :=
  ⟨!![1,goldenFourTau+1,0; 0,goldenFourTau,goldenFourTau+1; 0,goldenFourTau+1,goldenFourTau], by decide +kernel⟩
private def stage9 : SL(3,GoldenFour) :=
  ⟨!![1,1,1; 0,goldenFourTau,goldenFourTau+1; 0,goldenFourTau+1,goldenFourTau], by decide +kernel⟩
private def stage10 : SL(3,GoldenFour) :=
  ⟨!![0,0,1; goldenFourTau+1,1,1; goldenFourTau,1,1], by decide +kernel⟩
private def stage11 : SL(3,GoldenFour) :=
  ⟨!![1,1,1; goldenFourTau,0,goldenFourTau+1; goldenFourTau+1,0,goldenFourTau], by decide +kernel⟩
private def stage12 : SL(3,GoldenFour) :=
  ⟨!![1,goldenFourTau+1,0; goldenFourTau,goldenFourTau+1,1; goldenFourTau+1,1,1], by decide +kernel⟩
private def stage13 : SL(3,GoldenFour) :=
  ⟨!![goldenFourTau+1,1,goldenFourTau; goldenFourTau,goldenFourTau+1,0; 0,goldenFourTau,goldenFourTau+1], by decide +kernel⟩
private def stage14 : SL(3,GoldenFour) :=
  ⟨!![goldenFourTau+1,0,1; goldenFourTau,0,goldenFourTau; 0,goldenFourTau,goldenFourTau+1], by decide +kernel⟩
private def stage15 : SL(3,GoldenFour) :=
  ⟨!![1,goldenFourTau,goldenFourTau; goldenFourTau,0,0; 1,goldenFourTau+1,1], by decide +kernel⟩
private def stage16 : SL(3,GoldenFour) :=
  ⟨!![1,0,goldenFourTau+1; goldenFourTau,goldenFourTau+1,goldenFourTau; 1,1,0], by decide +kernel⟩
private def stage17 : SL(3,GoldenFour) :=
  ⟨!![goldenFourTau+1,goldenFourTau,goldenFourTau; 1,0,goldenFourTau+1; 1,1,0], by decide +kernel⟩
private def stage18 : SL(3,GoldenFour) :=
  ⟨!![goldenFourTau+1,goldenFourTau+1,1; 1,goldenFourTau,goldenFourTau; 1,goldenFourTau+1,1], by decide +kernel⟩
private def stage19 : SL(3,GoldenFour) :=
  ⟨!![goldenFourTau,goldenFourTau,1; goldenFourTau+1,0,1; 0,goldenFourTau,goldenFourTau+1], by decide +kernel⟩
private def stage20 : SL(3,GoldenFour) :=
  ⟨!![goldenFourTau,1,goldenFourTau+1; goldenFourTau+1,1,goldenFourTau; 0,goldenFourTau,goldenFourTau+1], by decide +kernel⟩
private def stage21 : SL(3,GoldenFour) :=
  ⟨!![1,goldenFourTau,0; 1,goldenFourTau+1,0; goldenFourTau+1,1,1], by decide +kernel⟩
private def stage22 : SL(3,GoldenFour) :=
  ⟨!![1,0,1; 1,1,1; goldenFourTau+1,0,goldenFourTau], by decide +kernel⟩
private def stage23 : SL(3,GoldenFour) :=
  ⟨!![0,1,0; 0,0,1; 1,goldenFourTau,1], by decide +kernel⟩
private def stage24 : SL(3,GoldenFour) :=
  ⟨!![0,1,0; 0,0,1; 1,0,0], by decide +kernel⟩
private def stage25 : SL(3,GoldenFour) :=
  ⟨!![1,1,goldenFourTau+1; 0,goldenFourTau+1,goldenFourTau; goldenFourTau,goldenFourTau,goldenFourTau+1], by decide +kernel⟩
private def stage26 : SL(3,GoldenFour) :=
  ⟨!![1,goldenFourTau+1,goldenFourTau; 0,goldenFourTau+1,goldenFourTau; goldenFourTau,1,1], by decide +kernel⟩
private def stage27 : SL(3,GoldenFour) :=
  ⟨!![1,goldenFourTau+1,0; 1,goldenFourTau,1; 0,goldenFourTau+1,goldenFourTau], by decide +kernel⟩
private def stage28 : SL(3,GoldenFour) :=
  ⟨!![1,1,1; 1,0,0; 0,goldenFourTau+1,goldenFourTau], by decide +kernel⟩
private def stage29 : SL(3,GoldenFour) :=
  ⟨!![0,0,1; 0,1,1; 1,goldenFourTau,1], by decide +kernel⟩
private def stage30 : SL(3,GoldenFour) :=
  ⟨!![0,0,1; 0,1,1; 1,0,0], by decide +kernel⟩
private def stage31 : SL(3,GoldenFour) :=
  ⟨!![1,1,1; 0,1,0; 0,1,1], by decide +kernel⟩
private def stage32 : SL(3,GoldenFour) :=
  ⟨!![1,goldenFourTau+1,0; 0,1,0; 0,1,1], by decide +kernel⟩
private def stage33 : SL(3,GoldenFour) :=
  ⟨!![1,goldenFourTau+1,goldenFourTau; 0,1,1; 1,0,0], by decide +kernel⟩
private def stage34 : SL(3,GoldenFour) :=
  ⟨!![1,1,goldenFourTau+1; 0,1,1; 1,goldenFourTau,1], by decide +kernel⟩
private def stage35 : SL(3,GoldenFour) :=
  ⟨!![goldenFourTau,goldenFourTau,goldenFourTau+1; 1,0,0; 0,goldenFourTau+1,goldenFourTau], by decide +kernel⟩
private def stage36 : SL(3,GoldenFour) :=
  ⟨!![goldenFourTau,1,1; 1,goldenFourTau,1; 0,goldenFourTau+1,goldenFourTau], by decide +kernel⟩
private def stage37 : SL(3,GoldenFour) :=
  ⟨!![goldenFourTau+1,0,goldenFourTau; 0,goldenFourTau+1,goldenFourTau; goldenFourTau,1,1], by decide +kernel⟩
private def stage38 : SL(3,GoldenFour) :=
  ⟨!![goldenFourTau+1,1,1; 0,goldenFourTau+1,goldenFourTau; goldenFourTau,goldenFourTau,goldenFourTau+1], by decide +kernel⟩
private def stage39 : SL(3,GoldenFour) :=
  ⟨!![0,goldenFourTau,goldenFourTau+1; 1,goldenFourTau,1; 1,1,goldenFourTau+1], by decide +kernel⟩
private def stage40 : SL(3,GoldenFour) :=
  ⟨!![0,goldenFourTau,goldenFourTau+1; 1,0,0; 1,goldenFourTau+1,goldenFourTau], by decide +kernel⟩
private def stage41 : SL(3,GoldenFour) :=
  ⟨!![1,goldenFourTau+1,1; 0,1,1; 1,goldenFourTau+1,0], by decide +kernel⟩
private def stage42 : SL(3,GoldenFour) :=
  ⟨!![1,1,0; 0,1,1; 1,1,1], by decide +kernel⟩
private def stage43 : SL(3,GoldenFour) :=
  ⟨!![1,1,0; 0,1,0; 0,0,1], by decide +kernel⟩
private theorem stage0_eq : stage0 = 1 := by decide +kernel
private theorem stage1_eq : stage1 = stage0 * threeA := by decide +kernel
private theorem stage2_eq : stage2 = stage1 * threeB := by decide +kernel
private theorem stage3_eq : stage3 = stage2 * threeA := by decide +kernel
private theorem stage4_eq : stage4 = stage3 * threeB := by decide +kernel
private theorem stage5_eq : stage5 = stage4 * threeA := by decide +kernel
private theorem stage6_eq : stage6 = stage5 * threeB⁻¹ := by decide +kernel
private theorem stage7_eq : stage7 = stage6 * threeA := by decide +kernel
private theorem stage8_eq : stage8 = stage7 * threeB⁻¹ := by decide +kernel
private theorem stage9_eq : stage9 = stage8 * threeA := by decide +kernel
private theorem stage10_eq : stage10 = stage9 * threeB := by decide +kernel
private theorem stage11_eq : stage11 = stage10 * threeB := by decide +kernel
private theorem stage12_eq : stage12 = stage11 * threeA := by decide +kernel
private theorem stage13_eq : stage13 = stage12 * threeB⁻¹ := by decide +kernel
private theorem stage14_eq : stage14 = stage13 * threeA := by decide +kernel
private theorem stage15_eq : stage15 = stage14 * threeB⁻¹ := by decide +kernel
private theorem stage16_eq : stage16 = stage15 * threeA := by decide +kernel
private theorem stage17_eq : stage17 = stage16 * threeB⁻¹ := by decide +kernel
private theorem stage18_eq : stage18 = stage17 * threeA := by decide +kernel
private theorem stage19_eq : stage19 = stage18 * threeB := by decide +kernel
private theorem stage20_eq : stage20 = stage19 * threeA := by decide +kernel
private theorem stage21_eq : stage21 = stage20 * threeB := by decide +kernel
private theorem stage22_eq : stage22 = stage21 * threeA := by decide +kernel
private theorem stage23_eq : stage23 = stage22 * threeB := by decide +kernel
private theorem stage24_eq : stage24 = stage23 * threeA := by decide +kernel
private theorem stage25_eq : stage25 = stage5 * threeB := by decide +kernel
private theorem stage26_eq : stage26 = stage25 * threeA := by decide +kernel
private theorem stage27_eq : stage27 = stage26 * threeB⁻¹ := by decide +kernel
private theorem stage28_eq : stage28 = stage27 * threeA := by decide +kernel
private theorem stage29_eq : stage29 = stage28 * threeB⁻¹ := by decide +kernel
private theorem stage30_eq : stage30 = stage29 * threeA := by decide +kernel
private theorem stage31_eq : stage31 = stage30 * threeB⁻¹ := by decide +kernel
private theorem stage32_eq : stage32 = stage31 * threeA := by decide +kernel
private theorem stage33_eq : stage33 = stage32 * threeB := by decide +kernel
private theorem stage34_eq : stage34 = stage33 * threeA := by decide +kernel
private theorem stage35_eq : stage35 = stage34 * threeB := by decide +kernel
private theorem stage36_eq : stage36 = stage35 * threeA := by decide +kernel
private theorem stage37_eq : stage37 = stage36 * threeB := by decide +kernel
private theorem stage38_eq : stage38 = stage37 * threeA := by decide +kernel
private theorem stage39_eq : stage39 = stage38 * threeB⁻¹ := by decide +kernel
private theorem stage40_eq : stage40 = stage39 * threeA := by decide +kernel
private theorem stage41_eq : stage41 = stage40 * threeB⁻¹ := by decide +kernel
private theorem stage42_eq : stage42 = stage41 * threeA := by decide +kernel
private theorem stage43_eq : stage43 = stage42 * threeB⁻¹ := by decide +kernel
private def rootTwelve : SL(3,GoldenFour) :=
  ⟨!![1,0,0;0,1,1;0,0,1], by decide +kernel⟩
private def rootZeroTwo : SL(3,GoldenFour) :=
  ⟨!![1,0,1;0,1,0;0,0,1], by decide +kernel⟩
private theorem rootTwelve_eq : rootTwelve = cycle⁻¹ * rootOne * cycle := by decide +kernel
private theorem rootZeroTwo_eq : rootZeroTwo = rootOne * rootTwelve * rootOne * rootTwelve := by
  decide +kernel
private theorem rootTau_eq : rootTau = threeA * rootZeroTwo := by decide +kernel

private theorem seed_mem (H : Subgroup SL(3,GoldenFour))
    (ha : threeA ∈ H) (hb : threeB ∈ H) :
    cycle ∈ H ∧ rootOne ∈ H ∧ rootTau ∈ H := by
  have h0 : stage0 ∈ H := stage0_eq.symm ▸ H.one_mem
  have h1 : stage1 ∈ H := stage1_eq.symm ▸ H.mul_mem h0 ha
  have h2 : stage2 ∈ H := stage2_eq.symm ▸ H.mul_mem h1 hb
  have h3 : stage3 ∈ H := stage3_eq.symm ▸ H.mul_mem h2 ha
  have h4 : stage4 ∈ H := stage4_eq.symm ▸ H.mul_mem h3 hb
  have h5 : stage5 ∈ H := stage5_eq.symm ▸ H.mul_mem h4 ha
  have h6 : stage6 ∈ H := stage6_eq.symm ▸ H.mul_mem h5 (H.inv_mem hb)
  have h7 : stage7 ∈ H := stage7_eq.symm ▸ H.mul_mem h6 ha
  have h8 : stage8 ∈ H := stage8_eq.symm ▸ H.mul_mem h7 (H.inv_mem hb)
  have h9 : stage9 ∈ H := stage9_eq.symm ▸ H.mul_mem h8 ha
  have h10 : stage10 ∈ H := stage10_eq.symm ▸ H.mul_mem h9 hb
  have h11 : stage11 ∈ H := stage11_eq.symm ▸ H.mul_mem h10 hb
  have h12 : stage12 ∈ H := stage12_eq.symm ▸ H.mul_mem h11 ha
  have h13 : stage13 ∈ H := stage13_eq.symm ▸ H.mul_mem h12 (H.inv_mem hb)
  have h14 : stage14 ∈ H := stage14_eq.symm ▸ H.mul_mem h13 ha
  have h15 : stage15 ∈ H := stage15_eq.symm ▸ H.mul_mem h14 (H.inv_mem hb)
  have h16 : stage16 ∈ H := stage16_eq.symm ▸ H.mul_mem h15 ha
  have h17 : stage17 ∈ H := stage17_eq.symm ▸ H.mul_mem h16 (H.inv_mem hb)
  have h18 : stage18 ∈ H := stage18_eq.symm ▸ H.mul_mem h17 ha
  have h19 : stage19 ∈ H := stage19_eq.symm ▸ H.mul_mem h18 hb
  have h20 : stage20 ∈ H := stage20_eq.symm ▸ H.mul_mem h19 ha
  have h21 : stage21 ∈ H := stage21_eq.symm ▸ H.mul_mem h20 hb
  have h22 : stage22 ∈ H := stage22_eq.symm ▸ H.mul_mem h21 ha
  have h23 : stage23 ∈ H := stage23_eq.symm ▸ H.mul_mem h22 hb
  have h24 : stage24 ∈ H := stage24_eq.symm ▸ H.mul_mem h23 ha
  have h25 : stage25 ∈ H := stage25_eq.symm ▸ H.mul_mem h5 hb
  have h26 : stage26 ∈ H := stage26_eq.symm ▸ H.mul_mem h25 ha
  have h27 : stage27 ∈ H := stage27_eq.symm ▸ H.mul_mem h26 (H.inv_mem hb)
  have h28 : stage28 ∈ H := stage28_eq.symm ▸ H.mul_mem h27 ha
  have h29 : stage29 ∈ H := stage29_eq.symm ▸ H.mul_mem h28 (H.inv_mem hb)
  have h30 : stage30 ∈ H := stage30_eq.symm ▸ H.mul_mem h29 ha
  have h31 : stage31 ∈ H := stage31_eq.symm ▸ H.mul_mem h30 (H.inv_mem hb)
  have h32 : stage32 ∈ H := stage32_eq.symm ▸ H.mul_mem h31 ha
  have h33 : stage33 ∈ H := stage33_eq.symm ▸ H.mul_mem h32 hb
  have h34 : stage34 ∈ H := stage34_eq.symm ▸ H.mul_mem h33 ha
  have h35 : stage35 ∈ H := stage35_eq.symm ▸ H.mul_mem h34 hb
  have h36 : stage36 ∈ H := stage36_eq.symm ▸ H.mul_mem h35 ha
  have h37 : stage37 ∈ H := stage37_eq.symm ▸ H.mul_mem h36 hb
  have h38 : stage38 ∈ H := stage38_eq.symm ▸ H.mul_mem h37 ha
  have h39 : stage39 ∈ H := stage39_eq.symm ▸ H.mul_mem h38 (H.inv_mem hb)
  have h40 : stage40 ∈ H := stage40_eq.symm ▸ H.mul_mem h39 ha
  have h41 : stage41 ∈ H := stage41_eq.symm ▸ H.mul_mem h40 (H.inv_mem hb)
  have h42 : stage42 ∈ H := stage42_eq.symm ▸ H.mul_mem h41 ha
  have h43 : stage43 ∈ H := stage43_eq.symm ▸ H.mul_mem h42 (H.inv_mem hb)
  have hc : cycle ∈ H := h24
  have h1 : rootOne ∈ H := h43
  have h12 : rootTwelve ∈ H := rootTwelve_eq.symm ▸
    H.mul_mem (H.mul_mem (H.inv_mem hc) h1) hc
  have h02 : rootZeroTwo ∈ H := rootZeroTwo_eq.symm ▸
    H.mul_mem (H.mul_mem (H.mul_mem h1 h12) h1) h12
  exact ⟨hc, h1, rootTau_eq.symm ▸ H.mul_mem ha h02⟩

private def cyclicRoot (a : GoldenFour) : SL(3,GoldenFour) :=
  SpecialLinearGroup.transvection (i := (0 : Fin 3)) (j := 1) (by decide) a

private def cyclicRoot' (a : GoldenFour) : SL(3,GoldenFour) :=
  cycle * cyclicRoot a * cycle⁻¹

private def cyclicRoot'' (a : GoldenFour) : SL(3,GoldenFour) :=
  cycle⁻¹ * cyclicRoot a * cycle

private theorem root_parameter_cases : ∀ a : GoldenFour,
    cyclicRoot a = 1 ∨ cyclicRoot a = rootOne ∨ cyclicRoot a = rootTau ∨
      cyclicRoot a = rootOne * rootTau := by
  rintro ⟨x, y⟩
  revert x y
  decide +kernel

open scoped commutatorElement in
private theorem elementary_cases : ∀ (i j : Fin 3) (hij : i ≠ j) (a : GoldenFour),
    SpecialLinearGroup.transvection hij a = cyclicRoot a ∨
    SpecialLinearGroup.transvection hij a = cyclicRoot' a ∨
    SpecialLinearGroup.transvection hij a = cyclicRoot'' a ∨
    SpecialLinearGroup.transvection hij a = ⁅cyclicRoot a, cyclicRoot'' 1⁆ ∨
    SpecialLinearGroup.transvection hij a = ⁅cyclicRoot' a, cyclicRoot 1⁆ ∨
    SpecialLinearGroup.transvection hij a = ⁅cyclicRoot'' a, cyclicRoot' 1⁆ := by
  rintro i j hij ⟨x, y⟩
  revert i j hij x y
  decide +kernel

private theorem elementary_mem (H : Subgroup SL(3,GoldenFour))
    (hc : cycle ∈ H) (h1 : rootOne ∈ H) (hw : rootTau ∈ H)
    (i j : Fin 3) (hij : i ≠ j) (a : GoldenFour) :
    SpecialLinearGroup.transvection hij a ∈ H := by
  have hr (a : GoldenFour) : cyclicRoot a ∈ H := by
    rcases root_parameter_cases a with h | h | h | h <;> rw [h]
    · exact H.one_mem
    · exact h1
    · exact hw
    · exact H.mul_mem h1 hw
  have hr' (a : GoldenFour) : cyclicRoot' a ∈ H :=
    H.mul_mem (H.mul_mem hc (hr a)) (H.inv_mem hc)
  have hr'' (a : GoldenFour) : cyclicRoot'' a ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem hc) (hr a)) hc
  rcases elementary_cases i j hij a with h | h | h | h | h | h <;> rw [h]
  · exact hr a
  · exact hr' a
  · exact hr'' a
  · exact H.mul_mem (H.mul_mem (H.mul_mem (hr a) (hr'' 1))
      (H.inv_mem (hr a))) (H.inv_mem (hr'' 1))
  · exact H.mul_mem (H.mul_mem (H.mul_mem (hr' a) (hr 1))
      (H.inv_mem (hr' a))) (H.inv_mem (hr 1))
  · exact H.mul_mem (H.mul_mem (H.mul_mem (hr'' a) (hr' 1))
      (H.inv_mem (hr'' a))) (H.inv_mem (hr' 1))

/-- The two literal matrices induced on the invariant three-space generate SL₃(GF(4)). -/
theorem threeA_threeB_generate : Subgroup.closure {threeA, threeB} = ⊤ := by
  let H := Subgroup.closure ({threeA, threeB} : Set SL(3,GoldenFour))
  obtain ⟨hc, h1, hw⟩ := seed_mem H
    (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
  apply top_unique
  intro g _
  exact Atlas.sl_elementary_induction (fun g => g ∈ H)
    (elementary_mem H hc h1 hw) (fun _ _ => H.mul_mem) g

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block
