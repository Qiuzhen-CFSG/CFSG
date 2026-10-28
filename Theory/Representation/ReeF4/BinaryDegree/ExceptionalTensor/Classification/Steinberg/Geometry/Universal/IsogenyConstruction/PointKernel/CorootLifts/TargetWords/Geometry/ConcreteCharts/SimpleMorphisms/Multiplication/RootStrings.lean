module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleMorphisms.Polynomial

/-!
# Coordinates along independent F4 root strings

Every root in an independent string is indexed by its distance from the bottom.
The root-string interval theorem identifies these coordinates, their bounds, and
the common string length. The construction follows the root-string argument in
`IntegralGeckConstruction.lean`, without changing its private implementation.
Source: the integral construction behind GLS3, Remark 1.12.10.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
open Theory.AlgebraicGroup.StandardRootSystem
namespace Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts.SimpleSL2Multiplication
local instance rootStringGeometryNeg : InvolutiveNeg Root := typeF4RootPairing.indexNeg
lemma root_chainBotIdx_add_nsmul_mem {i : typeF4RootPairing_base.support} {j : Root}
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j]) {n : ℕ}
    (hn : n ≤ typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j) :
    typeF4RootPairing.root (typeF4RootPairing.chainBotIdx i j) + n • typeF4RootPairing.root i ∈ Set.range typeF4RootPairing.root := by
  rw [typeF4RootPairing.root_chainBotIdx]
  have heq : typeF4RootPairing.root j - typeF4RootPairing.chainBotCoeff i j • typeF4RootPairing.root i + n • typeF4RootPairing.root i =
      typeF4RootPairing.root j + ((n : ℤ) - typeF4RootPairing.chainBotCoeff i j) • typeF4RootPairing.root i := by
    simp only [sub_smul]
    module
  rw [heq, typeF4RootPairing.root_add_zsmul_mem_range_iff hlin, Set.mem_Icc]
  constructor <;> omega

noncomputable def rootStringIdx (i : typeF4RootPairing_base.support) (j : Root)
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j]) (n : ℕ)
    (hn : n ≤ typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j) : Root :=
  (root_chainBotIdx_add_nsmul_mem hlin hn).choose

lemma root_rootStringIdx {i : typeF4RootPairing_base.support} {j : Root}
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j]) {n : ℕ}
    (hn : n ≤ typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j) :
    typeF4RootPairing.root (rootStringIdx i j hlin n hn) =
      typeF4RootPairing.root (typeF4RootPairing.chainBotIdx i j) + n • typeF4RootPairing.root i :=
  (root_chainBotIdx_add_nsmul_mem hlin hn).choose_spec

lemma root_rootStringIdx_eq {i : typeF4RootPairing_base.support} {j : Root}
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j]) {n : ℕ}
    (hn : n ≤ typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j) :
    typeF4RootPairing.root (rootStringIdx i j hlin n hn) =
      typeF4RootPairing.root j + ((n : ℤ) - typeF4RootPairing.chainBotCoeff i j) • typeF4RootPairing.root i := by
  rw [root_rootStringIdx hlin hn, typeF4RootPairing.root_chainBotIdx]
  simp only [sub_smul]
  module

lemma linearIndependent_rootStringIdx {i : typeF4RootPairing_base.support} {j : Root}
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j]) {n : ℕ}
    (hn : n ≤ typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j) :
    LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root (rootStringIdx i j hlin n hn)] := by
  rw [root_rootStringIdx_eq hlin hn, add_comm,
    LinearIndependent.pair_add_smul_right_iff]
  exact hlin

lemma chainBotCoeff_rootStringIdx {i : typeF4RootPairing_base.support} {j : Root}
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j]) {n : ℕ}
    (hn : n ≤ typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j) :
    typeF4RootPairing.chainBotCoeff i (rootStringIdx i j hlin n hn) = n := by
  have hlink : LinearIndependent ℝ
      ![typeF4RootPairing.root i, typeF4RootPairing.root (rootStringIdx i j hlin n hn)] :=
    linearIndependent_rootStringIdx hlin hn
  apply le_antisymm
  · have hmem := (typeF4RootPairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlink).2
      (le_refl (typeF4RootPairing.chainBotCoeff i (rootStringIdx i j hlin n hn)))
    rw [root_rootStringIdx_eq hlin hn] at hmem
    have heq : typeF4RootPairing.root j + ((n : ℤ) - typeF4RootPairing.chainBotCoeff i j) • typeF4RootPairing.root i -
        typeF4RootPairing.chainBotCoeff i (rootStringIdx i j hlin n hn) • typeF4RootPairing.root i =
        typeF4RootPairing.root j + ((n : ℤ) - typeF4RootPairing.chainBotCoeff i j -
          typeF4RootPairing.chainBotCoeff i (rootStringIdx i j hlin n hn)) • typeF4RootPairing.root i := by
      simp only [sub_smul]
      module
    rw [heq, typeF4RootPairing.root_add_zsmul_mem_range_iff hlin, Set.mem_Icc] at hmem
    omega
  · apply (typeF4RootPairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff hlink).1
    refine ⟨typeF4RootPairing.chainBotIdx i j, ?_⟩
    rw [root_rootStringIdx hlin hn]
    module

lemma chainTopCoeff_rootStringIdx {i : typeF4RootPairing_base.support} {j : Root}
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j]) {n : ℕ}
    (hn : n ≤ typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j) :
    typeF4RootPairing.chainTopCoeff i (rootStringIdx i j hlin n hn) =
      typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j - n := by
  have hlink : LinearIndependent ℝ
      ![typeF4RootPairing.root i, typeF4RootPairing.root (rootStringIdx i j hlin n hn)] :=
    linearIndependent_rootStringIdx hlin hn
  apply le_antisymm
  · have hmem := (typeF4RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlink).2
      (le_refl (typeF4RootPairing.chainTopCoeff i (rootStringIdx i j hlin n hn)))
    rw [root_rootStringIdx_eq hlin hn] at hmem
    have heq : typeF4RootPairing.root j + ((n : ℤ) - typeF4RootPairing.chainBotCoeff i j) • typeF4RootPairing.root i +
        typeF4RootPairing.chainTopCoeff i (rootStringIdx i j hlin n hn) • typeF4RootPairing.root i =
        typeF4RootPairing.root j + ((n : ℤ) - typeF4RootPairing.chainBotCoeff i j +
          typeF4RootPairing.chainTopCoeff i (rootStringIdx i j hlin n hn)) • typeF4RootPairing.root i := by
      simp only [add_smul]
      module
    rw [heq, typeF4RootPairing.root_add_zsmul_mem_range_iff hlin, Set.mem_Icc] at hmem
    omega
  · apply (typeF4RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff hlink).1
    refine ⟨typeF4RootPairing.chainTopIdx i j, ?_⟩
    rw [root_rootStringIdx_eq hlin hn, typeF4RootPairing.root_chainTopIdx]
    rw [← natCast_zsmul, ← natCast_zsmul]
    have hcast : ((typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j - n : ℕ) : ℤ) =
        typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j - n := by
      omega
    rw [hcast]
    module


lemma same_bottom_iff (i : typeF4RootPairing_base.support) (r j : Root) :
    typeF4RootPairing.chainBotIdx i r = typeF4RootPairing.chainBotIdx i j ↔
      typeF4RootPairing.root r + typeF4RootPairing.chainBotCoeff i j • typeF4RootPairing.root i =
        typeF4RootPairing.root j + typeF4RootPairing.chainBotCoeff i r • typeF4RootPairing.root i := by
  rw [← typeF4RootPairing.root.injective.eq_iff, typeF4RootPairing.root_chainBotIdx,
    typeF4RootPairing.root_chainBotIdx]
  exact sub_eq_sub_iff_add_eq_add

lemma same_bottom_root_eq {i : typeF4RootPairing_base.support} {r j : Root}
    (h : typeF4RootPairing.chainBotIdx i r = typeF4RootPairing.chainBotIdx i j) :
    typeF4RootPairing.root r = typeF4RootPairing.root j +
      ((typeF4RootPairing.chainBotCoeff i r : ℤ) - typeF4RootPairing.chainBotCoeff i j) •
        typeF4RootPairing.root i := by
  have h := (same_bottom_iff i r j).mp h
  simp only [sub_smul, natCast_zsmul]
  rw [← add_sub_assoc]
  exact eq_sub_iff_add_eq.mpr h

lemma same_bottom_bound {i : typeF4RootPairing_base.support} {r j : Root}
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j])
    (h : typeF4RootPairing.chainBotIdx i r = typeF4RootPairing.chainBotIdx i j) :
    typeF4RootPairing.chainBotCoeff i r ≤
      typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j := by
  have hm : typeF4RootPairing.root j +
      ((typeF4RootPairing.chainBotCoeff i r : ℤ) - typeF4RootPairing.chainBotCoeff i j) •
        typeF4RootPairing.root i ∈ Set.range typeF4RootPairing.root :=
    ⟨r, same_bottom_root_eq h⟩
  rw [typeF4RootPairing.root_add_zsmul_mem_range_iff hlin, Set.mem_Icc] at hm
  omega

lemma rootStringIdx_same_bottom {i : typeF4RootPairing_base.support} {j : Root}
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j])
    {n : ℕ} (hn : n ≤ typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j) :
    typeF4RootPairing.chainBotIdx i (rootStringIdx i j hlin n hn) =
      typeF4RootPairing.chainBotIdx i j := by
  apply typeF4RootPairing.root.injective
  rw [typeF4RootPairing.root_chainBotIdx, root_rootStringIdx hlin hn,
    chainBotCoeff_rootStringIdx hlin hn]
  module

lemma rootStringIdx_eq_of_same_bottom {i : typeF4RootPairing_base.support} {j r : Root}
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j])
    (h : typeF4RootPairing.chainBotIdx i r = typeF4RootPairing.chainBotIdx i j) :
    rootStringIdx i j hlin (typeF4RootPairing.chainBotCoeff i r) (same_bottom_bound hlin h) = r := by
  apply typeF4RootPairing.root.injective
  rw [root_rootStringIdx_eq hlin, same_bottom_root_eq h]

lemma rootStringIdx_injective {i : typeF4RootPairing_base.support} {j : Root}
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j])
    {n m : ℕ} (hn : n ≤ typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j)
    (hm : m ≤ typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j)
    (h : rootStringIdx i j hlin n hn = rootStringIdx i j hlin m hm) : n = m := by
  have := congrArg (typeF4RootPairing.chainBotCoeff i) h
  simpa only [chainBotCoeff_rootStringIdx] using this

lemma rootStringIdx_position {i : typeF4RootPairing_base.support} {j : Root}
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j]) :
    rootStringIdx i j hlin (typeF4RootPairing.chainBotCoeff i j) (Nat.le_add_right _ _) = j := by
  apply typeF4RootPairing.root.injective
  rw [root_rootStringIdx_eq]
  simp

lemma rootStringIdx_length {i : typeF4RootPairing_base.support} {j : Root}
    (hlin : LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j])
    {n : ℕ} (hn : n ≤ typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j) :
    typeF4RootPairing.chainBotCoeff i (rootStringIdx i j hlin n hn) +
      typeF4RootPairing.chainTopCoeff i (rootStringIdx i j hlin n hn) =
        typeF4RootPairing.chainBotCoeff i j + typeF4RootPairing.chainTopCoeff i j := by
  rw [chainBotCoeff_rootStringIdx, chainTopCoeff_rootStringIdx]
  omega

lemma independent_iff {i : typeF4RootPairing_base.support} {j : Root} :
    LinearIndependent ℝ ![typeF4RootPairing.root i, typeF4RootPairing.root j] ↔
      j ≠ (i : Root) ∧ j ≠ (-i : Root) := by
  rw [RootPairing.IsReduced.linearIndependent_iff]
  constructor
  · rintro ⟨hj, hn⟩
    exact ⟨Ne.symm hj, fun h => hn (by rw [h]; change _ = -typeF4RootPairing.root (typeF4RootPairing.reflectionPerm i i); simp only [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, neg_neg])⟩
  · rintro ⟨hj, hn⟩
    refine ⟨Ne.symm hj, fun h => hn ?_⟩
    apply typeF4RootPairing.root.injective
    change _ = typeF4RootPairing.root (typeF4RootPairing.reflectionPerm i i)
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, h, neg_neg]


end Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts.SimpleSL2Multiplication
