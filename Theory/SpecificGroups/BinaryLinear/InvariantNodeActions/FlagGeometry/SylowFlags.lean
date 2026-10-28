module

public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.FlagGeometry.InvariantSubspaces
public import Theory.SpecificGroups.LinearSylowNormalizers.Triangular

/-!
# Common Sylow subgroups align actual binary flags

Transport the general unitriangular Sylow subgroup through the specified
SL-to-linear equivalence. A coordinate calculation identifies its image with
the standard full flag stabilizer; Sylow conjugacy transports the basis.
Invariant-subspace reconstruction then aligns all retained cuts in any
partial flag containing this Sylow, preserving the original node labels.

This discharges the common-Sylow basis premise in the two-minimal-parabolic
argument of Aschbacher–Smith 13.8.25, printed pp.959–960 of `refs/quasithin.pdf`.
It works in every positive dimension and uses no automorphism classification.
-/

@[expose] public section

namespace BinaryLinear.InvariantNodeActions
open OuterCyclic
open scoped MatrixGroups

private noncomputable def standardBasis (m : ℕ) : Basis m :=
  Pi.basisFun (ZMod 2) (Fin (m + 1))

private theorem mem_standard_cutSpace {m : ℕ} (i : Fin m) (v : Space (m + 1)) :
    v ∈ cutSpace (standardBasis m) i ↔ ∀ j : Fin (m + 1), i.val < j.val → v j = 0 := by
  rw [cutSpace, Module.Basis.mem_span_image]
  simp only [Set.subset_def, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_ofPred_eq]
  change (∀ j : Fin (m + 1), v j ≠ 0 → j.val ≤ i.val) ↔ _
  constructor
  · intro h j hj
    by_contra hv
    exact Nat.not_le_of_gt hj (h j hv)
  · intro h j hj
    by_contra hle
    exact hj (h j (Nat.lt_of_not_ge hle))

private theorem standard_fullFlag_iff_upperTriangular {m : ℕ}
    (A : SL(m + 1, ZMod 2)) :
    slEquivLinear (m + 1) A ∈ cutStabilizer (standardBasis m) Set.univ ↔
      A.val.IsUpperTriangular := by
  rw [mem_cutStabilizer_maps]
  constructor
  · intro h i j hji
    let k : Fin m := ⟨j.val, by have := i.isLt; change j.val < i.val at hji; omega⟩
    have hv := h k (Set.mem_univ _) ((standardBasis m) j)
      ((basis_mem_cutSpace _ k j).mpr le_rfl)
    have hz := (mem_standard_cutSpace k _).mp hv i hji
    simpa only [slEquivLinear_apply, standardBasis, Pi.basisFun_apply,
      Matrix.mulVec_single_one, Matrix.col_apply] using hz
  · intro h i _ v hv
    apply (mem_standard_cutSpace i _).mpr
    intro j hj
    rw [slEquivLinear_apply, Matrix.mulVec, dotProduct]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hk : i.val < k.val
    · rw [(mem_standard_cutSpace i v).mp hv k hk, mul_zero]
    · rw [h (show k < j from by change k.val < j.val; omega), zero_mul]

private theorem standard_unipotent_map {m : ℕ} :
    (Theory.SpecificGroups.LinearSylowNormalizers.unipotent (m + 1) (ZMod 2)).map
      (slEquivLinear (m + 1)).toMonoidHom = cutStabilizer (standardBasis m) Set.univ := by
  ext g
  obtain ⟨A, rfl⟩ := (slEquivLinear (m + 1)).surjective g
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply,
    Theory.SpecificGroups.LinearSylowNormalizers.mem_unipotent,
    Theory.SpecificGroups.LinearSylowNormalizers.mem_borel,
    standard_fullFlag_iff_upperTriangular]
  constructor
  · exact And.left
  · intro h
    refine ⟨h, fun i => ?_⟩
    have hd := A.property
    rw [Matrix.det_of_isUpperTriangular h] at hd
    have hp : (∏ j, A.val j j) ≠ 0 := by rw [hd]; exact one_ne_zero
    have hi := Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)
    exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hi

/-- Every Sylow two-subgroup is the actual stabilizer of a full binary flag.
The general unitriangular Sylow construction supplies this in every dimension. -/
theorem sylow_eq_cutStabilizer {m : ℕ} (T : Sylow 2 (LinearGroup (m + 1))) :
    ∃ b : Basis m, (T : Subgroup (LinearGroup (m + 1))) = cutStabilizer b Set.univ := by
  let : Finite (LinearGroup (m + 1)) :=
    Finite.of_injective (fun g : LinearGroup (m + 1) => (g : Space (m + 1) → Space (m + 1)))
      DFunLike.coe_injective
  let S := (Theory.SpecificGroups.LinearSylowNormalizers.standardSylow
    (m + 1) (ZMod 2) (Nat.succ_pos m)).mapSurjective (f := (slEquivLinear (m + 1)).toMonoidHom)
      (slEquivLinear (m + 1)).surjective
  have hS : (S : Subgroup (LinearGroup (m + 1))) = cutStabilizer (standardBasis m) Set.univ := by
    change ((Theory.SpecificGroups.LinearSylowNormalizers.standardSylow
      (m + 1) (ZMod 2) (Nat.succ_pos m) : Subgroup SL(m + 1, ZMod 2)).map
        (slEquivLinear (m + 1)).toMonoidHom) = _
    rw [Theory.SpecificGroups.LinearSylowNormalizers.coe_standardSylow]
    exact standard_unipotent_map
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (LinearGroup (m + 1)) S T
  have he : (cutStabilizer (standardBasis m) Set.univ).map (MulAut.conj g).toMonoidHom =
      (T : Subgroup (LinearGroup (m + 1))) := by
    rw [← hS]
    change ((g • S : Sylow 2 (LinearGroup (m + 1))) : Subgroup (LinearGroup (m + 1))) = _
    rw [hg]
  exact ⟨(standardBasis m).map g, he.symm.trans (cutStabilizer_map_conj _ _ _)⟩

/-- A common Sylow aligns different original bases without changing node labels. -/
theorem commonSylow_minimalParabolic_alignment {m : ℕ}
    (b c : Basis m) (i j : Fin m) (T : Sylow 2 (LinearGroup (m + 1)))
    (hP : (T : Subgroup (LinearGroup (m + 1))) ≤ minimalParabolic b i)
    (hQ : (T : Subgroup (LinearGroup (m + 1))) ≤ minimalParabolic c j) :
    ∃ d : Basis m, (T : Subgroup (LinearGroup (m + 1))) = cutStabilizer d Set.univ ∧
      minimalParabolic b i = minimalParabolic d i ∧
      minimalParabolic c j = minimalParabolic d j := by
  obtain ⟨d, hd⟩ := sylow_eq_cutStabilizer T
  refine ⟨d, hd, ?_, ?_⟩
  · exact cutStabilizer_eq_of_fullFlag_le d b {i}ᶜ (hd ▸ hP)
  · exact cutStabilizer_eq_of_fullFlag_le d c {j}ᶜ (hd ▸ hQ)

end BinaryLinear.InvariantNodeActions
