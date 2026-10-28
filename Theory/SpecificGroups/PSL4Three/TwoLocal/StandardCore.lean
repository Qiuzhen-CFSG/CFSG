module

public import Theory.SpecificGroups.PSL4Three.TwoLocal.StandardInvolution
public import Theory.PGroupCore
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The two-core of the split involution centralizer in PSL₄(3)

The two block quaternion groups have a normal two-group image in the actual
projective centralizer. Every lift in this centralizer is block diagonal or
interchanges the two blocks. Conjugation preserves the quaternion image in
both cases. An element centralizing the image must be block diagonal, and
its two blocks must be scalar. Thus this image is self-centralizing.
Its containment in the intrinsic two-core proves the desired core-centralizer
inequality. The small two-by-two matrix calculations are kernel checked.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), printed pp.3–4,
repeated as Theorem 0.1.1(4), printed pp.481–482 of `refs/quasithin.pdf`.
-/

open Matrix
namespace Matrix.PSL4Three.TwoLocal.StandardCore
private abbrev Mat₂ := Matrix (Fin 2) (Fin 2) (ZMod 3)
private abbrev Mat₄ := Matrix (Fin 4) (Fin 4) (ZMod 3)

private def quaternionI : Mat₂ := !![0, 1; -1, 0]
private def quaternionJ : Mat₂ := !![1, 1; 1, -1]
private def quaternionMatrix : QuaternionGroup 2 → Mat₂
  | .a k => quaternionI ^ k.val
  | .xa k => quaternionJ * quaternionI ^ k.val

private def quaternionMatrixHom : QuaternionGroup 2 →* Mat₂ where
  toFun := quaternionMatrix
  map_one' := by decide
  map_mul' := by
    exact (by decide +kernel : ∀ x y, quaternionMatrix (x * y) =
      quaternionMatrix x * quaternionMatrix y)

private theorem quaternionMatrix_det (q : QuaternionGroup 2) : (quaternionMatrix q).det = 1 := by
  rcases q with i | i <;> fin_cases i <;> decide

private def block (A B : Mat₂) : Mat₄ :=
  !![A 0 0, A 0 1, 0, 0;
     A 1 0, A 1 1, 0, 0;
     0, 0, B 0 0, B 0 1;
     0, 0, B 1 0, B 1 1]

private theorem block_one : block 1 1 = 1 := by decide

private theorem block_mul (A B C D : Mat₂) : block A B * block C D = block (A * C) (B * D) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem block_det (A B : Mat₂) : (block A B).det = A.det * B.det := by
  have h : block A B = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B) := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

private def quaternionPairSL : (QuaternionGroup 2 × QuaternionGroup 2) →* SL where
  toFun q := ⟨block (quaternionMatrix q.1) (quaternionMatrix q.2), by
    rw [block_det, quaternionMatrix_det, quaternionMatrix_det, one_mul]⟩
  map_one' := by
    apply Subtype.ext
    change block (quaternionMatrixHom 1) (quaternionMatrixHom 1) = 1
    rw [map_one, block_one]
  map_mul' x y := by
    apply Subtype.ext
    change block (quaternionMatrixHom (x.1 * y.1)) (quaternionMatrixHom (x.2 * y.2)) = _
    rw [map_mul, map_mul]
    exact (block_mul _ _ _ _).symm

private theorem block_commutes_standard (A B : Mat₂) :
    block A B * standardInvolutionMatrix = standardInvolutionMatrix * block A B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, standardInvolutionMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private def quaternionPair : (QuaternionGroup 2 × QuaternionGroup 2) →* standardCentralizer :=
  (project.comp quaternionPairSL).codRestrict _ (by
    intro q
    exact (project_mem_standardCentralizer_iff _).mpr
      (Or.inl (block_commutes_standard _ _)))

/-- The image of the two block quaternion groups inside the full centralizer. -/
public def quaternionCore : Subgroup standardCentralizer := quaternionPair.range

/-- The block quaternion image is a two-group. -/
public theorem quaternionCore_isPGroup : IsPGroup 2 quaternionCore := by
  have hp : IsPGroup 2 (QuaternionGroup 2 × QuaternionGroup 2) := by
    apply IsPGroup.of_card (n := 6)
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card, QuaternionGroup.card]
  exact hp.of_surjective quaternionPair.rangeRestrict quaternionPair.rangeRestrict_surjective

private theorem quaternionPair_mem (q : QuaternionGroup 2 × QuaternionGroup 2) :
    quaternionPair q ∈ quaternionCore := ⟨q, rfl⟩

private def topBlock (M : Mat₄) : Mat₂ := !![M 0 0, M 0 1; M 1 0, M 1 1]
private def bottomBlock (M : Mat₄) : Mat₂ := !![M 2 2, M 2 3; M 3 2, M 3 3]

private theorem commuting_shape (M : Mat₄)
    (h : M * standardInvolutionMatrix = standardInvolutionMatrix * M) :
    M = block (topBlock M) (bottomBlock M) := by
  have hneg : ∀ x : ZMod 3, -x = x ↔ x = 0 := by decide
  have hneg' : ∀ x : ZMod 3, x = -x ↔ x = 0 := by decide
  ext i j
  have he := congrArg (fun A : Mat₄ => A i j) h
  fin_cases i <;> fin_cases j <;>
    first | rfl | simpa [block, topBlock, bottomBlock, standardInvolutionMatrix,
      Matrix.mul_apply, Fin.sum_univ_succ, hneg, hneg'] using he

private theorem swap_sq : blockSwapMatrix * blockSwapMatrix = 1 := by decide

private theorem swap_det : blockSwapMatrix.det = 1 := by decide

private theorem swap_anticommutes : blockSwapMatrix * standardInvolutionMatrix =
    -(standardInvolutionMatrix * blockSwapMatrix) := by decide

private theorem swap_block (A B : Mat₂) :
    blockSwapMatrix * block A B = block B A * blockSwapMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, blockSwapMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem lift_shape (g : SL) (hg : project g ∈ standardCentralizer) :
    ∃ A B : Mat₂, g.val = block A B ∨ g.val = block A B * blockSwapMatrix := by
  rcases (project_mem_standardCentralizer_iff g).mp hg with h | h
  · exact ⟨_, _, Or.inl (commuting_shape g.val h)⟩
  · have hc : (g.val * blockSwapMatrix) * standardInvolutionMatrix =
        standardInvolutionMatrix * (g.val * blockSwapMatrix) := by
      rw [mul_assoc, swap_anticommutes, mul_neg, ← mul_assoc, h, neg_mul,
        neg_neg, mul_assoc]
    have hs := commuting_shape (g.val * blockSwapMatrix) hc
    refine ⟨topBlock (g.val * blockSwapMatrix), bottomBlock (g.val * blockSwapMatrix), Or.inr ?_⟩
    rw [← hs, mul_assoc, swap_sq, mul_one]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
private theorem quaternion_intertwine : ∀ A : Mat₂, A.det ≠ 0 →
    ∀ q : QuaternionGroup 2, ∃ r : QuaternionGroup 2,
      A * quaternionMatrix q = quaternionMatrix r * A := by
  decide +kernel

private theorem block_intertwine (A B : Mat₂) (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (q : QuaternionGroup 2 × QuaternionGroup 2) :
    ∃ r : QuaternionGroup 2 × QuaternionGroup 2,
      block A B * (quaternionPairSL q).val = (quaternionPairSL r).val * block A B := by
  obtain ⟨a, ha⟩ := quaternion_intertwine A hA q.1
  obtain ⟨b, hb⟩ := quaternion_intertwine B hB q.2
  refine ⟨(a,b), ?_⟩
  change block A B * block _ _ = block _ _ * block A B
  rw [block_mul, block_mul, ha, hb]

private theorem lift_intertwine (g : SL) (hg : project g ∈ standardCentralizer)
    (q : QuaternionGroup 2 × QuaternionGroup 2) :
    ∃ r : QuaternionGroup 2 × QuaternionGroup 2,
      g * quaternionPairSL q = quaternionPairSL r * g := by
  obtain ⟨A, B, h | h⟩ := lift_shape g hg
  · have hd : A.det * B.det = 1 := by rw [← block_det, ← h]; exact g.property
    have hA : A.det ≠ 0 := fun hz => by simp [hz] at hd
    have hB : B.det ≠ 0 := fun hz => by simp [hz] at hd
    obtain ⟨r, hr⟩ := block_intertwine A B hA hB q
    refine ⟨r, Subtype.ext ?_⟩
    change g.val * (quaternionPairSL q).val = (quaternionPairSL r).val * g.val
    rwa [h]
  · have hd : A.det * B.det = 1 := by
      have hh := g.property
      rw [h, Matrix.det_mul, block_det, swap_det, mul_one] at hh
      exact hh
    have hA : A.det ≠ 0 := fun hz => by simp [hz] at hd
    have hB : B.det ≠ 0 := fun hz => by simp [hz] at hd
    obtain ⟨r, hr⟩ := block_intertwine A B hA hB (q.2, q.1)
    refine ⟨r, Subtype.ext ?_⟩
    change g.val * block (quaternionMatrix q.1) (quaternionMatrix q.2) =
      (quaternionPairSL r).val * g.val
    rw [h, mul_assoc, swap_block, ← mul_assoc]
    change (block A B * (quaternionPairSL (q.2, q.1)).val) * blockSwapMatrix = _
    rw [hr, mul_assoc]

/-- Normality is intrinsic to the full projective centralizer, including block interchange. -/
public theorem quaternionCore_normal : quaternionCore.Normal := by
  constructor
  rintro x ⟨q, rfl⟩ g
  obtain ⟨a, ha⟩ := project_surjective g.val
  obtain ⟨r, hr⟩ := lift_intertwine a (by rw [ha]; exact g.property) q
  refine ⟨r, ?_⟩
  apply Subtype.ext
  change project (quaternionPairSL r) = g.val * project (quaternionPairSL q) * g.val⁻¹
  rw [← ha, ← map_mul, ← map_inv, ← map_mul]
  exact congrArg project (by rw [hr, mul_inv_cancel_right])

private theorem topBlock_block (A B : Mat₂) : topBlock (block A B) = A := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem bottomBlock_block (A B : Mat₂) : bottomBlock (block A B) = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem block_neg (A B : Mat₂) : -(block A B) = block (-A) (-B) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [block]

private theorem block_eq_iff (A B C D : Mat₂) : block A B = block C D ↔ A = C ∧ B = D := by
  constructor
  · intro h
    exact ⟨by simpa only [topBlock_block] using congrArg topBlock h,
      by simpa only [bottomBlock_block] using congrArg bottomBlock h⟩
  · rintro ⟨rfl, rfl⟩; rfl

private theorem nonsingular_ne_neg : ∀ A : Mat₂, A.det ≠ 0 → A ≠ -A := by decide +kernel

private theorem quaternion_centralizer : ∀ A : Mat₂, A.det ≠ 0 →
    A * quaternionI = quaternionI * A → A * quaternionJ = quaternionJ * A →
    A = 1 ∨ A = -1 := by decide +kernel

private theorem quaternionI_no_signed_fixed : ∀ A : Mat₂, A.det ≠ 0 →
    A ≠ quaternionI * A ∧ A ≠ -(quaternionI * A) := by decide +kernel

private theorem block_project_commute_left (A B U : Mat₂) (hB : B.det ≠ 0)
    (h : block A B * block U 1 = block U 1 * block A B ∨
      block A B * block U 1 = -(block U 1 * block A B)) :
    A * U = U * A := by
  simp only [block_mul, mul_one, one_mul, block_neg, block_eq_iff] at h
  rcases h with h | h
  · exact h.1
  · exact (nonsingular_ne_neg B hB h.2).elim

private theorem block_project_commute_right (A B U : Mat₂) (hA : A.det ≠ 0)
    (h : block A B * block 1 U = block 1 U * block A B ∨
      block A B * block 1 U = -(block 1 U * block A B)) :
    B * U = U * B := by
  simp only [block_mul, mul_one, one_mul, block_neg, block_eq_iff] at h
  rcases h with h | h
  · exact h.2
  · exact (nonsingular_ne_neg A hA h.1).elim

private theorem offdiag_mul_block (A B U V : Mat₂) :
    (block A B * blockSwapMatrix) * block U V * blockSwapMatrix =
      block (A * V) (B * U) := by
  rw [mul_assoc (block A B), swap_block, ← mul_assoc (block A B), mul_assoc,
    swap_sq, mul_one, block_mul]

private theorem block_mul_offdiag (A B U V : Mat₂) :
    block U V * (block A B * blockSwapMatrix) * blockSwapMatrix =
      block (U * A) (V * B) := by
  rw [← mul_assoc, mul_assoc _ blockSwapMatrix, swap_sq, mul_one, block_mul]

private theorem offdiag_not_project_commute (A B : Mat₂) (hA : A.det ≠ 0)
    (h : (block A B * blockSwapMatrix) * block quaternionI 1 =
        block quaternionI 1 * (block A B * blockSwapMatrix) ∨
      (block A B * blockSwapMatrix) * block quaternionI 1 =
        -(block quaternionI 1 * (block A B * blockSwapMatrix))) : False := by
  rcases h with h | h
  · have he := congrArg (fun M : Mat₄ => M * blockSwapMatrix) h
    rw [offdiag_mul_block, block_mul_offdiag, mul_one, one_mul, block_eq_iff] at he
    exact (quaternionI_no_signed_fixed A hA).1 he.1
  · have he := congrArg (fun M : Mat₄ => M * blockSwapMatrix) h
    rw [offdiag_mul_block, neg_mul, block_mul_offdiag, mul_one, one_mul,
      block_neg, block_eq_iff] at he
    exact (quaternionI_no_signed_fixed A hA).2 he.1

/-- Centralizing both block quaternion factors forces membership in their image. -/
public theorem quaternionCore_selfCentralizing :
    Subgroup.centralizer (quaternionCore : Set standardCentralizer) ≤ quaternionCore := by
  intro x hx
  obtain ⟨g, hg⟩ := project_surjective x.val
  have hc (q : QuaternionGroup 2 × QuaternionGroup 2) :
      g.val * (quaternionPairSL q).val = (quaternionPairSL q).val * g.val ∨
      g.val * (quaternionPairSL q).val = -((quaternionPairSL q).val * g.val) := by
    apply (project_commute_iff _ _).mp
    have he := (Subgroup.mem_centralizer_iff.mp hx) (quaternionPair q) (quaternionPair_mem q)
    have he' := congrArg (fun y : standardCentralizer => y.val) he.symm
    change x.val * project (quaternionPairSL q) = project (quaternionPairSL q) * x.val at he'
    rwa [hg]
  obtain ⟨A, B, he | he⟩ := lift_shape g (by rw [hg]; exact x.property)
  · have hd : A.det * B.det = 1 := by rw [← block_det, ← he]; exact g.property
    have hA : A.det ≠ 0 := fun hz => by simp [hz] at hd
    have hB : B.det ≠ 0 := fun hz => by simp [hz] at hd
    have hleft (q : QuaternionGroup 2) : A * quaternionMatrix q = quaternionMatrix q * A := by
      apply block_project_commute_left A B _ hB
      have hv : (quaternionPairSL (q, 1)).val = block (quaternionMatrix q) 1 := by
        change block (quaternionMatrix q) (quaternionMatrixHom 1) = _
        rw [map_one]
      simpa only [he, hv] using hc (q, 1)
    have hright (q : QuaternionGroup 2) : B * quaternionMatrix q = quaternionMatrix q * B := by
      apply block_project_commute_right A B _ hA
      have hv : (quaternionPairSL (1, q)).val = block 1 (quaternionMatrix q) := by
        change block (quaternionMatrixHom 1) (quaternionMatrix q) = _
        rw [map_one]
      simpa only [he, hv] using hc (1, q)
    have hi : quaternionMatrix (.a 1) = quaternionI := by decide
    have hj : quaternionMatrix (.xa 0) = quaternionJ := by decide
    have ha := quaternion_centralizer A hA (by simpa only [hi] using hleft (.a 1))
      (by simpa only [hj] using hleft (.xa 0))
    have hb := quaternion_centralizer B hB (by simpa only [hi] using hright (.a 1))
      (by simpa only [hj] using hright (.xa 0))
    have hsign : ∀ U : Mat₂, U = 1 ∨ U = -1 → ∃ q, quaternionMatrix q = U := by
      intro U hU
      rcases hU with rfl | rfl
      · exact ⟨1, by decide⟩
      · exact ⟨.a 2, by decide⟩
    obtain ⟨a, ha⟩ := hsign A ha
    obtain ⟨b, hb⟩ := hsign B hb
    refine ⟨(a, b), ?_⟩
    apply Subtype.ext
    change project (quaternionPairSL (a,b)) = x.val
    rw [← hg]
    congr 1
    apply Subtype.ext
    change block (quaternionMatrix a) (quaternionMatrix b) = g.val
    rw [ha, hb, he]
  · have hd : A.det * B.det = 1 := by
      have hh := g.property
      rw [he, Matrix.det_mul, block_det, swap_det, mul_one] at hh
      exact hh
    have hA : A.det ≠ 0 := fun hz => by simp [hz] at hd
    exact (offdiag_not_project_commute A B hA (by
      have hh := hc (.a 1, 1)
      have hi : (quaternionPairSL (.a 1, 1)).val = block quaternionI 1 := by decide
      simpa only [he, hi] using hh)).elim

end Matrix.PSL4Three.TwoLocal.StandardCore

namespace Matrix.PSL4Three.TwoLocal

/-- The full centralizer of the split involution in PSL₄(3) has self-centralizing
intrinsic two-core. -/
public theorem standardCentralizer_centralizer_twoCore_le :
    Subgroup.centralizer (pCore 2 standardCentralizer : Set standardCentralizer) ≤
      pCore 2 standardCentralizer := by
  have hQ : StandardCore.quaternionCore ≤ pCore 2 standardCentralizer :=
    le_sSup ⟨StandardCore.quaternionCore_normal, StandardCore.quaternionCore_isPGroup⟩
  exact (Subgroup.centralizer_le hQ).trans
    (StandardCore.quaternionCore_selfCentralizing.trans hQ)

end Matrix.PSL4Three.TwoLocal
