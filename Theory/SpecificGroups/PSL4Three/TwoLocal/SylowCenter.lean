module

public import Theory.SpecificGroups.PSL4Three.TwoLocal.StandardInvolution
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Central involutions in a Sylow two-subgroup of PSL₄(3)

The images of two quaternion groups acting on complementary two-dimensional
blocks form a two-subgroup. Its centralizer in the actual projective group
consists only of the identity and the image of diag(-1,-1,1,1). Any Sylow
two-subgroup containing this image therefore has just this possible central
involution, which identifies its full ambient centralizer.

For the matrix calculation, each chosen quaternion generator acts trivially on
the other block and hence has trace two. Projective commutation cannot be
anticommutation for such a generator, since conjugation preserves trace.
Ordinary commutation with the four generators then forces a scalar on each
block. Over the field of three elements, invertibility leaves just four
matrices, giving two projective images. This treats all projective elements,
including those whose lifts square to minus the identity.

Source application: Aschbacher–Smith, Theorem 0.1.2(4), printed pp.3–4,
repeated as Theorem 0.1.1(4), printed pp.481–482 of `refs/quasithin.pdf`.
The standard-centralizer two-core calculation is a separate result.
-/

namespace Matrix.PSL4Three.TwoLocal.SylowCenter
abbrev Mat₂ := Matrix (Fin 2) (Fin 2) (ZMod 3)
abbrev Mat₄ := Matrix (Fin 4) (Fin 4) (ZMod 3)
def quaternionI : Mat₂ := !![0, 1; -1, 0]
def quaternionJ : Mat₂ := !![-1, 1; 1, 1]
def quaternionMatrix : QuaternionGroup 2 → Mat₂
  | .a k => quaternionI ^ k.val
  | .xa k => quaternionJ * quaternionI ^ k.val

def quaternionMatrixHom : QuaternionGroup 2 →* Mat₂ where
  toFun := quaternionMatrix
  map_one' := by decide
  map_mul' := by
    intro x y
    rcases x with i | i <;> rcases y with j | j <;>
      fin_cases i <;> fin_cases j <;> decide

theorem quaternionMatrix_det (q : QuaternionGroup 2) : (quaternionMatrix q).det = 1 := by
  rcases q with i | i <;> fin_cases i <;> decide

def block (A B : Mat₂) : Mat₄ :=
  !![A 0 0, A 0 1, 0, 0;
     A 1 0, A 1 1, 0, 0;
     0, 0, B 0 0, B 0 1;
     0, 0, B 1 0, B 1 1]

theorem block_one : block 1 1 = 1 := by decide

theorem block_mul (A B C D : Mat₂) : block A B * block C D = block (A * C) (B * D) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [block, Matrix.mul_apply, Fin.sum_univ_succ]

theorem block_det (A B : Mat₂) : (block A B).det = A.det * B.det := by
  have h : block A B = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]

def quaternionPairSL : (QuaternionGroup 2 × QuaternionGroup 2) →* SL where
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

def quaternionPair : (QuaternionGroup 2 × QuaternionGroup 2) →* PSL :=
  project.comp quaternionPairSL

theorem quaternionPair_isPGroup : IsPGroup 2 quaternionPair.range := by
  have hp : IsPGroup 2 (QuaternionGroup 2 × QuaternionGroup 2) := by
    apply IsPGroup.of_card (n := 6)
    norm_num [Nat.card_prod, Nat.card_eq_fintype_card, QuaternionGroup.card]
  exact hp.of_surjective quaternionPair.rangeRestrict quaternionPair.rangeRestrict_surjective

theorem commute_of_project_commute (g h : SL) (ht : h.val.trace ≠ -h.val.trace)
    (hc : project g * project h = project h * project g) :
    g.val * h.val = h.val * g.val := by
  rcases (project_commute_iff g h).mp hc with hc | hc
  · exact hc
  · have hi : g.val * (g⁻¹).val = 1 := by
      change (g * g⁻¹).val = 1
      rw [mul_inv_cancel]
      rfl
    have hi' : (g⁻¹).val * g.val = 1 := by
      change (g⁻¹ * g).val = 1
      rw [inv_mul_cancel]
      rfl
    have he := congrArg (fun A : Mat₄ => (A * (g⁻¹).val).trace) hc
    rw [trace_mul_cycle, hi', one_mul, neg_mul, Matrix.mul_assoc, hi, mul_one,
      trace_neg] at he
    exact (ht he).elim

theorem commuting_shape (A : Mat₄)
    (hI : A * block quaternionI 1 = block quaternionI 1 * A)
    (hJ : A * block quaternionJ 1 = block quaternionJ 1 * A)
    (hI' : A * block 1 quaternionI = block 1 quaternionI * A)
    (hJ' : A * block 1 quaternionJ = block 1 quaternionJ * A) :
    A = diagonal ![A 0 0, A 0 0, A 2 2, A 2 2] := by
  have h0 := congrArg (fun B : Mat₄ => B 0 0) hI
  have h1 := congrArg (fun B : Mat₄ => B 0 1) hI
  have h2 := congrArg (fun B : Mat₄ => B 0 2) hI
  have h3 := congrArg (fun B : Mat₄ => B 0 3) hI
  have h6 := congrArg (fun B : Mat₄ => B 1 2) hI
  have h7 := congrArg (fun B : Mat₄ => B 1 3) hI
  have h8 := congrArg (fun B : Mat₄ => B 2 0) hI
  have h9 := congrArg (fun B : Mat₄ => B 2 1) hI
  have h12 := congrArg (fun B : Mat₄ => B 3 0) hI
  have h13 := congrArg (fun B : Mat₄ => B 3 1) hI
  have h16 := congrArg (fun B : Mat₄ => B 0 0) hJ
  have h42 := congrArg (fun B : Mat₄ => B 2 2) hI'
  have h43 := congrArg (fun B : Mat₄ => B 2 3) hI'
  have h58 := congrArg (fun B : Mat₄ => B 2 2) hJ'
  simp [Matrix.mul_apply, Fin.sum_univ_succ, block, quaternionI, quaternionJ]
    at h0 h1 h2 h3 h6 h7 h8 h9 h12 h13 h16 h42 h43 h58
  have zero_pair : ∀ a b : ZMod 3, -a = b → a = b → a = 0 ∧ b = 0 := by decide
  obtain ⟨e01, e10⟩ := zero_pair _ _ h0 h16
  obtain ⟨e02, e12⟩ := zero_pair _ _ h6.symm h2
  obtain ⟨e03, e13⟩ := zero_pair _ _ h7.symm h3
  obtain ⟨e21, e20⟩ := zero_pair _ _ h8 h9.symm
  obtain ⟨e31, e30⟩ := zero_pair _ _ h12 h13.symm
  obtain ⟨e23, e32⟩ := zero_pair _ _ h42 h58
  ext i j
  fin_cases i <;> fin_cases j
  · rfl
  · exact e01
  · exact e02
  · exact e03
  · exact e10
  · exact h1.symm
  · exact e12
  · exact e13
  · exact e20
  · exact e21
  · rfl
  · exact e23
  · exact e30
  · exact e31
  · exact e32
  · exact h43.symm

theorem centralizing_quaternionPair (g : PSL)
    (hc : ∀ q, g * quaternionPair q = quaternionPair q * g) :
    g = 1 ∨ g = standardInvolution := by
  obtain ⟨g, rfl⟩ := project_surjective g
  have hi := commute_of_project_commute g (quaternionPairSL (.a 1, 1))
    (by decide) (hc (.a 1, 1))
  have hj := commute_of_project_commute g (quaternionPairSL (.xa 0, 1))
    (by decide) (hc (.xa 0, 1))
  have hi' := commute_of_project_commute g (quaternionPairSL (1, .a 1))
    (by decide) (hc (1, .a 1))
  have hj' := commute_of_project_commute g (quaternionPairSL (1, .xa 0))
    (by decide) (hc (1, .xa 0))
  have ei : (quaternionPairSL (.a 1, 1)).val = block quaternionI 1 := by decide
  have ej : (quaternionPairSL (.xa 0, 1)).val = block quaternionJ 1 := by decide
  have ei' : (quaternionPairSL (1, .a 1)).val = block 1 quaternionI := by decide
  have ej' : (quaternionPairSL (1, .xa 0)).val = block 1 quaternionJ := by decide
  rw [ei] at hi
  rw [ej] at hj
  rw [ei'] at hi'
  rw [ej'] at hj'
  have hs := commuting_shape g.val hi hj hi' hj'
  have hd : (diagonal ![g.val 0 0, g.val 0 0, g.val 2 2, g.val 2 2]).det = 1 := by
    rw [← hs]
    exact g.property
  have signs : ∀ a b : ZMod 3, (diagonal ![a, a, b, b]).det = 1 →
      ((diagonal ![a, a, b, b] : Mat₄) = 1 ∨ diagonal ![a, a, b, b] = -1) ∨
      (diagonal ![a, a, b, b] = standardInvolutionMatrix ∨
        diagonal ![a, a, b, b] = -standardInvolutionMatrix) := by decide
  rcases signs _ _ hd with he | he
  · left
    change project g = project 1
    apply (project_eq_iff g 1).mpr
    rw [hs]
    exact he
  · right
    change project g = project standardInvolutionSL
    apply (project_eq_iff g standardInvolutionSL).mpr
    rw [hs]
    exact he

end Matrix.PSL4Three.TwoLocal.SylowCenter

namespace Matrix.PSL4Three.TwoLocal

/-- A Sylow two-subgroup whose central involutions all equal the standard split
involution. Its existence follows by extending the concrete quaternion image. -/
public theorem exists_sylow_center_involution_eq_standard :
    ∃ T : Sylow 2 PSL, ∀ z : T, z ∈ Subgroup.center T → orderOf z = 2 →
      (z : PSL) = standardInvolution := by
  obtain ⟨T, hT⟩ := SylowCenter.quaternionPair_isPGroup.exists_le_sylow
  refine ⟨T, ?_⟩
  intro z hz ho
  have hc : ∀ q, (z : PSL) * SylowCenter.quaternionPair q =
      SylowCenter.quaternionPair q * z := by
    intro q
    have hq : SylowCenter.quaternionPair q ∈ T := hT ⟨q, rfl⟩
    exact congrArg (fun t : T => (t : PSL))
      ((Subgroup.mem_center_iff.mp hz) ⟨_, hq⟩).symm
  rcases SylowCenter.centralizing_quaternionPair z hc with he | he
  · have hz1 : z = 1 := Subtype.ext he
    rw [hz1, orderOf_one] at ho
    contradiction
  · exact he

/-- Every central involution in one Sylow two-subgroup has its full projective
centralizer isomorphic to the standard centralizer. -/
public theorem exists_sylow_center_centralizer_equiv :
    ∃ T : Sylow 2 PSL, ∀ z : T, z ∈ Subgroup.center T → orderOf z = 2 →
      Nonempty (Subgroup.centralizer ({(z : PSL)} : Set PSL) ≃* standardCentralizer) := by
  obtain ⟨T, hT⟩ := exists_sylow_center_involution_eq_standard
  refine ⟨T, ?_⟩
  intro z hz ho
  exact ⟨MulEquiv.subgroupCongr (by rw [hT z hz ho])⟩

end Matrix.PSL4Three.TwoLocal
