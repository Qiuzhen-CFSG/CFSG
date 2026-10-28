module

public import Theory.SpecificGroups.UnitaryThree.MatrixGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-!
# The faithful full matrix action on the 28 isotropic points

Every member of `matrixGroup`, the full determinant-one isometry group of the
anti-diagonal Hermitian form, acts on `Point`. An affine point `(x,y)` is the
line of `(y,x,1)` and infinity is the line of `(1,0,0)`.

We normalize each nonzero isotropic image vector by its last nonzero outer
coordinate. Normalization is unique up to nonzero scalar multiplication, so
matrix multiplication induces composition of permutations. The elementary
coordinate facts and the three generator equations are checked by kernel
reduction over `Nine`; the action laws use matrix identities, without any
matrix-generation hypothesis.

For faithfulness, fixing the four isotropic lines of `(1,0,0)`, `(0,0,1)`,
`(1,1,1)`, and `(1,i,1)` forces a matrix to be scalar. Its determinant is the
cube of that scalar, which equals one only for the scalar one in characteristic
three. The exported equations identify the root, torus, and swapping actions
with the existing permutation model.

Source: M. Suzuki, *A characterization of the 3-dimensional projective unitary
group over a finite field of odd characteristic*, J. Algebra 2 (1965),
Sections IV–VI; the projective action and its explicit Hermitian coordinates.
-/

public section

open FiniteField Matrix
open scoped Matrix
namespace UnitaryThree

private def pointVector : Point → (Fin 3 → Nine)
  | none => ![1, 0, 0]
  | some p => ![p.val.2, p.val.1, 1]

private def normalize (v : Fin 3 → Nine) : Point :=
  if v 2 = 0 then none else
    if h : v 0 / v 2 + star (v 0 / v 2) + star (v 1 / v 2) * (v 1 / v 2) = 0
    then some ⟨(v 1 / v 2, v 0 / v 2), h⟩ else none

private def pivot (v : Fin 3 → Nine) : Nine := if v 2 = 0 then v 0 else v 2

private theorem vector_normalize (v : Fin 3 → Nine) (hn : v ≠ 0)
    (hi : star v ⬝ᵥ (gram *ᵥ v) = 0) :
    pivot v ≠ 0 ∧ v = pivot v • pointVector (normalize v) := by
  have h : ∀ a b c : Nine, ![a, b, c] ≠ 0 →
      star ![a, b, c] ⬝ᵥ (gram *ᵥ ![a, b, c]) = 0 →
      pivot ![a, b, c] ≠ 0 ∧
      ![a, b, c] = pivot ![a, b, c] • pointVector (normalize ![a, b, c]) := by
    decide +kernel
  have hv : v = ![v 0, v 1, v 2] := by funext i; fin_cases i <;> rfl
  rw [hv] at hn hi ⊢
  exact h _ _ _ hn hi

private theorem normalize_smul (c : Nine) (hc : c ≠ 0) (p : Point) :
    normalize (c • pointVector p) = p := by
  have h : ∀ c : Nine, c ≠ 0 → ∀ p : Point,
      normalize (c • pointVector p) = p := by decide +kernel
  exact h c hc p

private theorem pointVector_nonzero (p : Point) : pointVector p ≠ 0 := by
  have h : ∀ p : Point, pointVector p ≠ 0 := by decide +kernel
  exact h p

private theorem pointVector_isotropic (p : Point) :
    star (pointVector p) ⬝ᵥ (gram *ᵥ pointVector p) = 0 := by
  have h : ∀ p : Point, star (pointVector p) ⬝ᵥ (gram *ᵥ pointVector p) = 0 := by
    decide +kernel
  exact h p

private theorem preserves_pairing (A : matrixGroup) (v : Fin 3 → Nine) :
    star (A.val.val *ᵥ v) ⬝ᵥ (gram *ᵥ (A.val.val *ᵥ v)) =
      star v ⬝ᵥ (gram *ᵥ v) := by
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, dotProduct_mulVec,
    vecMul_vecMul, A.property, ← dotProduct_mulVec]

private def actionFun (A : matrixGroup) (p : Point) : Point :=
  normalize (A.val.val *ᵥ pointVector p)

private theorem actionFun_spec (A : matrixGroup) (p : Point) :
    ∃ c : Nine, c ≠ 0 ∧ A.val.val *ᵥ pointVector p = c • pointVector (actionFun A p) := by
  have hn : A.val.val *ᵥ pointVector p ≠ 0 := by
    intro h
    apply pointVector_nonzero p
    have he := congrArg (fun v => (A⁻¹).val.val *ᵥ v) h
    simpa only [mulVec_mulVec, ← SpecialLinearGroup.coe_mul, ← Subgroup.coe_mul,
      inv_mul_cancel, Subgroup.coe_one, SpecialLinearGroup.coe_one, one_mulVec,
      mulVec_zero] using he
  exact ⟨_, vector_normalize _ hn (by rw [preserves_pairing, pointVector_isotropic])⟩

private theorem actionFun_one (p : Point) : actionFun 1 p = p := by
  change normalize ((1 : Matrix (Fin 3) (Fin 3) Nine) *ᵥ pointVector p) = p
  simpa using normalize_smul 1 one_ne_zero p

private theorem actionFun_mul (A B : matrixGroup) (p : Point) :
    actionFun (A * B) p = actionFun A (actionFun B p) := by
  obtain ⟨b, hb, he⟩ := actionFun_spec B p
  obtain ⟨a, ha, hf⟩ := actionFun_spec A (actionFun B p)
  change normalize ((A.val.val * B.val.val) *ᵥ pointVector p) = _
  rw [← mulVec_mulVec, he, mulVec_smul, hf, smul_smul]
  exact normalize_smul _ (mul_ne_zero hb ha) _

-- Packaging the explicit coordinate action requires additional elaboration heartbeats.
set_option maxHeartbeats 800000 in
/-- The full special unitary matrix group acts on its 28 isotropic lines. -/
def matrixAction : matrixGroup →* Equiv.Perm Point where
  toFun A :=
    { toFun := actionFun A
      invFun := actionFun A⁻¹
      left_inv p := by rw [← actionFun_mul, inv_mul_cancel, actionFun_one]
      right_inv p := by rw [← actionFun_mul, mul_inv_cancel, actionFun_one] }
  map_one' := by apply Equiv.ext; intro p; exact actionFun_one p
  map_mul' A B := by apply Equiv.ext; intro p; exact actionFun_mul A B p

private theorem frame_scalar (M : Matrix (Fin 3) (Fin 3) Nine)
    (a b c d : Nine)
    (h0 : M *ᵥ ![1, 0, 0] = a • ![1, 0, 0])
    (h2 : M *ᵥ ![0, 0, 1] = b • ![0, 0, 1])
    (h1 : M *ᵥ ![1, 1, 1] = c • ![1, 1, 1])
    (hi : M *ᵥ ![1, ⟨0, 1⟩, 1] = d • ![1, ⟨0, 1⟩, 1]) :
    M = c • (1 : Matrix (Fin 3) (Fin 3) Nine) := by
  have hcol0 (j : Fin 3) : M j 0 = a * (![1, 0, 0] : Fin 3 → Nine) j := by
    simpa [mulVec, dotProduct, Fin.sum_univ_succ] using congrFun h0 j
  have hcol2 (j : Fin 3) : M j 2 = b * (![0, 0, 1] : Fin 3 → Nine) j := by
    simpa [mulVec, dotProduct, Fin.sum_univ_succ] using congrFun h2 j
  have hrow (j : Fin 3) : M j 0 + M j 1 + M j 2 = c := by
    have hv : (![1, 1, 1] : Fin 3 → Nine) j = 1 := by fin_cases j <;> rfl
    simpa [mulVec, dotProduct, Fin.sum_univ_succ, add_assoc, hv] using congrFun h1 j
  have hrowi (j : Fin 3) : M j 0 + M j 1 * (⟨0, 1⟩ : Nine) + M j 2 =
      d * (![1, ⟨0, 1⟩, 1] : Fin 3 → Nine) j := by
    simpa [mulVec, dotProduct, Fin.sum_univ_succ, add_assoc] using congrFun hi j
  have hmid : M 1 1 = c := by simpa [hcol0, hcol2] using hrow 1
  have hcd : c = d := by
    apply mul_right_cancel₀ (show (⟨0, 1⟩ : Nine) ≠ 0 by decide)
    simpa [hcol0, hcol2, hmid] using hrowi 1
  subst d
  have hz (j : Fin 3) (hj : j = 0 ∨ j = 2) : M j 1 = 0 := by
    have hh : M j 1 * ((⟨0, 1⟩ : Nine) - 1) = 0 := by
      have hh := hrowi j
      have hv : (![1, ⟨0, 1⟩, 1] : Fin 3 → Nine) j = 1 := by
        rcases hj with rfl | rfl <;> rfl
      rw [hv, mul_one] at hh
      linear_combination hh - hrow j
    exact (mul_eq_zero.mp hh).resolve_right (by decide)
  have ha : a = c := by simpa [hcol0, hcol2, hz 0 (Or.inl rfl)] using hrow 0
  have hb : b = c := by simpa [hcol0, hcol2, hz 2 (Or.inr rfl)] using hrow 2
  apply Matrix.ext
  intro j k
  fin_cases k
  · fin_cases j <;> simp [hcol0, ha]
  · fin_cases j <;> simp [hz, hmid]
  · fin_cases j <;> simp [hcol2, hb]

/-- The full special unitary group acts faithfully on its isotropic lines. -/
theorem matrixAction_injective : Function.Injective matrixAction := by
  apply (injective_iff_map_eq_one matrixAction).mpr
  intro A hA
  have hfix (p : Point) : actionFun A p = p := by
    exact congrArg (fun f : Equiv.Perm Point => f p) hA
  have hs (p : Point) : ∃ c : Nine, c ≠ 0 ∧
      A.val.val *ᵥ pointVector p = c • pointVector p := by
    simpa only [hfix] using actionFun_spec A p
  obtain ⟨a, _, ha⟩ := hs none
  obtain ⟨b, _, hb⟩ := hs (some 1)
  obtain ⟨c, _, hc⟩ := hs (some ⟨(1, 1), by decide⟩)
  obtain ⟨d, _, hd⟩ := hs (some ⟨(⟨0, 1⟩, 1), by decide⟩)
  have he := frame_scalar A.val.val a b c d ha hb hc hd
  have hdet : c ^ 3 = 1 := by
    have h := A.val.property
    rw [he, Matrix.det_smul] at h
    simpa using h
  have hc1 : c = 1 := by
    have h : ∀ c : Nine, c ^ 3 = 1 → c = 1 := by decide +kernel
    exact h c hdet
  apply Subtype.ext
  apply Subtype.ext
  simpa [hc1] using he

/-- Root matrices induce the root-group translations. -/
@[simp] theorem matrixAction_root (p : Root) : matrixAction (matrixRoot p) = rootPerm p := by
  apply Equiv.ext
  intro q
  change actionFun (matrixRoot p) q = rootPerm p q
  have h : ∀ p : Root, ∀ q : Point, actionFun (matrixRoot p) q = rootPerm p q := by
    decide +kernel
  exact h p q

/-- Torus matrices induce the coordinate scaling permutations. -/
@[simp] theorem matrixAction_torus (r : Nineˣ) : matrixAction (matrixTorus r) = torusPerm r := by
  apply Equiv.ext
  intro q
  change actionFun (matrixTorus r) q = torusPerm r q
  have h : ∀ r : Nineˣ, ∀ q : Point, actionFun (matrixTorus r) q = torusPerm r q := by
    decide +kernel
  exact h r q

/-- The Weyl matrix induces reciprocal coordinates and exchanges zero and infinity. -/
@[simp] theorem matrixAction_swap : matrixAction matrixSwap = swapPerm := by
  apply Equiv.ext
  intro q
  change actionFun matrixSwap q = swapPerm q
  have h : ∀ q : Point, actionFun matrixSwap q = swapPerm q := by decide +kernel
  exact h q

end UnitaryThree

end
