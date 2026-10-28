module

public import Theory.Representation.OrthogonalFourPlusMatrix.Action
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Data.Matrix.Basis
public import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
/-!
The natural determinant module over F₂ is irreducible. Explicit row-operation
witnesses reduce each nonzero matrix to a matrix unit or a sum of two orbit
vectors. The nondegenerate alternating polar form gives the dimensions of
marked hyperplanes and their intersections. Two root elements in a singular
point stabilizer generate its perpendicular space by displacement; conjugating
these calculations treats every nonzero singular point.

These are the matrix calculations used in Aschbacher–Smith G.2.6, printed
p.336, and 15.3.53–54, printed p.1146. The determinant action itself is the
ATLAS-adapted action in the imported module.
-/

@[expose] public noncomputable section
open Matrix ClassicalOrthogonal.FourPlusMatrix
namespace ClassicalOrthogonal.FourPlusMatrix.PrimeFieldTwo.ModuleGeometry
abbrev V := Mat (F := ZMod 2)
abbrev Actors := PairSL (F := ZMod 2)
private def rawSL : Fin 6 → V :=
  ![!![1,0;0,1], !![1,1;0,1], !![1,0;1,1],
    !![0,1;1,0], !![0,1;1,1], !![1,1;1,0]]
private def sl (i : Fin 6) : SpecialLinearGroup (Fin 2) (ZMod 2) :=
  ⟨rawSL i, by fin_cases i <;> norm_num [rawSL, det_fin_two] <;> decide⟩
private def actor (i j : Fin 6) : Actors := (sl i, sl j)
private def unitMatrix : V := !![1,0;0,0]
def beta (x z : V) : ZMod 2 := x 0 0 * z 1 1 + x 1 1 * z 0 0 +
  x 0 1 * z 1 0 + x 1 0 * z 0 1
theorem polar_eq_beta (x z : V) : (determinantForm (F := ZMod 2)).polarBilin x z = beta x z := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    determinantForm_apply, det_fin_two, Matrix.add_apply, beta]
  simp only [sub_eq_add_neg, CharTwo.neg_eq]
  ring_nf
  simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, zero_add, add_zero]
private theorem orbit_unit (a b c d : ZMod 2) (hx : (!![a,b;c,d] : V) ≠ 0) :
    (∃ i j : Fin 6, matrixAction (actor i j) !![a,b;c,d] = unitMatrix) ∨
    (∃ i j k l : Fin 6, matrixAction (actor i j) !![a,b;c,d] +
      matrixAction (actor k l) !![a,b;c,d] = unitMatrix) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · exact False.elim (hx (by decide))
  · exact Or.inl ⟨3, 3, by decide⟩
  · exact Or.inl ⟨3, 0, by decide⟩
  · exact Or.inl ⟨3, 1, by decide⟩
  · exact Or.inl ⟨0, 3, by decide⟩
  · exact Or.inl ⟨2, 3, by decide⟩
  · exact Or.inr ⟨0, 0, 0, 2, by decide⟩
  · exact Or.inr ⟨0, 1, 0, 5, by decide⟩
  · exact Or.inl ⟨0, 0, by decide⟩
  · exact Or.inr ⟨0, 3, 0, 4, by decide⟩
  · exact Or.inl ⟨2, 0, by decide⟩
  · exact Or.inr ⟨0, 1, 0, 5, by decide⟩
  · exact Or.inl ⟨0, 1, by decide⟩
  · exact Or.inr ⟨0, 3, 0, 4, by decide⟩
  · exact Or.inr ⟨0, 0, 0, 2, by decide⟩
  · exact Or.inl ⟨2, 1, by decide⟩
private theorem singular_orbit_unit (a b c d : ZMod 2)
    (hx : (!![a,b;c,d] : V) ≠ 0) (hd : (!![a,b;c,d] : V).det = 0) :
    ∃ i j : Fin 6, matrixAction (actor i j) !![a,b;c,d] = unitMatrix := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d
  · exact False.elim (hx (by decide))
  · exact ⟨3, 3, by decide⟩
  · exact ⟨3, 0, by decide⟩
  · exact ⟨3, 1, by decide⟩
  · exact ⟨0, 3, by decide⟩
  · exact ⟨2, 3, by decide⟩
  · revert hd; decide
  · revert hd; decide
  · exact ⟨0, 0, by decide⟩
  · revert hd; decide
  · exact ⟨2, 0, by decide⟩
  · revert hd; decide
  · exact ⟨0, 1, by decide⟩
  · revert hd; decide
  · revert hd; decide
  · exact ⟨2, 1, by decide⟩

theorem irreducible (S : Submodule (ZMod 2) V)
    (hinv : ∀ a : Actors, ∀ x ∈ S, matrixAction a x ∈ S) : S = ⊥ ∨ S = ⊤ := by
  by_cases hS : S = ⊥
  · exact Or.inl hS
  right
  obtain ⟨x, hxS, hx⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  have hunit : unitMatrix ∈ S := by
    have he := orbit_unit (x 0 0) (x 0 1) (x 1 0) (x 1 1)
    rw [← Matrix.eta_fin_two x] at he
    rcases he hx with ⟨i,j,h⟩ | ⟨i,j,k,l,h⟩
    · exact h ▸ hinv (actor i j) x hxS
    · exact h ▸ S.add_mem (hinv (actor i j) x hxS) (hinv (actor k l) x hxS)
  have hsingle (i j : Fin 2) : Matrix.single i j (1 : ZMod 2) ∈ S := by
    have he : matrixAction (actor (if i = 0 then 0 else 3) (if j = 0 then 0 else 3))
        unitMatrix = Matrix.single i j 1 := by
      fin_cases i <;> fin_cases j <;> decide
    exact he ▸ hinv _ _ hunit
  apply top_unique
  intro y _
  rw [Matrix.matrix_eq_sum_single y]
  apply S.sum_mem
  intro i _
  apply S.sum_mem
  intro j _
  have hh := S.smul_mem (y i j) (hsingle i j)
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using hh

abbrev pairing : V →ₗ[ZMod 2] V →ₗ[ZMod 2] ZMod 2 :=
  (determinantForm (F := ZMod 2)).polarBilin

theorem pairing_symm (x z : V) : pairing x z = pairing z x := by
  rw [polar_eq_beta, polar_eq_beta]
  unfold beta
  ring

theorem pairing_self (x : V) : pairing x x = 0 := by
  rw [polar_eq_beta]
  unfold beta
  rw [mul_comm (x 1 1), mul_comm (x 1 0)]
  simp only [CharTwo.add_self_eq_zero, zero_add]

theorem pairing_nondegenerate {z : V} (h : ∀ x, pairing z x = 0) : z = 0 := by
  have h00 := h !![0,0;0,1]
  have h01 := h !![0,0;1,0]
  have h10 := h !![0,1;0,0]
  have h11 := h !![1,0;0,0]
  simp only [polar_eq_beta, beta, of_apply, cons_val_zero, cons_val_one,
    mul_zero, mul_one, zero_add, add_zero] at h00 h01 h10 h11
  ext i j
  fin_cases i <;> fin_cases j
  · exact h00
  · exact h01
  · exact h10
  · exact h11

def perp (z : V) : Submodule (ZMod 2) V := (pairing z).ker

@[simp] theorem mem_perp (z x : V) : x ∈ perp z ↔ pairing z x = 0 := Iff.rfl

theorem finrank_V : Module.finrank (ZMod 2) V = 4 := by
  change Module.finrank (ZMod 2) (Fin 2 → Fin 2 → ZMod 2) = 4
  rw [Module.finrank_pi_fintype, Module.finrank_pi_fintype]
  simp [Module.finrank_self]

theorem finrank_perp {z : V} (hz : z ≠ 0) : Module.finrank (ZMod 2) (perp z) = 3 := by
  have hn : pairing z ≠ 0 := by
    intro h
    apply hz
    apply pairing_nondegenerate
    intro x
    exact LinearMap.congr_fun h x
  have hr := Module.Dual.range_eq_top_of_ne_zero hn
  have he := (pairing z).finrank_range_add_finrank_ker
  rw [hr, finrank_top, Module.finrank_self, finrank_V] at he
  change Module.finrank (ZMod 2) (pairing z).ker = 3
  omega

theorem card_perp {z : V} (hz : z ≠ 0) : Nat.card (perp z) = 8 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_perp hz, Nat.card_zmod]
  norm_num

theorem perp_sup_eq_top {z w : V} (hn : pairing z w ≠ 0) : perp z ⊔ perp w = ⊤ := by
  have hz : z ≠ 0 := by intro h; simp [h] at hn
  have hnle : ¬ perp w ≤ perp z := by
    intro h
    exact hn (h (show w ∈ perp w from pairing_self w))
  have hs : perp z < perp z ⊔ perp w := by
    apply lt_of_le_of_ne le_sup_left
    intro h
    exact hnle (h.symm ▸ le_sup_right)
  have ht := Submodule.finrank_lt_finrank_of_lt hs
  rw [finrank_perp hz] at ht
  apply Submodule.eq_top_of_finrank_eq
  have hl := Submodule.finrank_le (perp z ⊔ perp w)
  rw [finrank_V] at hl ⊢
  omega

theorem finrank_perp_inf {z w : V} (hn : pairing z w ≠ 0) :
    Module.finrank (ZMod 2) ↥(perp z ⊓ perp w) = 2 := by
  have hz : z ≠ 0 := by intro h; simp [h] at hn
  have hw : w ≠ 0 := by intro h; simp [h] at hn
  have he := Submodule.finrank_sup_add_finrank_inf_eq (perp z) (perp w)
  rw [perp_sup_eq_top hn, finrank_top, finrank_V,
    finrank_perp hz, finrank_perp hw] at he
  omega

noncomputable def perpInfEquiv {z w : V} (hn : pairing z w ≠ 0) :
    ↥(perp z ⊓ perp w) ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) :=
  LinearEquiv.ofFinrankEq _ _ (by rw [finrank_perp_inf hn, Module.finrank_pi]; simp)

theorem card_perp_inf {z w : V} (hn : pairing z w ≠ 0) :
    Nat.card ↥(perp z ⊓ perp w) = 4 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_perp_inf hn, Nat.card_zmod]
  norm_num


theorem action_mul (a b : Actors) (x : V) :
    matrixAction (a * b) x = matrixAction a (matrixAction b x) :=
  LinearEquiv.congr_fun (matrixHom.map_mul a b) x

@[simp] theorem action_inv_cancel (a : Actors) (x : V) :
    matrixAction a⁻¹ (matrixAction a x) = x := by
  rw [← action_mul, inv_mul_cancel]
  exact LinearEquiv.congr_fun matrixHom.map_one x

@[simp] theorem action_cancel_inv (a : Actors) (x : V) :
    matrixAction a (matrixAction a⁻¹ x) = x := by
  rw [← action_mul, mul_inv_cancel]
  exact LinearEquiv.congr_fun matrixHom.map_one x

theorem pairing_action (a : Actors) (x z : V) :
    pairing (matrixAction a x) (matrixAction a z) = pairing x z := by
  simp only [pairing, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    determinantForm_apply, ← map_add, matrixAction_det]

private theorem unit_perp_le (S : Submodule (ZMod 2) V)
    (h : ∀ a : Actors, matrixAction a unitMatrix = unitMatrix →
      ∀ x : V, matrixAction a x - x ∈ S) : perp unitMatrix ≤ S := by
  have h00 := h (actor 1 0) (by decide) !![0,0;1,0]
  have h01 := h (actor 1 0) (by decide) !![0,0;0,1]
  have h10 := h (actor 0 2) (by decide) !![0,0;0,1]
  have he00 : matrixAction (actor 1 0) !![0,0;1,0] - !![0,0;1,0] = unitMatrix := by decide
  have he01 : matrixAction (actor 1 0) !![0,0;0,1] - !![0,0;0,1] = !![0,1;0,0] := by decide
  have he10 : matrixAction (actor 0 2) !![0,0;0,1] - !![0,0;0,1] = !![0,0;1,0] := by decide
  rw [he00] at h00
  rw [he01] at h01
  rw [he10] at h10
  intro x hx
  have hx11 : x 1 1 = 0 := by
    change pairing unitMatrix x = 0 at hx
    rw [polar_eq_beta] at hx
    simpa [beta, unitMatrix] using hx
  have he : x = (x 0 0) • unitMatrix + (x 0 1) • !![0,1;0,0] +
      (x 1 0) • !![0,0;1,0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [unitMatrix, hx11]
  rw [he]
  exact S.add_mem (S.add_mem (S.smul_mem _ h00) (S.smul_mem _ h01)) (S.smul_mem _ h10)

/-- The stabilizer of a nonzero singular vector moves the whole perpendicular
hyperplane. This is a statement about its actual determinant action. -/
theorem perp_le_of_displacements {z : V} (hz : z ≠ 0) (hd : z.det = 0)
    (S : Submodule (ZMod 2) V)
    (h : ∀ a : Actors, matrixAction a z = z → ∀ x : V, matrixAction a x - x ∈ S) :
    perp z ≤ S := by
  have he := singular_orbit_unit (z 0 0) (z 0 1) (z 1 0) (z 1 1)
  rw [← Matrix.eta_fin_two z] at he
  obtain ⟨i,j,he⟩ := he hz hd
  let a := actor i j
  have haz : matrixAction a z = unitMatrix := he
  let R := S.comap (matrixAction a⁻¹).toLinearMap
  have hR : perp unitMatrix ≤ R := by
    apply unit_perp_le
    intro b hb x
    have hz' : matrixAction (a⁻¹ * b * a) z = z := by
      rw [action_mul, action_mul, haz, hb, ← haz, action_inv_cancel]
    have hm := h (a⁻¹ * b * a) hz' (matrixAction a⁻¹ x)
    change matrixAction a⁻¹ (matrixAction b x - x) ∈ S
    rw [map_sub]
    simpa only [action_mul, action_cancel_inv] using hm
  intro x hx
  have hm : matrixAction a x ∈ perp unitMatrix := by
    rw [mem_perp, ← haz, pairing_action]
    exact hx
  have hh := hR hm
  change matrixAction a⁻¹ (matrixAction a x) ∈ S at hh
  simpa only [action_inv_cancel] using hh

/-- Every displacement by the point stabilizer is perpendicular to that point. -/
theorem displacement_mem_perp {z : V} (a : Actors) (ha : matrixAction a z = z) (x : V) :
    matrixAction a x - x ∈ perp z := by
  rw [mem_perp, map_sub, ← ha, pairing_action]
  rw [ha, sub_self]

private theorem unit_second_center {x : V}
    (h : ∀ a : Actors, matrixAction a unitMatrix = unitMatrix →
      matrixAction a x - x ∈ Submodule.span (ZMod 2) {unitMatrix}) :
    x ∈ perp unitMatrix := by
  have hh := h (actor 1 0) (by decide)
  rw [Submodule.mem_span_singleton] at hh
  obtain ⟨c, hc⟩ := hh
  have he := congrArg (fun y : V => y 0 1) hc
  have hs : sl 0 = 1 := by decide
  have hcalc : (matrixAction (actor 1 0) x - x) 0 1 = x 1 1 := by
    change (((sl 1).val * x * (sl 0)⁻¹.val) 0 1 - x 0 1) = x 1 1
    rw [hs, inv_one, SpecialLinearGroup.coe_one, mul_one]
    simp [sl, rawSL, Matrix.mul_apply, Fin.sum_univ_two]
  have hzero : x 1 1 = 0 := by
    rw [hcalc] at he
    simpa [unitMatrix] using he.symm
  change pairing unitMatrix x = 0
  rw [polar_eq_beta]
  simpa [beta, unitMatrix] using hzero

/-- A vector whose stabilizer displacements lie in the marked line already
lies in its perpendicular hyperplane. -/
theorem mem_perp_of_displacements_in_line {z x : V} (hz : z ≠ 0) (hd : z.det = 0)
    (h : ∀ a : Actors, matrixAction a z = z →
      matrixAction a x - x ∈ Submodule.span (ZMod 2) {z}) : x ∈ perp z := by
  have he := singular_orbit_unit (z 0 0) (z 0 1) (z 1 0) (z 1 1)
  rw [← Matrix.eta_fin_two z] at he
  obtain ⟨i,j,he⟩ := he hz hd
  let a := actor i j
  have haz : matrixAction a z = unitMatrix := he
  have hm : matrixAction a x ∈ perp unitMatrix := by
    apply unit_second_center
    intro b hb
    have hz' : matrixAction (a⁻¹ * b * a) z = z := by
      rw [action_mul, action_mul, haz, hb, ← haz, action_inv_cancel]
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (h (a⁻¹ * b * a) hz')
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    have hh := congrArg (matrixAction a) hc
    simpa only [map_smul, map_sub, action_mul, action_cancel_inv, haz] using hh
  rw [mem_perp, ← haz, pairing_action] at hm
  exact hm

end ClassicalOrthogonal.FourPlusMatrix.PrimeFieldTwo.ModuleGeometry
