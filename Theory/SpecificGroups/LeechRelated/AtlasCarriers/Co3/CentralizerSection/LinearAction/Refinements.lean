module

public import Theory.SpecificGroups.SymplecticSix.Basic
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Co3.CentralizerSection.LinearData
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Even quadratic refinements of binary symplectic six-space

A refinement is determined by its values on the six hyperbolic basis vectors.
Translation identifies the zeros of Q_u(x) = q₀(x) + β(x,u) with the fiber of
q₀ at q₀(u); these fibers have sizes 36 and 28. Thus the 36 even refinements
are preserved by inverse substitution under every genuine symplectic matrix.
The base form and the six basis-parameter forms separate vectors, proving
faithfulness without any matrix-generation or group-order premise.

This supplies the geometry used to compare the Co₃ centralizer image with
Sp₆(2) (GLS3 Table 5.3j; Aschbacher--Smith A.2.19, printed pp.40–41).

Adapted from Gerald Höhn's ATLAS, `Symplectic/RefinementAction.lean`,
`BinaryRefinements.lean`, `BinaryOddRefinements.lean`, and `BinarySixAction.lean`,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917. Changes: dimension six,
even refinements, translation-based counting, explicit binary polar expression,
and faithfulness using the base form and six basis parameters. The adapted
material retains the ATLAS Research and Attribution License 1.0; see the
complete license and attribution in this directory's `source/`.
-/

@[expose] public section
open Theory.SpecificGroups.SymplecticSix
noncomputable section
namespace Sporadic.LeechRelated.Co3.CentralizerSection.LinearAction
open LinearData (K Index Sp)
abbrev V := Index → K

def beta (x y : V) : K :=
  x (.inl 0)*y (.inr 0)+x (.inl 1)*y (.inr 1)+x (.inl 2)*y (.inr 2)+
  x (.inr 0)*y (.inl 0)+x (.inr 1)*y (.inl 1)+x (.inr 2)*y (.inl 2)

theorem beta_eq_form (x y : V) : beta x y = form K x y := by
  simp [beta, form_apply, Fin.sum_univ_succ, CharTwo.sub_eq_add]
  ring

theorem beta_preserved (g : Sp) (x y : V) : beta (g • x) (g • y) = beta x y := by
  simp only [beta_eq_form, preserves_form]

def q₀ (x : V) : K :=
  x (.inl 0)*x (.inr 0)+x (.inl 1)*x (.inr 1)+x (.inl 2)*x (.inr 2)

abbrev Refinement := {Q : V → K // Q 0 = 0 ∧ ∀ x y, Q (x+y) = Q x+Q y+beta x y}

theorem q₀_polar (x y : V) : q₀ (x+y) = q₀ x + q₀ y + beta x y := by
  simp only [q₀, beta, Pi.add_apply]
  ring

def refinementOf (a : V) : Refinement :=
  ⟨fun x => q₀ x+beta x a, by simp [q₀, beta], by
    intro x y
    dsimp only
    rw [q₀_polar]
    simp only [beta, Pi.add_apply]
    ring⟩

def e (i : Fin 3) : V := Pi.single (.inl i) 1

def f (i : Fin 3) : V := Pi.single (.inr i) 1

def parameterOf (Q : Refinement) : V :=
  Sum.elim (fun i => Q.val (f i)) (fun i => Q.val (e i))

theorem refinement_smul (Q : Refinement) (c : K) (x : V) : Q.val (c • x) = c*Q.val x := by
  fin_cases c
  · change Q.val ((0 : K) • x) = (0 : K)*Q.val x
    rw [zero_smul, Q.prop.1, zero_mul]
  · change Q.val ((1 : K) • x) = (1 : K)*Q.val x
    rw [one_smul, one_mul]

theorem coordinates (x : V) :
    x = x (.inl 0) • e 0+x (.inl 1) • e 1+x (.inl 2) • e 2+
      x (.inr 0) • f 0+x (.inr 1) • f 1+x (.inr 2) • f 2 := by
  funext i
  rcases i with i|i <;> fin_cases i <;> simp [e, f]

theorem refinement_reconstruction (Q : Refinement) : refinementOf (parameterOf Q) = Q := by
  apply Subtype.ext
  funext x
  change q₀ x+beta x (parameterOf Q) = Q.val x
  conv_rhs => rw [coordinates x]
  simp only [Q.prop.2, refinement_smul]
  simp [q₀, parameterOf, beta, e, f]
  ring

theorem parameter_refinement (a : V) : parameterOf (refinementOf a) = a := by
  funext i
  rcases i with i|i <;> fin_cases i <;>
    simp [parameterOf, refinementOf, q₀, beta, e, f, Pi.single_apply]

def refinementEquiv : V ≃ Refinement where
  toFun := refinementOf
  invFun := parameterOf
  left_inv := parameter_refinement
  right_inv := refinement_reconstruction

instance refinementAction : MulAction Sp Refinement where
  smul g Q := ⟨fun x => Q.val (toLinear g⁻¹ x), by
    change Q.val (toLinear g⁻¹ 0) = 0
    rw [map_zero, Q.prop.1], by
    intro x y
    change Q.val (toLinear g⁻¹ (x+y)) = _
    rw [map_add, Q.prop.2]
    simp only [toLinear_apply, beta_preserved]⟩
  one_smul Q := by
    apply Subtype.ext
    funext x
    change Q.val ((1 : Sp)⁻¹ • x) = Q.val x
    simp
  mul_smul g h Q := by
    apply Subtype.ext
    funext x
    change Q.val ((g*h)⁻¹ • x) = Q.val (h⁻¹ • (g⁻¹ • x))
    rw [mul_inv_rev, mul_smul]

@[simp] theorem refinementAction_apply (g : Sp) (Q : Refinement) (x : V) :
    (g • Q).val x = Q.val (g⁻¹ • x) := rfl

def zeroCount (Q : Refinement) : ℕ := Nat.card {x : V // Q.val x = 0}

theorem zeroCount_invariant (g : Sp) (Q : Refinement) : zeroCount (g • Q) = zeroCount Q := by
  exact Nat.card_congr (Equiv.subtypeEquiv (toLinear g⁻¹).toEquiv (fun _ => Iff.rfl))

abbrev EvenRefinement := {Q : Refinement // zeroCount Q = 36}
abbrev EvenParameter := {a : V // q₀ a = 0}

theorem zeroCount_refinement (a : V) :
    zeroCount (refinementOf a) = Nat.card {x : V // q₀ x = q₀ a} := by
  apply Nat.card_congr
  apply Equiv.subtypeEquiv (Equiv.addRight a)
  intro x
  change q₀ x + beta x a = 0 ↔ q₀ (x+a) = q₀ a
  rw [q₀_polar]
  constructor
  · intro h
    calc
      q₀ x + q₀ a + beta x a = (q₀ x + beta x a) + q₀ a := by ring
      _ = q₀ a := by rw [h, zero_add]
  · intro h
    have : (q₀ x + beta x a) + q₀ a = 0 + q₀ a := by
      simpa only [zero_add, add_right_comm] using h
    exact add_right_cancel this

set_option maxRecDepth 10000 in
theorem card_base_zero : Fintype.card {x : V // q₀ x = 0} = 36 := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem card_base_one : Fintype.card {x : V // q₀ x = 1} = 28 := by
  decide +kernel

theorem zeroCount_refinement_iff (a : V) : zeroCount (refinementOf a) = 36 ↔ q₀ a = 0 := by
  rw [zeroCount_refinement, Nat.card_eq_fintype_card]
  generalize q₀ a = c
  fin_cases c
  · change Fintype.card {x : V // q₀ x = 0} = 36 ↔ (0 : K) = 0
    rw [card_base_zero]
    simp
  · change Fintype.card {x : V // q₀ x = 1} = 36 ↔ (1 : K) = 0
    rw [card_base_one]
    simp

def evenRefinementEquiv : EvenParameter ≃ EvenRefinement :=
  Equiv.subtypeEquiv refinementEquiv (fun a => (zeroCount_refinement_iff a).symm)

theorem card_evenRefinement : Nat.card EvenRefinement = 36 := by
  rw [← Nat.card_congr evenRefinementEquiv, Nat.card_eq_fintype_card]
  exact card_base_zero

instance evenRefinementAction : MulAction Sp EvenRefinement where
  smul g Q := ⟨g • Q.val, by rw [zeroCount_invariant, Q.prop]⟩
  one_smul Q := by apply Subtype.ext; exact one_smul _ _
  mul_smul g h Q := by apply Subtype.ext; exact mul_smul _ _ _

@[simp] theorem evenRefinementAction_apply (g : Sp) (Q : EvenRefinement) (x : V) :
    (g • Q).val.val x = Q.val.val (g⁻¹ • x) := rfl

def evenForm (a : V) (ha : q₀ a = 0) : EvenRefinement :=
  ⟨refinementOf a, (zeroCount_refinement_iff a).mpr ha⟩

theorem beta_e (x : V) (i : Fin 3) : beta x (e i) = x (.inr i) := by
  fin_cases i <;> simp [beta, e]

theorem beta_f (x : V) (i : Fin 3) : beta x (f i) = x (.inl i) := by
  fin_cases i <;> simp [beta, f]

theorem q₀_e (i : Fin 3) : q₀ (e i) = 0 := by
  fin_cases i <;> simp [q₀, e]

theorem q₀_f (i : Fin 3) : q₀ (f i) = 0 := by
  fin_cases i <;> simp [q₀, f]

instance evenRefinement_faithful : FaithfulSMul Sp EvenRefinement := by
  apply faithfulSMul_iff.mpr
  intro g hg
  have hginv : g⁻¹ = 1 := by
    have he (x : V) : g⁻¹ • x = x := by
      have H (a : V) (ha : q₀ a = 0) :=
        congrArg (fun Q : EvenRefinement => Q.val.val x) (hg (evenForm a ha))
      have hz := H 0 (by simp [q₀])
      simp only [evenRefinementAction_apply, evenForm, refinementOf] at hz
      simp only [beta, Pi.zero_apply, mul_zero, add_zero] at hz
      funext s
      rcases s with i | i
      · have h := H (f i) (q₀_f i)
        change q₀ (g⁻¹ • x) + beta (g⁻¹ • x) (f i) = q₀ x + beta x (f i) at h
        rw [hz, beta_f, beta_f] at h
        exact add_left_cancel h
      · have h := H (e i) (q₀_e i)
        change q₀ (g⁻¹ • x) + beta (g⁻¹ • x) (e i) = q₀ x + beta x (e i) at h
        rw [hz, beta_e, beta_e] at h
        exact add_left_cancel h
    apply Subtype.ext
    apply Matrix.ext
    intro i j
    have h := congrFun (he (Pi.single j 1)) i
    simpa [smul_eq_mulVec, Matrix.mulVec_single, Pi.single_apply, Matrix.one_apply] using h
  exact inv_eq_one.mp hginv

end Sporadic.LeechRelated.Co3.CentralizerSection.LinearAction
