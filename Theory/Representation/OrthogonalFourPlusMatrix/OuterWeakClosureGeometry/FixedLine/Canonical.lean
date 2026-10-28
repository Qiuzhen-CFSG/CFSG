module
public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The canonical outer fixed-line geometry in determinant space

A determinant isometry over F₄ fixing the identity and the upper nilpotent
matrix unit has one binary coefficient and one arbitrary field coefficient.
The matrix units and determinant polarization determine its full formula.
Thus a faithful actor of order at least eight realizes all eight formulas.

On the fixed hyperplane of the diagonal swap, only the field coefficient
acts. Its additive homomorphism gives pointwise-kernel index at most four.
Two explicit displacements show that the binary moved span contains the
identity and its sum with the nilpotent matrix unit, which are nonsingular
and lie on distinct field lines. The movement theorem also accepts an
arbitrary binary subspace containing those literal displacements, for
transport to the original commutator space.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Lemma 9.4.5, printed pp.736–737; the canonical
calculation for the outer involution's fixed hyperplane and its moved space.
-/

@[expose] public noncomputable section
open Matrix Module
namespace ClassicalOrthogonal.FourPlusMatrix.Binary.OuterWeakClosureGeometry.FixedLine.Canonical

/-- The literal matrix units. -/
def E (i j : Fin 2) : V := Matrix.single i j 1

@[simp] theorem E_apply (i j k l : Fin 2) :
    E i j k l = if i = k ∧ j = l then 1 else 0 := rfl

private def polar (M N : V) : F :=
  M 0 0 * N 1 1 + M 1 1 * N 0 0 - M 0 1 * N 1 0 - M 1 0 * N 0 1

private lemma polar_preserved (t : V ≃ₗ[F] V) (ht : ∀ M, (t M).det = M.det)
    (M N : V) : polar (t M) (t N) = polar M N := by
  have h := ht (M + N)
  have hM := ht M
  have hN := ht N
  simp only [map_add, det_fin_two, Matrix.add_apply] at h hM hN
  unfold polar
  linear_combination h - hM - hN

theorem map_matrix (t : V ≃ₗ[F] V) (M : V) :
    t M = M 0 0 • t (E 0 0) + M 0 1 • t (E 0 1) +
      M 1 0 • t (E 1 0) + M 1 1 • t (E 1 1) := by
  have hM : M = M 0 0 • E 0 0 + M 0 1 • E 0 1 +
      M 1 0 • E 1 0 + M 1 1 • E 1 1 := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp [E_apply]
  conv_lhs => rw [hM]
  simp only [map_add, map_smul]

theorem diagonal_shape (t : V ≃ₗ[F] V) (ht : ∀ M, (t M).det = M.det)
    (hI : t (1 : V) = 1) (hN : t (E 0 1) = E 0 1) :
    (t (E 1 1) 0 0 = 0 ∨ t (E 1 1) 0 0 = 1) ∧
      t (E 1 1) = !![t (E 1 1) 0 0, t (E 1 0) 0 0; 0, t (E 1 1) 0 0 + 1] ∧
      t (E 1 0) = !![t (E 1 0) 0 0, (t (E 1 0) 0 0) ^ 2; 1, t (E 1 0) 0 0] := by
  have hp := polar_preserved t ht
  have hD10 : t (E 1 1) 1 0 = 0 := by
    simpa [hN, polar] using hp (E 0 1) (E 1 1)
  have hD11 : t (E 1 1) 1 1 = t (E 1 1) 0 0 + 1 := by
    have h := hp 1 (E 1 1)
    simp only [hI, polar, Matrix.one_apply, E_apply] at h
    norm_num at h
    simpa only [sub_eq_add_neg, CharTwo.neg_eq, add_comm] using eq_sub_of_add_eq h
  have ha : t (E 1 1) 0 0 = 0 ∨ t (E 1 1) 0 0 = 1 := by
    have h := ht (E 1 1)
    simp [det_fin_two, hD10, hD11] at h
    rcases h with h | h
    · exact Or.inl h
    · right
      have := eq_neg_of_add_eq_zero_left h
      simpa only [CharTwo.neg_eq] using this
  have hC10 : t (E 1 0) 1 0 = 1 := by
    simpa [hN, polar] using hp (E 0 1) (E 1 0)
  have hC11 : t (E 1 0) 1 1 = t (E 1 0) 0 0 := by
    have h := hp 1 (E 1 0)
    simpa [hI, polar, CharTwo.add_eq_zero] using h
  have hC01 : t (E 1 0) 0 1 = t (E 1 0) 0 0 ^ 2 := by
    have h := ht (E 1 0)
    symm
    simpa [det_fin_two, hC10, hC11, ← pow_two, sub_eq_zero]
      using h
  have hD01 : t (E 1 1) 0 1 = t (E 1 0) 0 0 := by
    have h := hp (E 1 1) (E 1 0)
    simp only [polar, E_apply, hD10, hD11, hC10, hC11] at h
    norm_num at h
    rw [add_mul, one_mul, ← add_assoc, CharTwo.add_self_eq_zero, zero_add] at h
    exact (sub_eq_zero.mp h).symm
  refine ⟨ha, ?_, ?_⟩ <;>
    funext i j <;> fin_cases i <;> fin_cases j <;>
      simp [hD10, hD11, hD01, hC10, hC11, hC01]


private lemma diagonal_first_unit (t : V ≃ₗ[F] V) (hI : t (1 : V) = 1) :
    t (E 0 0) = 1 - t (E 1 1) := by
  have he : E 0 0 = (1 : V) - E 1 1 := by
    funext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [he, map_sub, hI]

/-- The nilpotent upper matrix unit. -/
abbrev N : V := E 0 1

@[simp] theorem N_determinant : N.det = 0 := by decide +kernel

theorem N_ne_zero : N ≠ 0 := by decide +kernel

/-- The two parameters give the literal operator on every matrix. -/
theorem matrix_formula_of_shape (t : V ≃ₗ[F] V) (a b : F)
    (hI : t (1 : V) = 1) (hN : t N = N)
    (hD : t (E 1 1) = !![a, b; 0, a + 1])
    (hC : t (E 1 0) = !![b, b ^ 2; 1, b]) (M : V) :
    t M = !![M 0 0 + a * (M 0 0 + M 1 1) + b * M 1 0,
      M 0 1 + b * (M 0 0 + M 1 1) + b ^ 2 * M 1 0;
      M 1 0, M 1 1 + a * (M 0 0 + M 1 1) + b * M 1 0] := by
  rw [map_matrix t M, diagonal_first_unit t hI, hN, hD, hC]
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [N, Matrix.add_apply, Matrix.smul_apply,
      smul_eq_mul, sub_eq_add_neg, CharTwo.neg_eq, CharTwo.add_self_eq_zero]
  all_goals ring_nf
  all_goals simp only [CharTwo.two_eq_zero, mul_zero, zero_add]

/-- The binary first coefficient and arbitrary field second coefficient. -/
abbrev Parameters := {a : F // a = 0 ∨ a = 1} × F

theorem card_parameters : Nat.card Parameters = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

variable {B : Type*} [Group B]

/-- Coordinates of a faithful actor fixing the canonical pair. -/
def parameters (f : B →* (V ≃ₗ[F] V))
    (hdet : ∀ x M, (f x M).det = M.det)
    (hI : ∀ x, f x (1 : V) = 1) (hN : ∀ x, f x N = N)
    (x : B) : Parameters :=
  (⟨f x (E 1 1) 0 0, (diagonal_shape (f x) (hdet x) (hI x) (hN x)).1⟩,
    f x (E 1 0) 0 0)

theorem parameters_injective (f : B →* (V ≃ₗ[F] V)) (hf : Function.Injective f)
    (hdet : ∀ x M, (f x M).det = M.det)
    (hI : ∀ x, f x (1 : V) = 1) (hN : ∀ x, f x N = N) :
    Function.Injective (parameters f hdet hI hN) := by
  intro x y hxy
  have ha := congrArg (fun p : Parameters => p.1.val) hxy
  have hb := congrArg (fun p : Parameters => p.2) hxy
  dsimp only [parameters] at ha hb
  apply hf
  apply LinearEquiv.ext
  intro M
  obtain ⟨_, hDx, hCx⟩ := diagonal_shape (f x) (hdet x) (hI x) (hN x)
  obtain ⟨_, hDy, hCy⟩ := diagonal_shape (f y) (hdet y) (hI y) (hN y)
  rw [matrix_formula_of_shape (f x) _ _ (hI x) (hN x) hDx hCx,
    matrix_formula_of_shape (f y) _ _ (hI y) (hN y) hDy hCy, ha, hb]

theorem parameters_surjective (f : B →* (V ≃ₗ[F] V)) (hf : Function.Injective f)
    (hdet : ∀ x M, (f x M).det = M.det)
    (hI : ∀ x, f x (1 : V) = 1) (hN : ∀ x, f x N = N)
    (hcard : 8 ≤ Nat.card B) : Function.Surjective (parameters f hdet hI hN) :=
  ((parameters_injective f hf hdet hI hN).bijective_of_nat_card_le
    (card_parameters ▸ hcard)).2

/-- Every one of the eight possible formulas occurs when the faithful actor
has at least eight elements. -/
theorem exists_operator (f : B →* (V ≃ₗ[F] V)) (hf : Function.Injective f)
    (hdet : ∀ x M, (f x M).det = M.det)
    (hI : ∀ x, f x (1 : V) = 1) (hN : ∀ x, f x N = N)
    (hcard : 8 ≤ Nat.card B) (a b : F) (ha : a = 0 ∨ a = 1) :
    ∃ x : B, ∀ M : V,
      f x M = !![M 0 0 + a * (M 0 0 + M 1 1) + b * M 1 0,
        M 0 1 + b * (M 0 0 + M 1 1) + b ^ 2 * M 1 0;
        M 1 0, M 1 1 + a * (M 0 0 + M 1 1) + b * M 1 0] := by
  obtain ⟨x, hx⟩ := parameters_surjective f hf hdet hI hN hcard (⟨a, ha⟩, b)
  have hxa := congrArg (fun p : Parameters => p.1.val) hx
  have hxb := congrArg (fun p : Parameters => p.2) hx
  dsimp only [parameters] at hxa hxb
  obtain ⟨_, hD, hC⟩ := diagonal_shape (f x) (hdet x) (hI x) (hN x)
  refine ⟨x, fun M => ?_⟩
  rw [matrix_formula_of_shape (f x) _ _ (hI x) (hN x) hD hC, hxa, hxb]

/-- The fixed hyperplane of the canonical diagonal swap. -/
def fixedHyperplane : Submodule F V where
  carrier := {M | M 0 0 = M 1 1}
  zero_mem' := rfl
  add_mem' := by intro M P hM hP; change M 0 0 + P 0 0 = M 1 1 + P 1 1; rw [hM, hP]
  smul_mem' := by intro c M hM; change c * M 0 0 = c * M 1 1; rw [hM]

@[simp] theorem mem_fixedHyperplane (M : V) :
    M ∈ fixedHyperplane ↔ M 0 0 = M 1 1 := Iff.rfl

/-- The canonical involution interchanges the diagonal entries. -/
def swap : V ≃ₗ[F] V where
  toFun M := !![M 1 1, M 0 1; M 1 0, M 0 0]
  invFun M := !![M 1 1, M 0 1; M 1 0, M 0 0]
  left_inv M := by funext i j; fin_cases i <;> fin_cases j <;> simp
  right_inv M := by funext i j; fin_cases i <;> fin_cases j <;> simp
  map_add' M P := by funext i j; fin_cases i <;> fin_cases j <;> simp
  map_smul' c M := by funext i j; fin_cases i <;> fin_cases j <;> simp

@[simp] theorem swap_apply (M : V) :
    swap M = !![M 1 1, M 0 1; M 1 0, M 0 0] := rfl

/-- The literal fixed space is the equal-diagonal hyperplane. -/
theorem swap_fixed_iff (M : V) : swap M = M ↔ M ∈ fixedHyperplane := by
  constructor
  · intro h
    exact (congrArg (fun P : V => P 0 0) h).symm
  · intro h
    have hh := (mem_fixedHyperplane M).mp h
    funext i j
    fin_cases i <;> fin_cases j <;> simp [hh]

/-- On the swap-fixed hyperplane the first parameter has no effect. -/
theorem hyperplane_formula (t : V ≃ₗ[F] V)
    (hdet : ∀ M, (t M).det = M.det) (hI : t (1 : V) = 1) (hN : t N = N)
    (M : V) (hM : M ∈ fixedHyperplane) :
    t M = !![M 0 0 + t (E 1 0) 0 0 * M 1 0,
      M 0 1 + (t (E 1 0) 0 0) ^ 2 * M 1 0;
      M 1 0, M 1 1 + t (E 1 0) 0 0 * M 1 0] := by
  obtain ⟨_, hD, hC⟩ := diagonal_shape t hdet hI hN
  rw [matrix_formula_of_shape t _ _ hI hN hD hC]
  have hh : M 0 0 + M 1 1 = 0 := by rw [(mem_fixedHyperplane M).mp hM]; exact CharTwo.add_self_eq_zero _
  simp only [hh, mul_zero, add_zero]

/-- The coefficient controlling the action on the fixed hyperplane is additive. -/
def coefficientHom (f : B →* (V ≃ₗ[F] V))
    (hdet : ∀ x M, (f x M).det = M.det)
    (hI : ∀ x, f x (1 : V) = 1) (hN : ∀ x, f x N = N) : B →* Multiplicative F where
  toFun x := Multiplicative.ofAdd (f x (E 1 0) 0 0)
  map_one' := by change f 1 (E 1 0) 0 0 = 0; simp
  map_mul' x y := by
    change f (x * y) (E 1 0) 0 0 = f x (E 1 0) 0 0 + f y (E 1 0) 0 0
    rw [map_mul, LinearEquiv.mul_apply]
    obtain ⟨_, hDy, hCy⟩ := diagonal_shape (f y) (hdet y) (hI y) (hN y)
    have hmem : f y (E 1 0) ∈ fixedHyperplane := by rw [hCy]; rfl
    rw [hyperplane_formula (f x) (hdet x) (hI x) (hN x) _ hmem, hCy]
    simp [add_comm]

/-- The actual pointwise kernel on the swap-fixed hyperplane. -/
def pointwiseKernel (f : B →* (V ≃ₗ[F] V)) : Subgroup B where
  carrier := {x | ∀ M ∈ fixedHyperplane, f x M = M}
  one_mem' := by intro M hM; simp
  mul_mem' := by
    intro x y hx hy M hM
    rw [map_mul, LinearEquiv.mul_apply, hy M hM, hx M hM]
  inv_mem' := by
    intro x hx M hM
    apply (f x).injective
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    exact (hx M hM).symm

@[simp] theorem mem_pointwiseKernel (f : B →* (V ≃ₗ[F] V)) (x : B) :
    x ∈ pointwiseKernel f ↔ ∀ M ∈ fixedHyperplane, f x M = M := Iff.rfl

/-- Vanishing of the second coefficient is exactly the pointwise-kernel condition. -/
theorem pointwiseKernel_eq_ker (f : B →* (V ≃ₗ[F] V))
    (hdet : ∀ x M, (f x M).det = M.det)
    (hI : ∀ x, f x (1 : V) = 1) (hN : ∀ x, f x N = N) :
    pointwiseKernel f = (coefficientHom f hdet hI hN).ker := by
  ext x
  change (∀ M ∈ fixedHyperplane, f x M = M) ↔ f x (E 1 0) 0 0 = 0
  constructor
  · intro hx
    have hh := congrArg (fun M : V => M 0 0) (hx (E 1 0) (by rfl))
    simpa using hh
  · intro hx M hM
    rw [hyperplane_formula (f x) (hdet x) (hI x) (hN x) M hM, hx]
    funext i j
    fin_cases i <;> fin_cases j <;> simp

/-- There are at most four restrictions to the fixed hyperplane. -/
theorem pointwiseKernel_index_le_four (f : B →* (V ≃ₗ[F] V))
    (hdet : ∀ x M, (f x M).det = M.det)
    (hI : ∀ x, f x (1 : V) = 1) (hN : ∀ x, f x N = N) :
    (pointwiseKernel f).index ≤ 4 := by
  rw [pointwiseKernel_eq_ker f hdet hI hN, Subgroup.index_ker]
  have hc := Nat.card_le_card_of_injective
    (fun x : (coefficientHom f hdet hI hN).range => x.val) Subtype.val_injective
  simpa only [Nat.card_eq_fintype_card, Fintype.card_multiplicative,
    Representation.SL2FourNatural.card_field] using hc

/-- Binary span of the actual displacements of the fixed hyperplane. -/
def movedSpan (f : B →* (V ≃ₗ[F] V)) : Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {v | ∃ x : B, ∃ M ∈ fixedHyperplane, f x M - M = v}

/-- Two nonsingular, noncollinear vectors occur in any subspace containing
all the actual displacements of the fixed hyperplane. -/
theorem movement_witnesses (f : B →* (V ≃ₗ[F] V)) (hf : Function.Injective f)
    (hdet : ∀ x M, (f x M).det = M.det)
    (hI : ∀ x, f x (1 : V) = 1) (hN : ∀ x, f x N = N)
    (hcard : 8 ≤ Nat.card B) (W : Submodule (ZMod 2) V)
    (hmove : ∀ x M, M ∈ fixedHyperplane → f x M - M ∈ W) :
    (1 : V) ∈ W ∧ (1 : V) + N ∈ W := by
  let w : F := QuadraticAlgebra.omega
  obtain ⟨x, hx⟩ := exists_operator f hf hdet hI hN hcard 0 1 (Or.inl rfl)
  obtain ⟨y, hy⟩ := exists_operator f hf hdet hI hN hcard 0 w (Or.inl rfl)
  have hC : E 1 0 ∈ fixedHyperplane := by rfl
  have hCw : w ^ 2 • E 1 0 ∈ fixedHyperplane := fixedHyperplane.smul_mem _ hC
  have hsum : (f x (w ^ 2 • E 1 0) - w ^ 2 • E 1 0) +
      (f y (E 1 0) - E 1 0) = (1 : V) := by
    rw [hx, hy]
    decide +kernel
  have hsingle : f x (E 1 0) - E 1 0 = (1 : V) + N := by
    rw [hx]
    decide +kernel
  exact ⟨hsum ▸ W.add_mem (hmove x _ hCw) (hmove y _ hC),
    hsingle ▸ hmove x _ hC⟩

/-- The actual binary moved span contains the two marked nonsingular vectors. -/
theorem mem_movedSpan (f : B →* (V ≃ₗ[F] V)) (hf : Function.Injective f)
    (hdet : ∀ x M, (f x M).det = M.det)
    (hI : ∀ x, f x (1 : V) = 1) (hN : ∀ x, f x N = N)
    (hcard : 8 ≤ Nat.card B) :
    (1 : V) ∈ movedSpan f ∧ (1 : V) + N ∈ movedSpan f :=
  movement_witnesses f hf hdet hI hN hcard (movedSpan f)
    (fun x M hM => Submodule.subset_span ⟨x, M, hM, rfl⟩)

theorem witness_determinants : (1 : V).det = 1 ∧ ((1 : V) + N).det = 1 := by
  decide +kernel

theorem witnesses_noncollinear : ¬ ∃ c : F, c • (1 : V) = (1 : V) + N := by
  rintro ⟨c, hc⟩
  have hh := congrArg (fun M : V => M 0 1) hc
  simp [N] at hh

/-- The canonical moved space meets two distinct nonsingular field lines. -/
theorem movedSpan_nonsingular_pair (f : B →* (V ≃ₗ[F] V)) (hf : Function.Injective f)
    (hdet : ∀ x M, (f x M).det = M.det)
    (hI : ∀ x, f x (1 : V) = 1) (hN : ∀ x, f x N = N)
    (hcard : 8 ≤ Nat.card B) :
    ∃ x ∈ movedSpan f, ∃ y ∈ movedSpan f,
      x.det ≠ 0 ∧ y.det ≠ 0 ∧ y ∉ Submodule.span F ({x} : Set V) := by
  obtain ⟨hI', hN'⟩ := mem_movedSpan f hf hdet hI hN hcard
  refine ⟨1, hI', 1 + N, hN', ?_, ?_, ?_⟩
  · rw [witness_determinants.1]; exact one_ne_zero
  · rw [witness_determinants.2]; exact one_ne_zero
  · intro h
    exact witnesses_noncollinear (Submodule.mem_span_singleton.mp h)

end ClassicalOrthogonal.FourPlusMatrix.Binary.OuterWeakClosureGeometry.FixedLine.Canonical
