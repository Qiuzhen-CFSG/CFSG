module

public import Theory.SpecificGroups.Monster.Construction.NMonomial.EAction.Transport
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.SpinActions.Consequences

/-!
# The signed symmetric-pair model of the triality action

The carrier consists of three symmetric matrices on the marked coordinates,
with zero diagonal. Inverse pullback by the actual halfspace permutations,
multiplied by the product of the two natural coordinate signs, gives a genuine
representation of `N`. This is the source's `Bbar_E`; its comparison with the
literal Griess summands is separate.

Source: Aschbacher, *Sporadic Groups*, the construction before 29.10 and 29.10,
printed pp. 158–159. The matrix with entries one in positions `xy` and `yx`
is the unscaled symmetric tensor `x ⊗ y + y ⊗ x`.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace Sporadic.Monster.Construction.NMonomial.EAction
open TrialitySpin SignedModules.Natural Atlas.Codes Atlas.Fischer

/-- The real character of the Parker sign bit. -/
abbrev sign := SpinActions.realSign

@[simp] theorem sign_zero : sign 0 = 1 := rfl
@[simp] theorem sign_one : sign 1 = -1 := rfl

theorem sign_add (a b : ParkerBit) : sign (a+b) = sign a * sign b := by
  have hb : ∀ t : ParkerBit, t = 0 ∨ t = 1 := by decide
  rcases hb a with rfl | rfl
  · simp
  · rcases hb b with rfl | rfl
    · simp
    · rw [show (1 : ParkerBit) + 1 = 0 from rfl, sign_zero, sign_one]
      norm_num

@[simp] theorem sign_square (a : ParkerBit) : sign a * sign a = 1 := by
  rw [← sign_add]
  simp

/-- Three literal symmetric zero-diagonal matrices on the marked Golay coordinates. -/
def pairMatrices : Submodule ℝ (Axis → Omega → Omega → ℝ) where
  carrier := {f | (∀ i x y, f i x y = f i y x) ∧ (∀ i x, f i x x = 0)}
  zero_mem' := by constructor <;> intros <;> rfl
  add_mem' := by
    rintro f h ⟨hf,hf0⟩ ⟨hh,hh0⟩
    constructor
    · intro i x y; change f i x y + h i x y = f i y x + h i y x; rw [hf,hh]
    · intro i x; change f i x x + h i x x = 0; rw [hf0,hh0,add_zero]
  smul_mem' := by
    rintro c f ⟨hf,hf0⟩
    constructor
    · intro i x y; change c * f i x y = c * f i y x; rw [hf]
    · intro i x; change c * f i x x = 0; rw [hf0,mul_zero]

abbrev PairSpace := pairMatrices

/-- Coefficients of the actual symmetric tensor action; inverse pullback enforces
left composition, and its two signs are those of the natural factors. -/
def pairLinear (g : N) : PairSpace →ₗ[ℝ] PairSpace where
  toFun f := ⟨fun i x y =>
    sign (coordinateShift g⁻¹ i x + coordinateShift g⁻¹ i y) *
      f.val (axisPermutation g⁻¹ i) (coordinatePermutation g⁻¹ x) (coordinatePermutation g⁻¹ y), by
    constructor
    · intro i x y
      dsimp only
      rw [add_comm (coordinateShift g⁻¹ i x), f.prop.1]
    · intro i x
      dsimp only
      rw [f.prop.2, mul_zero]⟩
  map_add' f h := by
    apply Subtype.ext
    funext i x y
    exact mul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext i x y
    change _ * (c * _) = c * (_ * _)
    ring

/-- The source signed symmetric-pair representation, before the Griess comparison. -/
def pairRepresentation : Representation ℝ N PairSpace where
  toFun := pairLinear
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext i x y
    simp [pairLinear]
  map_mul' g h := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext i x y
    simp only [pairLinear, LinearMap.coe_mk, AddHom.coe_mk, Module.End.mul_apply,
      mul_inv_rev, coordinateShift_mul, map_mul, Equiv.Perm.coe_mul, Function.comp_apply]
    rw [show coordinateShift g⁻¹ i x +
        coordinateShift h⁻¹ (axisPermutation g⁻¹ i) (coordinatePermutation g⁻¹ x) +
        (coordinateShift g⁻¹ i y +
          coordinateShift h⁻¹ (axisPermutation g⁻¹ i) (coordinatePermutation g⁻¹ y)) =
        (coordinateShift g⁻¹ i x + coordinateShift g⁻¹ i y) +
          (coordinateShift h⁻¹ (axisPermutation g⁻¹ i) (coordinatePermutation g⁻¹ x) +
           coordinateShift h⁻¹ (axisPermutation g⁻¹ i) (coordinatePermutation g⁻¹ y)) by abel,
      sign_add, mul_assoc]

/-- The source pair generator, with entries one in the two symmetric positions. -/
def pairVector (i : Axis) (x y : Omega) (hxy : x ≠ y) : PairSpace :=
  ⟨fun j u v => if j = i ∧ ((u = x ∧ v = y) ∨ (u = y ∧ v = x)) then 1 else 0, by
    constructor
    · intro j u v
      change (if j = i ∧ ((u = x ∧ v = y) ∨ (u = y ∧ v = x)) then (1 : ℝ) else 0) =
        (if j = i ∧ ((v = x ∧ u = y) ∨ (v = y ∧ u = x)) then 1 else 0)
      simp only [and_comm, or_comm]
    · intro j u
      change (if j = i ∧ ((u = x ∧ u = y) ∨ (u = y ∧ u = x)) then (1 : ℝ) else 0) = 0
      apply if_neg
      rintro ⟨_, ⟨rfl,h⟩ | ⟨rfl,h⟩⟩
      · exact hxy h
      · exact hxy h.symm⟩

@[simp] theorem pairVector_swap (i : Axis) (x y : Omega) (hxy : x ≠ y) :
    pairVector i x y hxy = pairVector i y x hxy.symm := by
  apply Subtype.ext
  funext j u v
  simp [pairVector, or_comm]

/-- The sign of inverse transport at a forward image equals the original sign. -/
theorem coordinateShift_inverse_forward (g : N) (i : Axis) (x : Omega) :
    coordinateShift g⁻¹ (axisPermutation g i) (coordinatePermutation g x) =
      coordinateShift g i x := by
  have h := coordinateShift_mul g⁻¹ g i x
  rw [inv_mul_cancel, coordinateShift_one] at h
  have he := eq_neg_of_add_eq_zero_right h.symm
  simpa using he

/-- Forward evaluation is the tensor product of the two actual natural signs. -/
theorem pairRepresentation_apply_forward (g : N) (f : PairSpace)
    (i : Axis) (x y : Omega) :
    (pairRepresentation g f).val (axisPermutation g i)
      (coordinatePermutation g x) (coordinatePermutation g y) =
    sign (coordinateShift g i x + coordinateShift g i y) * f.val i x y := by
  change sign (coordinateShift g⁻¹ (axisPermutation g i) (coordinatePermutation g x) +
    coordinateShift g⁻¹ (axisPermutation g i) (coordinatePermutation g y)) *
    f.val (axisPermutation g⁻¹ (axisPermutation g i))
      (coordinatePermutation g⁻¹ (coordinatePermutation g x))
      (coordinatePermutation g⁻¹ (coordinatePermutation g y)) = _
  rw [coordinateShift_inverse_forward, coordinateShift_inverse_forward]
  simp

/-- Source 29.10 on pair generators, with coordinate transport explicit. -/
theorem pairRepresentation_pairVector (g : N) (i : Axis) (x y : Omega) (hxy : x ≠ y) :
    pairRepresentation g (pairVector i x y hxy) =
      sign (coordinateShift g i x + coordinateShift g i y) •
        pairVector (axisPermutation g i) (coordinatePermutation g x) (coordinatePermutation g y)
          (fun h => hxy ((coordinatePermutation g).injective h)) := by
  apply Subtype.ext
  funext j u v
  obtain ⟨j,rfl⟩ := (axisPermutation g).surjective j
  obtain ⟨u,rfl⟩ := (coordinatePermutation g).surjective u
  obtain ⟨v,rfl⟩ := (coordinatePermutation g).surjective v
  rw [pairRepresentation_apply_forward]
  change _ = sign (coordinateShift g i x + coordinateShift g i y) * _
  simp only [pairVector, Equiv.apply_eq_iff_eq]
  by_cases hj : j = i
  · subst j
    by_cases h : (u = x ∧ v = y) ∨ (u = y ∧ v = x)
    · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [add_comm]
    · simp [h]
  · simp [hj]

/-- The signed scalar used in the pair model is exactly the natural coordinate sign. -/
theorem naturalTransport_basis_sign (g : N) (i : Axis) (x : Omega) :
    naturalTransport g i (basis i x) =
      sign (coordinateShift g i x) • basis (axisPermutation g i) (coordinatePermutation g x) := by
  rw [basis_eq_L, naturalTransport_L]
  have hb : ∀ b : ParkerBit, b = 0 ∨ b = 1 := by decide
  rcases hb (coordinateShift g i x) with h | h
  · simp [h, basis_eq_L]
  · simp only [h, show (1 : ParkerBit) + 1 = 0 from rfl, L_zero, sign_one]
    exact (neg_one_smul ℝ _).symm

/-- All three loop families act by the source product of two coordinate signs. -/
theorem pairRepresentation_loop (a i : Axis) (d : ParkerLoop)
    (x y : Omega) (hxy : x ≠ y) :
    pairRepresentation (loopGenerator a d) (pairVector i x y hxy) =
      sign (if a = i then 0 else d.1.val x + d.1.val y) • pairVector i x y hxy := by
  rw [pairRepresentation_pairVector]
  simp only [coordinateShift_loop, axisPermutation_loop, coordinatePermutation_loop,
    Equiv.Perm.one_apply]
  by_cases h : a = i
  · simp only [if_pos h, add_zero]
  · simp only [if_neg h]

/-- A standard automorphism transports both coordinates and its actual target axis. -/
theorem pairRepresentation_standard (a i : Axis) (α : ParkerStandardGroup)
    (x y : Omega) (hxy : x ≠ y) :
    pairRepresentation (standardGenerator a α) (pairVector i x y hxy) =
      pairVector (autTarget a α.val i) ((parkerStandardProjection α).val x)
        ((parkerStandardProjection α).val y)
        (fun h => hxy ((parkerStandardProjection α).val.injective h)) := by
  simpa only [coordinateShift_standard, axisPermutation_standard,
    coordinatePermutation_standard, add_zero, sign_zero, one_smul, standardAxes,
    Equiv.coe_fn_mk] using
      pairRepresentation_pairVector (standardGenerator a α) i x y hxy

private theorem pairRepresentation_eq_one_of_uniform (g : N)
    (ha : axisPermutation g = 1) (hp : coordinatePermutation g = 1)
    (hc : ∀ i x y, coordinateShift g i x = coordinateShift g i y) :
    pairRepresentation g = 1 := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext i x y
  have h := pairRepresentation_apply_forward g f i x y
  simpa [ha,hp,hc i x y] using h

private theorem pairRepresentation_omega_product (a b : Axis) (s t : ParkerBit) :
    pairRepresentation (loopGenerator a (parkerSign s parkerOmega) *
      loopGenerator b (parkerSign t parkerOmega)) = 1 := by
  apply pairRepresentation_eq_one_of_uniform
  · simp
  · simp
  · intro i x y
    simp only [coordinateShift_mul, axisPermutation_loop, coordinatePermutation_loop,
      Equiv.Perm.one_apply, coordinateShift_loop]
    rfl

/-- The source kernel `K` acts trivially on symmetric pairs, although its natural
factors may both act as minus identity. -/
theorem pairRepresentation_of_mem_K {g : N} (hg : g ∈ TrialitySpin.K) :
    pairRepresentation g = 1 := by
  apply (show TrialitySpin.K ≤ pairRepresentation.ker from ?_) hg
  apply (Subgroup.closure_le _).2
  intro k hk
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hk
  rcases hk with rfl | rfl | rfl
  · exact pairRepresentation_omega_product 1 2 1 0
  · exact pairRepresentation_omega_product 2 0 1 0
  · exact pairRepresentation_omega_product 0 1 1 0

/-- The diagonal sum of the three trace forms, in the source normalization. -/
def pairGamma : LinearMap.BilinForm ℝ PairSpace :=
  { toFun := fun f =>
      { toFun := fun h => ∑ i, ∑ x, ∑ y, f.val i x y * h.val i x y
        map_add' := by intros; simp [mul_add, Finset.sum_add_distrib]
        map_smul' := by intros; simp [mul_left_comm, ← Finset.mul_sum] }
    map_add' := by intros; ext; simp [add_mul, Finset.sum_add_distrib]
    map_smul' := by intros; ext; simp [mul_assoc, ← Finset.mul_sum] }

/-- Orthogonality of the full signed pair action. -/
theorem pairGamma_invariant (g : N) (f h : PairSpace) :
    pairGamma (pairRepresentation g f) (pairRepresentation g h) = pairGamma f h := by
  change (∑ i, ∑ x, ∑ y, (pairRepresentation g f).val i x y *
    (pairRepresentation g h).val i x y) = ∑ i, ∑ x, ∑ y, f.val i x y * h.val i x y
  rw [← Equiv.sum_comp (axisPermutation g)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Equiv.sum_comp (coordinatePermutation g)]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Equiv.sum_comp (coordinatePermutation g)]
  apply Finset.sum_congr rfl
  intro y _
  rw [pairRepresentation_apply_forward, pairRepresentation_apply_forward]
  calc
    _ = (sign (coordinateShift g i x + coordinateShift g i y) *
      sign (coordinateShift g i x + coordinateShift g i y)) * (f.val i x y * h.val i x y) := by ring
    _ = _ := by rw [sign_square, one_mul]

end Sporadic.Monster.Construction.NMonomial.EAction
