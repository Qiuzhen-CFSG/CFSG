module

public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.ModuleFactors.ChiefFactors
public import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The middle chief factor of the binary exterior parabolic

The six mixed wedge coordinates identify the literal quotient `V₇/V₁` with
`Matrix (Fin 2) (Fin 3) (ZMod 2)`. For every element of the actual two-space
parabolic, the exterior minor formula induces `X ↦ A * X * D.transpose`,
where `A` and `D` are its literal diagonal blocks. The coordinate matrix is
also explicitly identified with `F₂² ⊗ F₂³`, and the quotient equivalence
intertwines with the tensor product of the two natural block operators.

Irreducibility follows from actual block transvections in the parabolic.
Their differences from the identity give left and right multiplication by
off-diagonal matrix units; composing two such operators also gives diagonal
units. Any nonzero coefficient of an invariant subspace therefore supplies
all six matrix units. Transport through the checked representation equivalence
proves `middleChiefFactor_isIrreducible`, discharging the middle-factor premise
of `exteriorStabilizer_V₁_chief_chain_with_factors`.

Source: Aschbacher--Smith, Lemma 12.5.2(1), printed p.817/PDF p.834.
-/

@[expose] public section

open scoped BigOperators TensorProduct
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional
noncomputable section

/-- The two-by-three coefficient matrices for the tensor of the natural block modules. -/
abbrev MiddleTensor := Matrix (Fin 2) (Fin 3) (ZMod 2)

/-- The six mixed wedge coordinates of a vector in the actual invariant space V₇. -/
def middleCoordinates : seventhSubrepresentation.toSubmodule →ₗ[ZMod 2] MiddleTensor where
  toFun v := ![![coordinates v.val 1, coordinates v.val 2, coordinates v.val 3],
    ![coordinates v.val 4, coordinates v.val 5, coordinates v.val 6]]
  map_add' v w := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      change coordinates (v.val + w.val) _ = coordinates v.val _ + coordinates w.val _
    all_goals rw [map_add]; rfl
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      change coordinates (c • v.val) _ = c * coordinates v.val _
    all_goals rw [map_smul]; rfl

theorem middleCoordinates_apply (v : seventhSubrepresentation.toSubmodule) :
    middleCoordinates v = ![![coordinates v.val 1, coordinates v.val 2, coordinates v.val 3],
      ![coordinates v.val 4, coordinates v.val 5, coordinates v.val 6]] := rfl

/-- Lift a mixed coefficient matrix to V₇ with zero Λ²Γ₂ coordinate. -/
def middleSection (x : MiddleTensor) : seventhSubrepresentation.toSubmodule :=
  ⟨coordinates.symm ![0, x 0 0, x 0 1, x 0 2, x 1 0, x 1 1, x 1 2, 0, 0, 0], by
    apply (mem_coordinateSpan _ _).mpr
    intro i hi
    fin_cases i <;> simp_all [-coordinates_apply]⟩

theorem middleCoordinates_section (x : MiddleTensor) : middleCoordinates (middleSection x) = x := by
  rw [middleCoordinates_apply]
  change ![![coordinates (coordinates.symm _) 1, coordinates (coordinates.symm _) 2,
    coordinates (coordinates.symm _) 3], ![coordinates (coordinates.symm _) 4,
    coordinates (coordinates.symm _) 5, coordinates (coordinates.symm _) 6]] = x
  simp only [LinearEquiv.apply_symm_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The kernel is exactly the literal copy of V₁ inside V₇. -/
theorem middleCoordinates_ker : middleCoordinates.ker = firstInsideSeventh.toSubmodule := by
  ext v
  change middleCoordinates v = 0 ↔ v.val ∈ V₁
  rw [V₁, mem_coordinateSpan]
  have hv := (mem_coordinateSpan _ _).mp v.property
  have h7 := hv 7 (by decide)
  have h8 := hv 8 (by decide)
  have h9 := hv 9 (by decide)
  constructor
  · intro h i hi
    have hc (a : Fin 2) (b : Fin 3) := congrFun (congrFun h a) b
    fin_cases i
    · simp at hi
    · exact hc 0 0
    · exact hc 0 1
    · exact hc 0 2
    · exact hc 1 0
    · exact hc 1 1
    · exact hc 1 2
    · exact h7
    · exact h8
    · exact h9
  · intro h
    ext i j
    fin_cases i <;> fin_cases j <;> exact h _ (by decide)

/-- The quotient equivalence induced by the six mixed wedge coordinates. -/
def middleTensorEquiv :
    (seventhSubrepresentation.toSubmodule ⧸ firstInsideSeventh.toSubmodule) ≃ₗ[ZMod 2]
      MiddleTensor :=
  (Submodule.quotEquivOfEq _ _ middleCoordinates_ker.symm).trans
    (middleCoordinates.quotKerEquivOfSurjective
      (fun x => ⟨middleSection x, middleCoordinates_section x⟩))

@[simp] theorem middleTensorEquiv_mk (v : seventhSubrepresentation.toSubmodule) :
    middleTensorEquiv (firstInsideSeventh.toSubmodule.mkQ v) = middleCoordinates v := rfl

/-- Embed the two upper-block coordinates in the natural five-space. -/
def middleUpperIndex (i : Fin 2) : Fin 5 := i.castLE (by decide)
/-- Embed the three lower-block coordinates in the natural five-space. -/
def middleLowerIndex (j : Fin 3) : Fin 5 := ⟨j.val + 2, by omega⟩

/-- The explicit tensor operator of the two diagonal blocks of the actual matrix. -/
def middleTensorOperator (g : Group) : MiddleTensor →ₗ[ZMod 2] MiddleTensor where
  toFun x i j := ∑ a : Fin 2, ∑ b : Fin 3,
    g.val (middleUpperIndex i) (middleUpperIndex a) *
      g.val (middleLowerIndex j) (middleLowerIndex b) * x a b
  map_add' x y := by
    ext i j
    change (∑ a : Fin 2, ∑ b : Fin 3, _ * (x a b + y a b)) =
      (∑ a : Fin 2, ∑ b : Fin 3, _ * x a b) + (∑ a : Fin 2, ∑ b : Fin 3, _ * y a b)
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext i j
    change (∑ a : Fin 2, ∑ b : Fin 3, _ * (c * x a b)) =
      c * (∑ a : Fin 2, ∑ b : Fin 3, _ * x a b)
    simp only [Finset.mul_sum, mul_left_comm]

theorem middleTensorOperator_apply (g : Group) (x : MiddleTensor) (i : Fin 2) (j : Fin 3) :
    middleTensorOperator g x i j = ∑ a : Fin 2, ∑ b : Fin 3,
      g.val (middleUpperIndex i) (middleUpperIndex a) *
        g.val (middleLowerIndex j) (middleLowerIndex b) * x a b := rfl

/-- The exterior minor formula on V₇, with the V₁ coordinate discarded. -/
theorem middleCoordinates_action (g : parabolic 2) (v : seventhSubrepresentation.toSubmodule) :
    middleCoordinates (seventhSubrepresentation.toRepresentation g v) =
      middleTensorOperator g.val (middleCoordinates v) := by
  have hz := (mem_parabolic_iff_lowerLeft_zero 2 g.val).mp g.property
  have h20 := hz 2 0 (by decide) (by decide)
  have h21 := hz 2 1 (by decide) (by decide)
  have h30 := hz 3 0 (by decide) (by decide)
  have h31 := hz 3 1 (by decide) (by decide)
  have h40 := hz 4 0 (by decide) (by decide)
  have h41 := hz 4 1 (by decide) (by decide)
  have hv := (mem_coordinateSpan _ _).mp v.property
  have h7 := hv 7 (by decide)
  have h8 := hv 8 (by decide)
  have h9 := hv 9 (by decide)
  change ![![coordinates (exteriorAction 2 g.val v.val) 1,
    coordinates (exteriorAction 2 g.val v.val) 2, coordinates (exteriorAction 2 g.val v.val) 3],
    ![coordinates (exteriorAction 2 g.val v.val) 4,
    coordinates (exteriorAction 2 g.val v.val) 5, coordinates (exteriorAction 2 g.val v.val) 6]] = _
  rw [coordinates_action]
  ext i j
  rw [middleTensorOperator_apply, middleCoordinates_apply]
  fin_cases i <;> fin_cases j <;>
    simp [middleUpperIndex, middleLowerIndex,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ, actionMatrix, pair,
      h20, h21, h30, h31, h40, h41, h7, h8, h9,
      add_assoc, -coordinates_apply]

/-- Pointwise intertwining for the literal quotient representation V₇/V₁. -/
theorem middleTensorEquiv_action (g : parabolic 2)
    (v : seventhSubrepresentation.toSubmodule ⧸ firstInsideSeventh.toSubmodule) :
    middleTensorEquiv (middleChiefFactor g v) =
      middleTensorOperator g.val (middleTensorEquiv v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v => exact middleCoordinates_action g v

/-- The concrete tensor representation of the actual two-space parabolic. -/
def middleTensorRepresentation : Representation (ZMod 2) (parabolic 2) MiddleTensor where
  toFun g := middleTensorOperator g.val
  map_one' := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := middleTensorEquiv.surjective x
    rw [← middleTensorEquiv_action]
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := middleTensorEquiv.surjective x
    change middleTensorOperator (g * h).val (middleTensorEquiv v) =
      middleTensorOperator g.val (middleTensorOperator h.val (middleTensorEquiv v))
    calc
      _ = middleTensorEquiv (middleChiefFactor (g * h) v) :=
        (middleTensorEquiv_action (g * h) v).symm
      _ = middleTensorEquiv (middleChiefFactor g (middleChiefFactor h v)) :=
        congrArg middleTensorEquiv (congrArg (fun f => f v) (map_mul middleChiefFactor g h))
      _ = middleTensorOperator g.val (middleTensorEquiv (middleChiefFactor h v)) :=
        middleTensorEquiv_action g (middleChiefFactor h v)
      _ = _ := congrArg (middleTensorOperator g.val) (middleTensorEquiv_action h v)

/-- The checked representation equivalence from the literal chief factor to its matrix model. -/
def middleChiefFactorEquivTensor : middleChiefFactor.Equiv middleTensorRepresentation where
  toLinearEquiv := middleTensorEquiv
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    exact middleTensorEquiv_action g v

/-- The literal upper-left two-by-two block, in its original coordinate order. -/
def middleUpperBlock (g : Group) : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  fun i j => g.val (middleUpperIndex i) (middleUpperIndex j)

/-- The literal lower-right three-by-three block, in its original coordinate order. -/
def middleLowerBlock (g : Group) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  fun i j => g.val (middleLowerIndex i) (middleLowerIndex j)

/-- The coordinate tensor operator is exactly X ↦ A X Dᵀ. -/
theorem middleTensorOperator_eq_mul (g : Group) (x : MiddleTensor) :
    middleTensorOperator g x = middleUpperBlock g * x * (middleLowerBlock g).transpose := by
  ext i j
  rw [middleTensorOperator_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
    middleUpperBlock, middleLowerBlock]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- An actual parabolic element adding one upper-block row to another. -/
def middleRowTransvection (r s : Fin 2) (hrs : r ≠ s) : parabolic 2 :=
  ⟨Matrix.SpecialLinearGroup.transvection (show middleUpperIndex r ≠ middleUpperIndex s by
    simpa [middleUpperIndex] using hrs) 1, by
    apply (mem_parabolic_iff_lowerLeft_zero 2 _).mpr
    intro i j hi hj
    have hij : i ≠ j := by intro h; subst i; omega
    have hri : middleUpperIndex r ≠ i := by
      intro h
      have := congrArg Fin.val h
      dsimp [middleUpperIndex] at this
      omega
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single,
      hij, hri]⟩

/-- An actual parabolic element giving an elementary operation in the lower block. -/
def middleColumnTransvection (r s : Fin 3) (hrs : r ≠ s) : parabolic 2 :=
  ⟨Matrix.SpecialLinearGroup.transvection (show middleLowerIndex r ≠ middleLowerIndex s by
    simpa [middleLowerIndex, Fin.ext_iff] using hrs) 1, by
    apply (mem_parabolic_iff_lowerLeft_zero 2 _).mpr
    intro i j hi hj
    have hij : i ≠ j := by intro h; subst i; omega
    have hsj : middleLowerIndex s ≠ j := by
      intro h
      have := congrArg Fin.val h
      dsimp [middleLowerIndex] at this
      omega
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single,
      hij, hsj]⟩

private theorem middleRowTransvection_blocks (r s : Fin 2) (hrs : r ≠ s) :
    middleUpperBlock (middleRowTransvection r s hrs).val =
      1 + Matrix.single r s 1 ∧
    middleLowerBlock (middleRowTransvection r s hrs).val = 1 := by
  constructor
  · ext i j
    simp [middleUpperBlock, middleRowTransvection, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.one_apply, Matrix.single, middleUpperIndex]
  · ext i j
    change (1 + Matrix.single (middleUpperIndex r) (middleUpperIndex s) (1 : ZMod 2))
      (middleLowerIndex i) (middleLowerIndex j) = (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j
    simp [Matrix.one_apply, Matrix.single, middleUpperIndex, middleLowerIndex, Fin.ext_iff]
    omega

private theorem middleColumnTransvection_blocks (r s : Fin 3) (hrs : r ≠ s) :
    middleUpperBlock (middleColumnTransvection r s hrs).val = 1 ∧
    middleLowerBlock (middleColumnTransvection r s hrs).val =
      1 + Matrix.single r s 1 := by
  constructor
  · ext i j
    change (1 + Matrix.single (middleLowerIndex r) (middleLowerIndex s) (1 : ZMod 2))
      (middleUpperIndex i) (middleUpperIndex j) = (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)) i j
    simp [Matrix.one_apply, Matrix.single, middleUpperIndex, middleLowerIndex, Fin.ext_iff]
    omega
  · ext i j
    simp [middleLowerBlock, middleColumnTransvection, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.one_apply, Matrix.single, middleLowerIndex, Fin.ext_iff]

/-- The upper-block transvections act by elementary row operations on the tensor matrix. -/
theorem middleTensorRepresentation_rowTransvection (r s : Fin 2) (hrs : r ≠ s)
    (x : MiddleTensor) :
    middleTensorRepresentation (middleRowTransvection r s hrs) x =
      x + Matrix.single r s (1 : ZMod 2) * x := by
  change middleTensorOperator _ x = _
  rw [middleTensorOperator_eq_mul, (middleRowTransvection_blocks r s hrs).1,
    (middleRowTransvection_blocks r s hrs).2]
  simp [Matrix.add_mul]

/-- The lower-block transvections act by elementary column operations on the tensor matrix. -/
theorem middleTensorRepresentation_columnTransvection (r s : Fin 3) (hrs : r ≠ s)
    (x : MiddleTensor) :
    middleTensorRepresentation (middleColumnTransvection r s hrs) x =
      x + x * Matrix.single s r (1 : ZMod 2) := by
  change middleTensorOperator _ x = _
  rw [middleTensorOperator_eq_mul, (middleColumnTransvection_blocks r s hrs).1,
    (middleColumnTransvection_blocks r s hrs).2]
  simp [Matrix.mul_add]

private theorem middle_invariant_left_unit (W : Subrepresentation middleTensorRepresentation)
    (x : MiddleTensor) (hx : x ∈ W) (r s : Fin 2) :
    Matrix.single r s (1 : ZMod 2) * x ∈ W := by
  have hoff (a b : Fin 2) (hab : a ≠ b) (y : MiddleTensor) (hy : y ∈ W) :
      Matrix.single a b (1 : ZMod 2) * y ∈ W := by
    have h := W.toSubmodule.sub_mem (W.apply_mem_toSubmodule (middleRowTransvection a b hab) hy) hy
    change Matrix.single a b (1 : ZMod 2) * y ∈ W.toSubmodule
    simpa only [middleTensorRepresentation_rowTransvection, add_sub_cancel_left] using h
  by_cases hrs : r = s
  · subst s
    obtain ⟨t, ht⟩ := exists_ne r
    have h := hoff r t ht.symm _ (hoff t r ht x hx)
    simpa only [← Matrix.mul_assoc, Matrix.single_mul_single_same, one_mul] using h
  · exact hoff r s hrs x hx

private theorem middle_invariant_right_unit (W : Subrepresentation middleTensorRepresentation)
    (x : MiddleTensor) (hx : x ∈ W) (r s : Fin 3) :
    x * Matrix.single r s (1 : ZMod 2) ∈ W := by
  have hoff (a b : Fin 3) (hab : a ≠ b) (y : MiddleTensor) (hy : y ∈ W) :
      y * Matrix.single a b (1 : ZMod 2) ∈ W := by
    have h := W.toSubmodule.sub_mem (W.apply_mem_toSubmodule (middleColumnTransvection b a hab.symm) hy) hy
    change y * Matrix.single a b (1 : ZMod 2) ∈ W.toSubmodule
    simpa only [middleTensorRepresentation_columnTransvection, add_sub_cancel_left] using h
  by_cases hrs : r = s
  · subst s
    obtain ⟨t, ht⟩ := exists_ne r
    have h := hoff t r ht _ (hoff r t ht.symm x hx)
    simpa only [Matrix.mul_assoc, Matrix.single_mul_single_same, one_mul] using h
  · exact hoff r s hrs x hx

/-- Every nonzero invariant subspace contains all matrix units, hence the whole tensor module. -/
theorem middleTensorRepresentation_isIrreducible :
    Representation.IsIrreducible middleTensorRepresentation := by
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro W
  by_cases hW : W = ⊥
  · exact Or.inl hW
  right
  have hn : W.toSubmodule ≠ ⊥ := fun h => hW (Subrepresentation.toSubmodule_injective h)
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  obtain ⟨a, b, hab⟩ : ∃ a b, x a b ≠ 0 := by
    by_contra h
    push Not at h
    exact hx0 (funext fun a => funext (h a))
  have hab1 : x a b = 1 := (by decide : ∀ z : ZMod 2, z ≠ 0 → z = 1) _ hab
  have hunit (i : Fin 2) (j : Fin 3) : Matrix.single i j (1 : ZMod 2) ∈ W := by
    have h := middle_invariant_right_unit W _ (middle_invariant_left_unit W x hx i a) b j
    simpa only [Matrix.single_mul_mul_single, one_mul, mul_one, hab1] using h
  apply Subrepresentation.toSubmodule_injective
  apply top_unique
  intro y _
  rw [Matrix.matrix_eq_sum_single y]
  apply W.toSubmodule.sum_mem
  intro i _
  apply W.toSubmodule.sum_mem
  intro j _
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
    W.toSubmodule.smul_mem (y i j) (hunit i j)

/-- The actual middle factor in the source chief series is irreducible, with no additional premises. -/
theorem middleChiefFactor_isIrreducible : Representation.IsIrreducible middleChiefFactor :=
  middleChiefFactor_isIrreducible_of_equiv middleChiefFactorEquivTensor
    middleTensorRepresentation_isIrreducible

/-- The usual tensor product realized by its two-by-three coefficient matrix. -/
def middleTensorProductCoordinates :
    ((Fin 2 → ZMod 2) ⊗[ZMod 2] (Fin 3 → ZMod 2)) ≃ₗ[ZMod 2] MiddleTensor :=
  (_root_.TensorProduct.comm (ZMod 2) (Fin 2 → ZMod 2) (Fin 3 → ZMod 2)).trans
    ((_root_.TensorProduct.piScalarRight (ZMod 2) (ZMod 2) (Fin 3 → ZMod 2) (Fin 2)).trans
      (Matrix.ofLinearEquiv (ZMod 2)))

@[simp] theorem middleTensorProductCoordinates_tmul
    (u : Fin 2 → ZMod 2) (v : Fin 3 → ZMod 2) (i : Fin 2) (j : Fin 3) :
    middleTensorProductCoordinates (u ⊗ₜ[ZMod 2] v) i j = u i * v j := by
  simp [middleTensorProductCoordinates]

private theorem middleTensorOperator_pure (g : Group)
    (u : Fin 2 → ZMod 2) (v : Fin 3 → ZMod 2) :
    middleTensorOperator g (Matrix.of (fun i j => u i * v j)) =
      Matrix.of (fun i j => (middleUpperBlock g).mulVec u i * (middleLowerBlock g).mulVec v j) := by
  ext i j
  rw [middleTensorOperator_apply]
  simp only [Matrix.mulVec, dotProduct, middleUpperBlock, middleLowerBlock,
    Finset.sum_mul, Finset.mul_sum, Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The explicit block formula is the tensor of the two natural block actions. -/
theorem middleTensorProductCoordinates_action (g : Group)
    (t : (Fin 2 → ZMod 2) ⊗[ZMod 2] (Fin 3 → ZMod 2)) :
    middleTensorProductCoordinates
      (_root_.TensorProduct.map (middleUpperBlock g).mulVecLin (middleLowerBlock g).mulVecLin t) =
      middleTensorOperator g (middleTensorProductCoordinates t) := by
  induction t using _root_.TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul u v =>
    rw [_root_.TensorProduct.map_tmul]
    have h (a : Fin 2 → ZMod 2) (b : Fin 3 → ZMod 2) :
        middleTensorProductCoordinates (a ⊗ₜ[ZMod 2] b) = Matrix.of (fun i j => a i * b j) := by
      ext i j
      exact middleTensorProductCoordinates_tmul a b i j
    rw [h, h, middleTensorOperator_pure]
    rfl

/-- The literal middle quotient identified with F₂² ⊗ F₂³. -/
def middleChiefFactorTensorProductEquiv :
    (seventhSubrepresentation.toSubmodule ⧸ firstInsideSeventh.toSubmodule) ≃ₗ[ZMod 2]
      ((Fin 2 → ZMod 2) ⊗[ZMod 2] (Fin 3 → ZMod 2)) :=
  middleTensorEquiv.trans middleTensorProductCoordinates.symm

/-- Pointwise intertwining on the actual quotient with the actual diagonal blocks. -/
theorem middleChiefFactorTensorProductEquiv_action (g : parabolic 2)
    (v : seventhSubrepresentation.toSubmodule ⧸ firstInsideSeventh.toSubmodule) :
    middleChiefFactorTensorProductEquiv (middleChiefFactor g v) =
      _root_.TensorProduct.map (middleUpperBlock g.val).mulVecLin (middleLowerBlock g.val).mulVecLin
        (middleChiefFactorTensorProductEquiv v) := by
  apply middleTensorProductCoordinates.injective
  have h (q : seventhSubrepresentation.toSubmodule ⧸ firstInsideSeventh.toSubmodule) :
      middleTensorProductCoordinates (middleChiefFactorTensorProductEquiv q) = middleTensorEquiv q :=
    middleTensorProductCoordinates.apply_symm_apply _
  calc
    _ = middleTensorEquiv (middleChiefFactor g v) := h _
    _ = middleTensorOperator g.val (middleTensorEquiv v) := middleTensorEquiv_action g v
    _ = middleTensorOperator g.val
        (middleTensorProductCoordinates (middleChiefFactorTensorProductEquiv v)) :=
      congrArg (middleTensorOperator g.val) (h v).symm
    _ = _ := (middleTensorProductCoordinates_action g.val (middleChiefFactorTensorProductEquiv v)).symm

end
end Representation.SL5ExteriorSquare
