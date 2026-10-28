module

public import Theory.AtlasPort.OtherSporadic.Lattices.LeechClassTypes
public import Theory.SpecificGroups.Monster.Construction.Symmetric
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Short Leech classes and their symmetric tensors

The minimal vectors of the actual ATLAS Leech lattice reduce two-to-one
onto 98,280 binary classes. A class therefore determines a rank-one symmetric
tensor and the vector expression in (28.6), independently of an antipodal
choice. Coordinates are divided by `sqrt 8`, so the inner product agrees
with the integral lattice pairing divided by eight. Tensor covariance uses
the existing symmetric-conjugation convention.

Source: Aschbacher, *Sporadic Groups*, Sections 22–23, the remark before
Lemma 27.8, and equations (28.2), (28.6), printed pp. 150–152. Lattice
facts are reused from the attributed ATLAS ports by Gerald Höhn; no new
lattice model is substituted. The equivariant extraspecial comparison is
not asserted here.
-/

@[expose] public section
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators Matrix
open Atlas.Codes Atlas.Lattices
namespace Sporadic.Monster.Construction.LocalC

abbrev ShortClass := ↥(shellClasses 4)

theorem shortClass_card : Nat.card ShortClass = 98280 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe, shellClasses_counts.1]

def shortReduction (x : LeechShell 4) : ShortClass :=
  ⟨leechReduction x.val, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩⟩

theorem shortReduction_surjective : Function.Surjective shortReduction := by
  intro a
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp a.prop
  exact ⟨x, Subtype.ext hx⟩

theorem shortReduction_eq_iff (x y : LeechShell 4) :
    shortReduction x = shortReduction y ↔ x.val = y.val ∨ x.val = -y.val := by
  constructor
  · intro h
    have hx := leech_shell_halfNorm 4 x
    have hy := leech_shell_halfNorm 4 y
    exact leech_congruent_short_unique _ _ (congrArg Subtype.val h) (by omega)
  · intro h
    apply Subtype.ext
    rcases h with h | h
    · exact congrArg leechReduction h
    · change leechReduction x.val = leechReduction y.val
      rw [h, leechReduction_neg]

def shortRepresentative (a : ShortClass) : LeechShell 4 :=
  Classical.choose (shortReduction_surjective a)

@[simp] theorem shortRepresentative_reduce (a : ShortClass) :
    shortReduction (shortRepresentative a) = a :=
  Classical.choose_spec (shortReduction_surjective a)

theorem shortRepresentative_unique (a : ShortClass) (x : LeechShell 4)
    (hx : shortReduction x = a) :
    x.val = (shortRepresentative a).val ∨ x.val = -(shortRepresentative a).val :=
  (shortReduction_eq_iff _ _).mp (hx.trans (shortRepresentative_reduce a).symm)

def shortClassPermutation (g : LeechIsometryGroup) : Equiv.Perm ShortClass where
  toFun a := ⟨leechModTwoRepresentation g a.val, shellClasses_transport g 4 a.val a.prop⟩
  invFun a := ⟨leechModTwoRepresentation g⁻¹ a.val,
    shellClasses_transport g⁻¹ 4 a.val a.prop⟩
  left_inv a := by
    apply Subtype.ext
    change leechModTwoMap g⁻¹ (leechModTwoMap g a.val) = a.val
    rw [← leechModTwoMap_mul, inv_mul_cancel, leechModTwoMap_one]
  right_inv a := by
    apply Subtype.ext
    change leechModTwoMap g (leechModTwoMap g⁻¹ a.val) = a.val
    rw [← leechModTwoMap_mul, mul_inv_cancel, leechModTwoMap_one]

def shortClassRepresentation : LeechIsometryGroup →* Equiv.Perm ShortClass where
  toFun := shortClassPermutation
  map_one' := by ext a; exact leechModTwoMap_one a.val
  map_mul' g h := by ext a; exact leechModTwoMap_mul g h a.val

@[simp] theorem shortReduction_transport (g : LeechIsometryGroup) (x : LeechShell 4) :
    shortReduction (shellPermutation g 4 x) = shortClassRepresentation g (shortReduction x) := rfl

/-- The fixed coordinate marking used to compare the ATLAS lattice with the
24-by-24 symmetric matrices. -/
def coordinateMarking : Fin 24 ≃ Omega :=
  (Fintype.equivOfCardEq (show Fintype.card Omega = Fintype.card (Fin 24) by
    simp [Omega, HexIndex])).symm

abbrev NaturalSpace := Fin 24 → ℝ

/-- Coordinates relative to an orthonormal basis, hence the factor `sqrt 8`. -/
def leechVector (x : leech) : NaturalSpace :=
  fun i => (x.val (coordinateMarking i) : ℝ) / Real.sqrt 8

@[simp] theorem leechVector_neg (x : leech) : leechVector (-x) = -leechVector x := by
  ext i
  simp [leechVector, neg_div]

/-- The symmetric tensor `v ⊗ v`. -/
def rankOne (v : NaturalSpace) : SymmetricPart :=
  ⟨Matrix.of (fun i j => v i * v j), by
    apply Matrix.IsSymm.ext
    intro i j
    exact mul_comm _ _⟩

@[simp] theorem rankOne_neg (v : NaturalSpace) : rankOne (-v) = rankOne v := by
  apply Subtype.ext
  ext i j
  simp [rankOne]

def shortTensor (a : ShortClass) : SymmetricPart :=
  rankOne (leechVector (shortRepresentative a).val)

theorem shortTensor_eq (x : LeechShell 4) :
    shortTensor (shortReduction x) = rankOne (leechVector x.val) := by
  rcases shortRepresentative_unique (shortReduction x) x rfl with h | h
  · rw [h]; rfl
  · rw [h, leechVector_neg, rankOne_neg]; rfl

/-- Matrix formula in the source's integral Leech coordinates. -/
theorem rankOne_leechVector (x : leech) (i j : Fin 24) :
    (rankOne (leechVector x)).val i j =
      (x.val (coordinateMarking i) : ℝ) * (x.val (coordinateMarking j) : ℝ) / 8 := by
  change (_ / Real.sqrt 8) * (_ / Real.sqrt 8) = _
  rw [div_mul_div_comm, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 8)]

/-- The vector-dependent expression in (28.6) has no sign choice. -/
def vectorCorrection (v a : NaturalSpace) : NaturalSpace :=
  a - (2 * ∑ i, a i * v i) • v

@[simp] theorem vectorCorrection_neg (v a : NaturalSpace) :
    vectorCorrection (-v) a = vectorCorrection v a := by
  ext i
  simp [vectorCorrection, Finset.sum_neg_distrib]

def shortCorrection (r : ShortClass) (a : NaturalSpace) : NaturalSpace :=
  vectorCorrection (leechVector (shortRepresentative r).val) a

theorem shortCorrection_eq (x : LeechShell 4) (a : NaturalSpace) :
    shortCorrection (shortReduction x) a = vectorCorrection (leechVector x.val) a := by
  rcases shortRepresentative_unique (shortReduction x) x rfl with h | h
  · rw [h]; rfl
  · rw [h, leechVector_neg, vectorCorrection_neg]; rfl

/-- The ambient form is the standard Leech form, with its normalization. -/
theorem leechVector_dot (x y : leech) :
    (∑ i, leechVector x i * leechVector y i) = (integerDot x.val y.val : ℝ) / 8 := by
  have hs : (∑ i : Fin 24, (x.val (coordinateMarking i) : ℝ) *
      (y.val (coordinateMarking i) : ℝ)) = (integerDot x.val y.val : ℝ) := by
    rw [coordinateMarking.sum_comp (fun j => (x.val j : ℝ) * (y.val j : ℝ))]
    simp [integerDot]
  calc
    _ = ∑ i : Fin 24, (x.val (coordinateMarking i) : ℝ) *
        (y.val (coordinateMarking i) : ℝ) / 8 := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [leechVector, div_mul_div_comm,
        Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 8)]
    _ = _ := by rw [← Finset.sum_div, hs]

theorem shortVector_norm (x : LeechShell 4) :
    (∑ i, leechVector x.val i * leechVector x.val i) = 4 := by
  rw [leechVector_dot, x.prop]
  norm_num

/-- The coefficient of `y(r)` in (28.2). -/
theorem symmetricGamma_rankOne (A : SymmetricPart) (v : NaturalSpace) :
    symmetricGamma A (rankOne v) = ∑ i, ∑ j, A.val i j * v i * v j := by
  unfold symmetricGamma Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag_apply, Matrix.mul_apply, rankOne, Matrix.of_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Rank-one tensors transform under the same orthogonal conjugation used
by the existing symmetric-summand API. This identity holds for every matrix. -/
theorem rankOne_conjugate (P : Matrix (Fin 24) (Fin 24) ℝ) (v : NaturalSpace) :
    symmetricConjugate P (rankOne v) = rankOne (Pᵀ *ᵥ v) := by
  apply Subtype.ext
  ext i j
  simp only [symmetricConjugate, rankOne, Matrix.mul_apply, Matrix.of_apply,
    Matrix.transpose_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Covariance, with the exact coordinate action premise separated from the
choice of short representative. The local-group assembly supplies this premise. -/
theorem shortTensor_covariant (g : LeechIsometryGroup)
    (P : Matrix (Fin 24) (Fin 24) ℝ)
    (hP : ∀ x : leech, leechVector (g.val x) = Pᵀ *ᵥ leechVector x)
    (a : ShortClass) :
    shortTensor (shortClassRepresentation g a) = symmetricConjugate P (shortTensor a) := by
  have h := shortTensor_eq (shellPermutation g 4 (shortRepresentative a))
  rw [shortReduction_transport, shortRepresentative_reduce] at h
  rw [h, shortTensor, rankOne_conjugate]
  exact congrArg rankOne (hP (shortRepresentative a).val)

end Sporadic.Monster.Construction.LocalC
