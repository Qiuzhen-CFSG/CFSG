module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.Tactic.LinearCombination

/-!
# The point local subgroup in the four-dimensional unitary group

The local factor fixes the first isotropic vector. Its inclusion in the
point parabolic is normal because it is the kernel of the scalar action on
that line. The injective projective map transports this subgroup faithfully.
The action on the perpendicular quotient is the middle two-by-two block;
we parametrize its entire kernel by Hermitian Heisenberg coordinates. Writing
z = t + x σ(y) identifies those coordinates with F × F × F^σ and computes
the kernel's order.

This constructs the local factor and radical candidate for Aschbacher--Smith,
F.1.12(I)(6), printed pp. 263--264 of `refs/quasithin.pdf`. Identification of
this kernel with O₂, its special-group structure, the quotient isomorphism,
and the residual calculations require further theorems.
-/

open Matrix BenderSuzuki.MatrixGroups
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
open UnitaryFourFlag
variable (F : Type*) [Field F]
section Finite
variable [Finite F] (J : HermitianForm 4 F)

/-- The scalar by which a point-parabolic element acts on its invariant line. -/
def pointScalar : pointParabolicSU F J →* F where
  toFun a := a.val.val.val 0 0
  map_one' := by simp
  map_mul' a b := by
    obtain ⟨h1,h2,h3⟩ := (mem_pointParabolicSU F J b.val).mp b.property
    change (a.val.val.val * b.val.val.val) 0 0 = _
    simp [Matrix.mul_apply, Fin.sum_univ_succ, h1,h2,h3]

/-- The first local factor fixes the isotropic vector, not merely its line. -/
def localSU : Subgroup (SU F J) :=
  (MulAction.stabilizer (GL (Fin 4) F) (![1,0,0,0] : Fin 4 → F)).comap
    J.specialSubgroup.subtype

omit [Finite F] in
theorem mem_localSU (a : SU F J) : a ∈ localSU F J ↔
    a.val.val 0 0 = 1 ∧ a.val.val 1 0 = 0 ∧
      a.val.val 2 0 = 0 ∧ a.val.val 3 0 = 0 := by
  change a.val • (![1,0,0,0] : Fin 4 → F) = _ ↔ _
  change a.val.val.mulVec (![1,0,0,0]) = _ ↔ _
  simp [mulVec, dotProduct, Fin.sum_univ_succ, funext_iff, Fin.forall_fin_succ]

theorem localSU_le_pointParabolicSU : localSU F J ≤ pointParabolicSU F J := by
  intro a ha
  exact (mem_pointParabolicSU F J a).mpr ((mem_localSU F J a).mp ha).2

theorem localSU_subgroupOf_eq_ker :
    (localSU F J).subgroupOf (pointParabolicSU F J) = (pointScalar F J).ker := by
  ext a
  change a.val ∈ localSU F J ↔ pointScalar F J a = 1
  rw [mem_localSU]
  exact ⟨fun h => h.1, fun h => ⟨h, (mem_pointParabolicSU F J a.val).mp a.property⟩⟩

instance localSU_normal : ((localSU F J).subgroupOf (pointParabolicSU F J)).Normal := by
  rw [localSU_subgroupOf_eq_ker]
  infer_instance

/-- The local subgroup in the actual projective model. -/
def localPSU : Subgroup (PSU F J) := (localSU F J).map (project F J)

def pointParabolicPSU : Subgroup (PSU F J) := (pointParabolicSU F J).map (project F J)

theorem localPSU_le_pointParabolicPSU : localPSU F J ≤ pointParabolicPSU F J :=
  Subgroup.map_mono (localSU_le_pointParabolicSU F J)

instance localPSU_normal : ((localPSU F J).subgroupOf (pointParabolicPSU F J)).Normal := by
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (localPSU_le_pointParabolicPSU F J)).mpr
  exact (Subgroup.map_mono ((Subgroup.normal_subgroupOf_iff_le_normalizer
    (localSU_le_pointParabolicSU F J)).mp (localSU_normal F J))).trans
      (Subgroup.le_normalizer_map (project F J))

variable [CharP F 2]
def localProjectEquiv : localSU F J ≃* localPSU F J :=
  (localSU F J).equivMapOfInjective (project F J) (project_injective F J)

@[simp] theorem localProjectEquiv_apply (a : localSU F J) :
    (localProjectEquiv F J a).val = project F J a.val := rfl

end Finite

variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
/-- Fixing the first vector forces the opposite row by the unitary equation. -/
theorem last_row (a : SU F (form F σ hσ)) (ha : a ∈ localSU F (form F σ hσ)) :
    a.val.val 3 0 = 0 ∧ a.val.val 3 1 = 0 ∧ a.val.val 3 2 = 0 ∧
      a.val.val 3 3 = 1 := by
  obtain ⟨h0,h1,h2,h3⟩ := (mem_localSU F _ a).mp ha
  have hu := a.property.1
  change (form F σ hσ).conjTranspose a.val.val * gram F * a.val.val = gram F at hu
  have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 1) hu
  have h02 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 2) hu
  have h03 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 3) hu
  simp [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
    Fin.sum_univ_succ, h0,h1,h2,h3] at h01 h02 h03
  exact ⟨h3,h01,h02,h03⟩

/-- The action on the two middle coordinates of the perpendicular quotient. -/
def middleBlock : localSU F (form F σ hσ) →* Matrix (Fin 2) (Fin 2) F where
  toFun a := !![a.val.val.val 1 1, a.val.val.val 1 2;
    a.val.val.val 2 1, a.val.val.val 2 2]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    obtain ⟨_,a10,a20,_⟩ := (mem_localSU F _ a.val).mp a.property
    obtain ⟨_,b31,b32,_⟩ := last_row F σ hσ b.val b.property
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, a10,a20,b31,b32]

/-- The candidate unipotent radical, as a kernel in the actual local subgroup.
Its identification with the two-core is a separate structural theorem. -/
def radical : Subgroup (localSU F (form F σ hσ)) := (middleBlock F σ hσ).ker

instance radical_normal : (radical F σ hσ).Normal := inferInstanceAs
  (middleBlock F σ hσ).ker.Normal

theorem mem_radical (a : localSU F (form F σ hσ)) : a ∈ radical F σ hσ ↔
    a.val.val.val 1 1 = 1 ∧ a.val.val.val 1 2 = 0 ∧
    a.val.val.val 2 1 = 0 ∧ a.val.val.val 2 2 = 1 := by
  change middleBlock F σ hσ a = 1 ↔ _
  constructor
  · intro h
    exact ⟨congrArg (fun M => M 0 0) h, congrArg (fun M => M 0 1) h,
      congrArg (fun M => M 1 0) h, congrArg (fun M => M 1 1) h⟩
  · rintro ⟨h11,h12,h21,h22⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [middleBlock, h11,h12,h21,h22]


/-- Coordinates for the unipotent radical. The last equation is the remaining
unitary equation in the upper-right corner. -/
structure RadicalCoordinates where
  x : F
  y : F
  z : F
  trace_eq : z + σ z = σ x * y + σ y * x

def radicalMatrix (c : RadicalCoordinates F σ) : Matrix (Fin 4) (Fin 4) F :=
  !![1, σ c.y, σ c.x, c.z; 0, 1, 0, c.x; 0, 0, 1, c.y; 0, 0, 0, 1]

theorem radicalMatrix_det (c : RadicalCoordinates F σ) : (radicalMatrix F σ c).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular]
  · simp [radicalMatrix, Fin.prod_univ_succ]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [radicalMatrix]

variable [CharP F 2]

theorem radicalMatrix_unitary (c : RadicalCoordinates F σ) :
    (form F σ hσ).conjTranspose (radicalMatrix F σ c) * gram F *
      radicalMatrix F σ c = gram F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [form, gram, radicalMatrix, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_succ, hσ c.x, hσ c.y, CharTwo.add_self_eq_zero]
  have h := c.trace_eq
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h

/-- A coordinate triple gives an actual special unitary matrix. -/
def radicalElement (c : RadicalCoordinates F σ) : SU F (form F σ hσ) :=
  ⟨GeneralLinearGroup.mkOfDetNeZero (radicalMatrix F σ c)
    (by rw [radicalMatrix_det]; exact one_ne_zero),
   radicalMatrix_unitary F σ hσ c, Units.ext (radicalMatrix_det F σ c)⟩

theorem radicalElement_mem_local (c : RadicalCoordinates F σ) :
    radicalElement F σ hσ c ∈ localSU F (form F σ hσ) := by
  rw [mem_localSU]
  simp [radicalElement, radicalMatrix]

/-- The coordinate matrices lie in the kernel of the perpendicular-quotient action. -/
def radicalOfCoordinates (c : RadicalCoordinates F σ) : radical F σ hσ :=
  ⟨⟨radicalElement F σ hσ c, radicalElement_mem_local F σ hσ c⟩, by
    rw [mem_radical]
    simp [radicalElement, radicalMatrix]⟩



theorem radical_entries (a : radical F σ hσ) :
    a.val.val.val.val 0 1 = σ (a.val.val.val.val 2 3) ∧
    a.val.val.val.val 0 2 = σ (a.val.val.val.val 1 3) ∧
    a.val.val.val.val 0 3 + σ (a.val.val.val.val 0 3) =
      σ (a.val.val.val.val 1 3) * a.val.val.val.val 2 3 +
      σ (a.val.val.val.val 2 3) * a.val.val.val.val 1 3 := by
  obtain ⟨h00,h10,h20,h30⟩ := (mem_localSU F _ a.val.val).mp a.val.property
  obtain ⟨_,h31,h32,h33⟩ := last_row F σ hσ a.val.val a.val.property
  obtain ⟨h11,h12,h21,h22⟩ := (mem_radical F σ hσ a.val).mp a.property
  have hu := a.val.val.property.1
  change (form F σ hσ).conjTranspose a.val.val.val.val * gram F *
    a.val.val.val.val = gram F at hu
  have h13 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 1 3) hu
  have h23 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 2 3) hu
  have h03 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 3 3) hu
  simp [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
    Fin.sum_univ_succ, h31,h32,h33,h11,h12,h21,h22] at h13 h23 h03
  refine ⟨?_, ?_, ?_⟩
  · apply σ.injective
    rw [hσ]
    exact ((eq_neg_of_add_eq_zero_left h13).trans (CharTwo.neg_eq _)).symm
  · apply σ.injective
    rw [hσ]
    exact ((eq_neg_of_add_eq_zero_left h23).trans (CharTwo.neg_eq _)).symm
  · linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h03

def coordinatesOfRadical (a : radical F σ hσ) : RadicalCoordinates F σ where
  x := a.val.val.val.val 1 3
  y := a.val.val.val.val 2 3
  z := a.val.val.val.val 0 3
  trace_eq := (radical_entries F σ hσ a).2.2

/-- The coordinates parametrize the whole kernel, not just a subgroup of it. -/
def radicalCoordinatesEquiv : RadicalCoordinates F σ ≃ radical F σ hσ where
  toFun := radicalOfCoordinates F σ hσ
  invFun := coordinatesOfRadical F σ hσ
  left_inv c := by cases c; rfl
  right_inv a := by
    obtain ⟨h00,h10,h20,h30⟩ := (mem_localSU F _ a.val.val).mp a.val.property
    obtain ⟨_,h31,h32,h33⟩ := last_row F σ hσ a.val.val a.val.property
    obtain ⟨h11,h12,h21,h22⟩ := (mem_radical F σ hσ a.val).mp a.property
    obtain ⟨h01,h02,_⟩ := radical_entries F σ hσ a
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [radicalOfCoordinates, radicalElement, radicalMatrix, coordinatesOfRadical,
        h00,h10,h20,h30,h31,h32,h33,h11,h12,h21,h22,h01,h02]


/-- Writing `z = t + x * σ y` removes the trace constraint; `t` runs over the
actual fixed subfield of the stored involution. -/
def radicalParametersEquiv : RadicalCoordinates F σ ≃ F × F × FixedBy.subfield F σ where
  toFun c := (c.x, c.y, ⟨c.z + c.x * σ c.y, by
    change σ (c.z + c.x * σ c.y) = c.z + c.x * σ c.y
    rw [map_add, map_mul, hσ]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) -c.trace_eq⟩)
  invFun p := ⟨p.1, p.2.1, p.2.2.val + p.1 * σ p.2.1, by
    have ht : σ p.2.2.val = p.2.2.val := p.2.2.property
    rw [map_add, map_mul, hσ, ht]
    ring_nf
    simp [CharTwo.two_eq_zero]⟩
  left_inv c := by
    have hz : c.z + c.x * σ c.y + c.x * σ c.y = c.z := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    cases c
    simp_all
  right_inv p := by
    rcases p with ⟨x,y,t⟩
    have hz : t.val + x * σ y + x * σ y = t.val := by
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    simp only [hz]

/-- Cardinality of the entire kernel in terms of the matrix and fixed fields. -/
theorem radical_card : Nat.card (radical F σ hσ) =
    Nat.card F * Nat.card F * Nat.card (FixedBy.subfield F σ) := by
  rw [← Nat.card_congr (radicalCoordinatesEquiv F σ hσ),
    Nat.card_congr (radicalParametersEquiv F σ hσ), Nat.card_prod, Nat.card_prod,
    mul_assoc]

/-- The multiplication law in the radical is the Hermitian Heisenberg law. -/
theorem radical_mul_coordinates (c d : RadicalCoordinates F σ) :
    let e := coordinatesOfRadical F σ hσ
      (radicalOfCoordinates F σ hσ c * radicalOfCoordinates F σ hσ d)
    e.x = c.x + d.x ∧ e.y = c.y + d.y ∧
      e.z = c.z + d.z + σ c.y * d.x + σ c.x * d.y := by
  dsimp [coordinatesOfRadical, radicalOfCoordinates, radicalElement]
  simp [radicalMatrix, Matrix.mul_apply, Fin.sum_univ_succ,
    add_comm, add_left_comm, add_assoc]

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
