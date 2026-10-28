module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.Blocks.Torus
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The radical, SU₃, and cubic torus as one concrete subgroup

The middle SU₃ and cubic torus commute. Their product acts on the unipotent
coordinates, giving a homomorphism from `Coord ⋊ (SU₃ × C₃)` to the actual
projective line parabolic. It is faithful: in the Witt basis a scalar image
would have equal first and last entries, forcing the cubic parameter to be one.
Exhaustion of the full stabilizer is a separate matrix calculation.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.11--12(7), printed pp.262--264.
-/

@[expose] public section
open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic.Blocks
variable {F : Type*} [Field F] [CharP F 2]
  (J : HermitianForm 5 F) (hconj : ∀ x, J.conj x = x ^ 4)

omit [CharP F 2] in
/-- Scalar multiplication on the middle space commutes with its SU₃ action. -/
theorem leviAction_commute_cubic (A : (middleForm J).specialSubgroup) (b : Cubic (F := F)) :
    Commute (leviAction J A) (cubicAction J hconj b) := by
  apply MulEquiv.ext
  intro u
  apply Coord.ext
  · change A.val.val *ᵥ ((b.val : F) ^ 2 • u.vector) =
      (b.val : F) ^ 2 • (A.val.val *ᵥ u.vector)
    exact mulVec_smul _ _ _
  · rfl

abbrev FullLevi := (middleForm J).specialSubgroup × Cubic (F := F)

def fullLeviAction : FullLevi J →* MulAut (Coord J) :=
  (leviAction J).noncommCoprod (cubicAction J hconj) (leviAction_commute_cubic J hconj)

/-- The proposed full block coordinates, with the verified conjugation action. -/
abbrev FullProduct := Coord J ⋊[fullLeviAction J hconj] FullLevi J

def fullLeviMap (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    FullLevi J →* lineParabolic J :=
  (leviParabolic J hJ).noncommCoprod (cubicParabolic J hconj c hc hJ)
    (fun A b => (cubicParabolic_commute_levi J hconj c hc hJ b A).symm)

/-- Multiplication of the actual three matrix factors. -/
def fullMap (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    FullProduct J hconj →* lineParabolic J :=
  SemidirectProduct.lift (toParabolic J hJ) (fullLeviMap J hconj c hc hJ) (by
    intro p
    apply MonoidHom.ext
    intro u
    change toParabolic J hJ (leviAction J p.1 (cubicAction J hconj p.2 u)) = _
    rw [toParabolic_leviAction, toParabolic_cubicAction J hconj c hc hJ]
    change _ = (leviParabolic J hJ p.1 * cubicParabolic J hconj c hc hJ p.2) *
      toParabolic J hJ u * (leviParabolic J hJ p.1 * cubicParabolic J hconj c hc hJ p.2)⁻¹
    group)

@[simp] theorem fullMap_apply (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1)
    (x : FullProduct J hconj) :
    fullMap J hconj c hc hJ x = toParabolic J hJ x.left *
      (leviParabolic J hJ x.right.1 * cubicParabolic J hconj c hc hJ x.right.2) := rfl

/-- The established radical--SU₃ coordinates embed by setting the cubic parameter to one. -/
def radicalLeviInclusion : RadicalLevi J →* FullProduct J hconj :=
  SemidirectProduct.map (MonoidHom.id _) (MonoidHom.inl _ _) (by
    intro A
    apply MonoidHom.ext
    intro u
    change leviAction J A u = (leviAction J A * cubicAction J hconj 1) u
    rw [map_one, mul_one])

@[simp] theorem radicalLeviInclusion_left (x : RadicalLevi J) :
    (radicalLeviInclusion J hconj x).left = x.left := rfl
@[simp] theorem radicalLeviInclusion_right (x : RadicalLevi J) :
    (radicalLeviInclusion J hconj x).right = (x.right, 1) := rfl

theorem fullMap_comp_radicalLeviInclusion (c : F) (hc : c + J.conj c = 1)
    (hJ : J.form = 1) :
    (fullMap J hconj c hc hJ).comp (radicalLeviInclusion J hconj) = radicalLeviMap J hJ := by
  apply MonoidHom.ext
  intro x
  simp

/-- The middle special-unitary block of the concrete product. -/
def productProjection : FullProduct J hconj →* (middleForm J).specialSubgroup :=
  (MonoidHom.fst _ _).comp SemidirectProduct.rightHom

/-- The cubic parameter of the concrete product. -/
def productCharacter : FullProduct J hconj →* Cubic (F := F) :=
  (MonoidHom.snd _ _).comp SemidirectProduct.rightHom

@[simp] theorem productProjection_apply (x : FullProduct J hconj) :
    productProjection J hconj x = x.right.1 := rfl
@[simp] theorem productCharacter_apply (x : FullProduct J hconj) :
    productCharacter J hconj x = x.right.2 := rfl

theorem productCharacter_ker :
    (productCharacter J hconj).ker = (radicalLeviInclusion J hconj).range := by
  ext x
  constructor
  · intro hx
    have hb : x.right.2 = 1 := hx
    refine ⟨⟨x.left, x.right.1⟩, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact Prod.ext rfl hb.symm
  · rintro ⟨y, rfl⟩
    rfl

theorem product_common_kernel :
    (productProjection J hconj).ker ⊓ (productCharacter J hconj).ker =
      (SemidirectProduct.inl : Coord J →* FullProduct J hconj).range := by
  ext x
  constructor
  · rintro ⟨hA, hb⟩
    refine ⟨x.left, ?_⟩
    apply SemidirectProduct.ext
    · rfl
    · exact Prod.ext (show 1 = x.right.1 from hA.symm) (show 1 = x.right.2 from hb.symm)
  · rintro ⟨u, rfl⟩
    exact ⟨rfl, rfl⟩

/-- The original isotropic line generator. -/
def lineVector : Fin 5 → F := ![1,1,0,0,0]

private theorem unipotent_fixes_lineVector (u : Coord J) :
    (ambientGL J u).val *ᵥ lineVector = lineVector := by
  rw [ambientGL_val]
  apply fixes_line
  simp [lineVector, line]

private theorem unipotent_fixes_lineCovector (u : Coord J) :
    lineVector ᵥ* (ambientGL J u).val = lineVector := by
  rw [ambientGL_val]
  ext i
  fin_cases i <;> simp [lineVector, ambientMatrix, Matrix.vecMul,
    dotProduct, Fin.sum_univ_succ] <;> ring_nf <;> simp [CharTwo.two_eq_zero]

omit [CharP F 2] in
private theorem levi_fixes_lineVector (A : (middleForm J).specialSubgroup) :
    leviMatrix A.val.val *ᵥ lineVector = lineVector := by
  ext i
  fin_cases i <;> simp [lineVector, leviMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

omit [CharP F 2] in
private theorem levi_fixes_lineCovector (A : (middleForm J).specialSubgroup) :
    lineVector ᵥ* leviMatrix A.val.val = lineVector := by
  ext i
  fin_cases i <;> simp [lineVector, leviMatrix, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]

private theorem cubic_lineVector (c : F) (b : Cubic (F := F)) :
    (cubicGL c b).val *ᵥ lineVector = (b.val : F)^2 • lineVector := by
  rw [cubicGL_matrix]
  ext i
  fin_cases i <;> simp [lineVector, cubicAmbientMatrix, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ] <;> ring_nf <;> simp [CharTwo.two_eq_zero]

private theorem cubic_lineCovector (c : F) (b : Cubic (F := F)) :
    lineVector ᵥ* (cubicGL c b).val = (b.val : F) • lineVector := by
  rw [cubicGL_matrix]
  ext i
  fin_cases i <;> simp [lineVector, cubicAmbientMatrix, Matrix.vecMul,
    dotProduct, Fin.sum_univ_succ] <;> ring_nf <;> simp [CharTwo.two_eq_zero]

/-- Scalar projectivization does not identify different full block coordinates. -/
theorem fullMap_injective (c : F) (hc : c + J.conj c = 1) (hJ : J.form = 1) :
    Function.Injective (fullMap J hconj c hc hJ) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  let u := x.left
  let A := x.right.1
  let b := x.right.2
  have hp : project J (toSU J hJ u * (leviSU J hJ A * cubicSU J hconj c hc hJ b)) = 1 := by
    rw [map_mul, map_mul]
    exact congrArg Subtype.val hx
  have hs : ProjGenLinGroup.mk (ambientGL J u * (leviGL A.val * cubicGL c b)) = 1 :=
    congrArg Subtype.val hp
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hs
  obtain ⟨a, ha⟩ := hs
  have hv : (ambientGL J u * (leviGL A.val * cubicGL c b)).val *ᵥ lineVector =
      (b.val : F)^2 • lineVector := by
    simp only [Units.val_mul, ← mulVec_mulVec, cubic_lineVector, mulVec_smul]
    change (b.val : F)^2 • ((ambientGL J u).val *ᵥ (leviMatrix A.val.val *ᵥ lineVector)) = _
    rw [levi_fixes_lineVector, unipotent_fixes_lineVector]
  have hw : lineVector ᵥ* (ambientGL J u * (leviGL A.val * cubicGL c b)).val =
      (b.val : F) • lineVector := by
    simp only [Units.val_mul, ← vecMul_vecMul, unipotent_fixes_lineCovector]
    change (lineVector ᵥ* leviMatrix A.val.val) ᵥ* (cubicGL c b).val = _
    rw [levi_fixes_lineCovector, cubic_lineCovector]
  rw [← ha] at hv hw
  have hcol : (a : F) = (b.val : F)^2 := by
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar, lineVector,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hv 0
  have hrow : (a : F) = (b.val : F) := by
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar, lineVector,
      Matrix.vecMul, dotProduct, Fin.sum_univ_succ] using congrFun hw 0
  have hb : b = 1 := by
    apply Subtype.ext
    apply Units.ext
    change (b.val : F) = 1
    apply mul_right_cancel₀ b.val.ne_zero
    simpa only [pow_two, one_mul, Units.val_one] using hcol.symm.trans hrow
  have hx' : radicalLeviMap J hJ (⟨u, A⟩ : RadicalLevi J) = 1 := by
    change toParabolic J hJ u * leviParabolic J hJ A = 1
    change toParabolic J hJ u * (leviParabolic J hJ A * cubicParabolic J hconj c hc hJ b) = 1 at hx
    simpa only [hb, map_one, mul_one] using hx
  have hzero : (⟨u, A⟩ : RadicalLevi J) = 1 :=
    (radicalLeviMap_injective J hJ) (hx'.trans (map_one _).symm)
  apply SemidirectProduct.ext
  · exact congrArg (fun z : RadicalLevi J => z.left) hzero
  · exact Prod.ext (congrArg (fun z : RadicalLevi J => z.right) hzero) hb

end Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic.Blocks
