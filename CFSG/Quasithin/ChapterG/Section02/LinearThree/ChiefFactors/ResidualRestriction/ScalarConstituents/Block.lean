module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.Residual
/-!
# The natural and dual flags of the full point parabolic

The lower-right block gives a surjection P → GL₂(F), with an explicit
block diagonal section and scalar character det⁻¹. The natural line and
the dual annihilator plane are kernels of coordinate quotient maps.
Their actual quotient equivalences and action equations retain both
scalar characters: det⁻¹ on the line and det on the dual quotient.
The remaining actions are B on the natural quotient and B⁻ᵀ on the plane.

Source: Aschbacher–Smith, G.2.5(6–8), printed pp.335–336.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents
open Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

/-- The action on the natural quotient by the first coordinate line. -/
def blockValue : pointParabolicSL F →* Matrix (Fin 2) (Fin 2) F where
  toFun x := !![x.val.val 1 1, x.val.val 1 2; x.val.val 2 1, x.val.val 2 2]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    have hx := (mem_pointParabolicSL_iff F x).mp x.property
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, hx.1, hx.2]

def block : pointParabolicSL F →* GL (Fin 2) F := (blockValue F).toHomUnits

@[simp] theorem block_coe (x : pointParabolicSL F) :
    (block F x : Matrix (Fin 2) (Fin 2) F) =
      !![x.val.val 1 1, x.val.val 1 2; x.val.val 2 1, x.val.val 2 2] := rfl

theorem scalar_mul_block_det (x : pointParabolicSL F) :
    scalar F x * GeneralLinearGroup.det (block F x) = 1 := by
  apply Units.ext
  have hx := (mem_pointParabolicSL_iff F x).mp x.property
  have hd := x.val.property
  change x.val.val 0 0 * Matrix.det (blockValue F x) = 1
  rw [det_fin_three] at hd
  simpa [blockValue, det_fin_two, hx.1, hx.2, mul_sub, mul_assoc] using hd

theorem scalar_eq_det_inv (x : pointParabolicSL F) :
    scalar F x = (GeneralLinearGroup.det (block F x))⁻¹ :=
  eq_inv_of_mul_eq_one_left (scalar_mul_block_det F x)

/-- A literal block diagonal lift into SL₃, with the required determinant twist. -/
def blockLift (B : GL (Fin 2) F) : pointParabolicSL F :=
  ⟨⟨!![(↑(GeneralLinearGroup.det B)⁻¹ : F), 0, 0;
      0, (B : Matrix (Fin 2) (Fin 2) F) 0 0, (B : Matrix (Fin 2) (Fin 2) F) 0 1;
      0, (B : Matrix (Fin 2) (Fin 2) F) 1 0, (B : Matrix (Fin 2) (Fin 2) F) 1 1], by
    have hd : (↑(GeneralLinearGroup.det B)⁻¹ : F) *
        Matrix.det (B : Matrix (Fin 2) (Fin 2) F) = 1 :=
      Units.inv_mul (GeneralLinearGroup.det B)
    simpa [det_fin_three, det_fin_two, mul_sub, mul_assoc] using hd⟩,
    (mem_pointParabolicSL_iff F _).mpr ⟨rfl, rfl⟩⟩

@[simp] theorem block_lift (B : GL (Fin 2) F) : block F (blockLift F B) = B := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem block_surjective : Function.Surjective (block F) :=
  fun B => ⟨blockLift F B, block_lift F B⟩

/-- The genuine quotient map onto GL₂, without dropping its odd determinant. -/
noncomputable def blockQuotientEquiv :
    (pointParabolicSL F ⧸ (block F).ker) ≃* GL (Fin 2) F :=
  QuotientGroup.quotientKerEquivOfSurjective (block F) (block_surjective F)

@[simp] theorem blockQuotientEquiv_mk (x : pointParabolicSL F) :
    blockQuotientEquiv F (QuotientGroup.mk' (block F).ker x) = block F x := rfl

/-- Coordinate quotient by the invariant natural line. -/
def tail : (Fin 3 → F) →ₗ[F] (Fin 2 → F) where
  toFun v := ![v 1, v 2]
  map_add' u v := by ext i; fin_cases i <;> rfl
  map_smul' a v := by ext i; fin_cases i <;> rfl

/-- Coordinate quotient by the annihilator plane in the dual. -/
def head : (Fin 3 → F) →ₗ[F] F where
  toFun v := v 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def naturalLine : Submodule F (Fin 3 → F) := (tail F).ker

def dualPlane : Submodule F (Fin 3 → F) := (head F).ker

omit [Finite F] in
theorem mem_naturalLine (v : Fin 3 → F) : v ∈ naturalLine F ↔ v 1 = 0 ∧ v 2 = 0 := by
  change ![v 1, v 2] = (0 : Fin 2 → F) ↔ _
  constructor
  · intro hv; exact ⟨congrFun hv 0, congrFun hv 1⟩
  · rintro ⟨h1,h2⟩; simp [h1,h2]

omit [Finite F] in
@[simp] theorem mem_dualPlane (v : Fin 3 → F) : v ∈ dualPlane F ↔ v 0 = 0 := Iff.rfl

def lineVector (z : F) : Fin 3 → F := ![z,0,0]
def planeVector (w : Fin 2 → F) : Fin 3 → F := ![0,w 0,w 1]

theorem natural_line_action (x : pointParabolicSL F) (z : F) :
    x.val.val *ᵥ lineVector F z = lineVector F ((scalar F x : F) * z) := by
  have hx := (mem_pointParabolicSL_iff F x).mp x.property
  ext i
  fin_cases i <;>
    simp [lineVector, mulVec, dotProduct, Fin.sum_univ_three, hx.1, hx.2]

theorem natural_quotient_action (x : pointParabolicSL F) (v : Fin 3 → F) :
    tail F (x.val.val *ᵥ v) = (block F x : Matrix (Fin 2) (Fin 2) F) *ᵥ tail F v := by
  have hx := (mem_pointParabolicSL_iff F x).mp x.property
  ext i
  fin_cases i <;>
    simp [tail, mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, hx.1, hx.2]

theorem transpose_plane_action (x : pointParabolicSL F) (w : Fin 2 → F) :
    x.val.val.transpose *ᵥ planeVector F w =
      planeVector F ((block F x : Matrix (Fin 2) (Fin 2) F).transpose *ᵥ w) := by
  have hx := (mem_pointParabolicSL_iff F x).mp x.property
  ext i
  fin_cases i <;>
    simp [planeVector, mulVec, dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, hx.1, hx.2]

theorem dual_plane_action (x : pointParabolicSL F) (w : Fin 2 → F) :
    x.val⁻¹.val.transpose *ᵥ planeVector F w =
      planeVector F ((block F x⁻¹ : Matrix (Fin 2) (Fin 2) F).transpose *ᵥ w) :=
  transpose_plane_action F x⁻¹ w

theorem transpose_quotient_action (x : pointParabolicSL F) (v : Fin 3 → F) :
    head F (x.val.val.transpose *ᵥ v) = (scalar F x : F) * head F v := by
  have hx := (mem_pointParabolicSL_iff F x).mp x.property
  simp [head, mulVec, dotProduct, Fin.sum_univ_three, hx.1, hx.2]

theorem dual_quotient_action (x : pointParabolicSL F) (v : Fin 3 → F) :
    head F (x.val⁻¹.val.transpose *ᵥ v) = (↑(scalar F x)⁻¹ : F) * head F v := by
  rw [show x.val⁻¹.val = (x⁻¹).val.val from rfl, transpose_quotient_action, map_inv]

omit [Finite F] in
theorem tail_surjective : Function.Surjective (tail F) := by
  intro w
  refine ⟨planeVector F w, ?_⟩
  ext i; fin_cases i <;> rfl

omit [Finite F] in
theorem head_surjective : Function.Surjective (head F) := fun z => ⟨lineVector F z, rfl⟩

noncomputable def naturalQuotientEquiv : ((Fin 3 → F) ⧸ naturalLine F) ≃ₗ[F] (Fin 2 → F) :=
  (tail F).quotKerEquivOfSurjective (tail_surjective F)
noncomputable def dualQuotientEquiv : ((Fin 3 → F) ⧸ dualPlane F) ≃ₗ[F] F :=
  (head F).quotKerEquivOfSurjective (head_surjective F)

omit [Finite F] in
/-- The covector plane is the literal annihilator of the invariant line. -/
theorem dualPlane_annihilator (w : Fin 3 → F) :
    w ∈ dualPlane F ↔ ∀ v ∈ naturalLine F, dotProduct w v = 0 := by
  constructor
  · intro hw v hv
    have hv := (mem_naturalLine F v).mp hv
    simp [dotProduct, Fin.sum_univ_three, (mem_dualPlane F w).mp hw, hv.1, hv.2]
  · intro hw
    have h := hw (lineVector F 1) ((mem_naturalLine F _).mpr ⟨rfl,rfl⟩)
    simpa [dotProduct, Fin.sum_univ_three, lineVector, mem_dualPlane] using h

def naturalLineEquiv : naturalLine F ≃ₗ[F] F where
  toFun v := v.val 0
  invFun z := ⟨lineVector F z, (mem_naturalLine F _).mpr ⟨rfl,rfl⟩⟩
  left_inv v := by
    apply Subtype.ext
    have hv := (mem_naturalLine F v.val).mp v.property
    ext i; fin_cases i <;> simp [lineVector, hv.1, hv.2]
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def dualPlaneEquiv : dualPlane F ≃ₗ[F] (Fin 2 → F) where
  toFun v := tail F v.val
  invFun w := ⟨planeVector F w, rfl⟩
  left_inv v := by
    apply Subtype.ext
    have hv := (mem_dualPlane F v.val).mp v.property
    ext i; fin_cases i <;> simp [planeVector, tail, hv]
  right_inv w := by ext i; fin_cases i <;> rfl
  map_add' v w := (tail F).map_add v.val w.val
  map_smul' a v := (tail F).map_smul a v.val

omit [Finite F] in
theorem naturalLine_dimension : Module.finrank F (naturalLine F) = 1 := by
  rw [(naturalLineEquiv F).finrank_eq, Module.finrank_self]

omit [Finite F] in
theorem dualPlane_dimension : Module.finrank F (dualPlane F) = 2 := by
  rw [(dualPlaneEquiv F).finrank_eq, Module.finrank_fin_fun]

omit [Finite F] in
@[simp] theorem naturalQuotientEquiv_mk (v : Fin 3 → F) :
    naturalQuotientEquiv F ((naturalLine F).mkQ v) = tail F v :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

omit [Finite F] in
@[simp] theorem dualQuotientEquiv_mk (v : Fin 3 → F) :
    dualQuotientEquiv F ((dualPlane F).mkQ v) = head F v :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

theorem naturalLine_invariant (x : pointParabolicSL F) {v : Fin 3 → F}
    (hv : v ∈ naturalLine F) : x.val.val *ᵥ v ∈ naturalLine F := by
  change tail F (x.val.val *ᵥ v) = 0
  rw [natural_quotient_action, show tail F v = 0 from hv, mulVec_zero]

theorem dualPlane_invariant (x : pointParabolicSL F) {v : Fin 3 → F}
    (hv : v ∈ dualPlane F) : x.val⁻¹.val.transpose *ᵥ v ∈ dualPlane F := by
  change head F (x.val⁻¹.val.transpose *ᵥ v) = 0
  rw [dual_quotient_action, show head F v = 0 from hv, mul_zero]

end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents
