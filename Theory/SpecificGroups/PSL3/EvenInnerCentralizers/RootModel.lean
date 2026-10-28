module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow
public import Theory.SpecificGroups.PSL3Even.UnipotentGeometry.ScalarGeneration

/-!
# The highest-root centralizer in PSL₃ over a binary field

The marked root is the literal matrix `1 + E₀₂`. Its special linear
centralizer consists of upper triangular matrices with equal first and last
diagonal entries. Trace invariance removes the scalar ambiguity when lifting
its projective centralizer in characteristic two. The centralizing torus is
`diag(a, a⁻², a)`; it acts on the two simple roots with weights `a³` and `a⁻³`.

These are intrinsic matrix calculations for the inner-involution case in
Aschbacher–Smith, 16.4.8, combined manuscript of 1 March 2004, printed p.1188.
Conjugacy of arbitrary involutions and the finite centralizer invariants are
separate results.
-/

@[expose] public section
noncomputable section
open scoped MatrixGroups
open Matrix.PSL3Even.UnipotentGeometry

namespace Matrix.PSL3.EvenInnerCentralizers
variable (F : Type*) [Field F]

/-- The marked highest-root transvection in the special linear group. -/
def rootSL : SL(3,F) := specialLinear F ⟨0,0,1⟩

/-- Its image in the genuine projective special linear group. -/
def root : PSL(3,F) := projection F (rootSL F)

def centralizerSL : Subgroup SL(3,F) := Subgroup.centralizer {rootSL F}

def centralizer : Subgroup PSL(3,F) := Subgroup.centralizer {root F}

theorem root_ne_one : root F ≠ 1 := by
  intro h
  have he : (⟨0,0,1⟩ : U F) = 1 :=
    projective_injective F (h.trans (map_one (projective F)).symm)
  have hc := congrArg U.c he
  exact one_ne_zero hc

theorem rootSL_sq [CharP F 2] : rootSL F ^ 2 = 1 := by
  rw [rootSL, ← map_pow, (square_eq_one_iff F _).mpr (Or.inl rfl), map_one]

theorem root_sq [CharP F 2] : root F ^ 2 = 1 := by
  rw [root, ← map_pow, rootSL_sq, map_one]

theorem mem_centralizerSL_iff (g : SL(3,F)) : g ∈ centralizerSL F ↔
    g.val 1 0 = 0 ∧ g.val 2 0 = 0 ∧ g.val 2 1 = 0 ∧ g.val 0 0 = g.val 2 2 := by
  change g ∈ Subgroup.centralizer {rootSL F} ↔ _
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h := h.symm
    have h10 := congrArg (fun a : SL(3,F) => a.val 1 2) h
    have h20 := congrArg (fun a : SL(3,F) => a.val 0 0) h
    have h21 := congrArg (fun a : SL(3,F) => a.val 0 1) h
    have hd := congrArg (fun a : SL(3,F) => a.val 0 2) h
    change (matrix F ⟨0,0,1⟩ * g.val) 1 2 = (g.val * matrix F ⟨0,0,1⟩) 1 2 at h10
    change (matrix F ⟨0,0,1⟩ * g.val) 0 0 = (g.val * matrix F ⟨0,0,1⟩) 0 0 at h20
    change (matrix F ⟨0,0,1⟩ * g.val) 0 1 = (g.val * matrix F ⟨0,0,1⟩) 0 1 at h21
    change (matrix F ⟨0,0,1⟩ * g.val) 0 2 = (g.val * matrix F ⟨0,0,1⟩) 0 2 at hd
    simp [matrix, Matrix.mul_apply, Fin.sum_univ_three] at h10 h20 h21 hd
    exact ⟨h10, h20, h21, (add_left_cancel (hd.trans (add_comm _ _))).symm⟩
  · rintro ⟨h10,h20,h21,hd⟩
    symm
    apply Subtype.ext
    change matrix F ⟨0,0,1⟩ * g.val = g.val * matrix F ⟨0,0,1⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, Matrix.mul_apply, Fin.sum_univ_three, h10,h20,h21,hd,add_comm]

theorem specialLinear_mem_centralizerSL (u : U F) :
    specialLinear F u ∈ centralizerSL F := by
  rw [mem_centralizerSL_iff]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem projective_mem_centralizer (u : U F) : projective F u ∈ centralizer F := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  exact congrArg (projection F)
    (Subgroup.mem_centralizer_singleton_iff.mp (specialLinear_mem_centralizerSL F u))

/-- The actual faithful unitriangular embedding into the marked centralizer. -/
def unipotentInCentralizer : U F →* centralizer F :=
  (projective F).codRestrict (centralizer F) (projective_mem_centralizer F)

theorem unipotentInCentralizer_injective : Function.Injective (unipotentInCentralizer F) :=
  fun _ _ h => projective_injective F (congrArg Subtype.val h)

/-- The full projective centralizer has exactly the special linear centralizer
as its preimage; scalar projective commutation creates no extra elements. -/
theorem centralizer_comap [CharP F 2] :
    (centralizer F).comap (projection F) = centralizerSL F := by
  ext g
  change projection F g ∈ Subgroup.centralizer {root F} ↔
    g ∈ Subgroup.centralizer {rootSL F}
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hp : projection F (g * rootSL F * g⁻¹) = projection F (rootSL F) := by
      simpa only [map_mul, map_inv, root, mul_inv_cancel_right] using
        congrArg (fun x => x * (projection F g)⁻¹) h
    have hc := (projection F).eq_iff.mp hp
    rw [projection_ker] at hc
    obtain ⟨r,_,hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
    have he : (g * rootSL F * g⁻¹).val = r • (rootSL F).val := by
      calc
        (g * rootSL F * g⁻¹).val =
            (rootSL F * ((rootSL F)⁻¹ * (g * rootSL F * g⁻¹))).val := by
              simp only [mul_inv_cancel_left]
        _ = (rootSL F).val * Matrix.scalar (Fin 3) r := by
              rw [SpecialLinearGroup.coe_mul, ← hr]
        _ = r • (rootSL F).val := by
              ext i j
              simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]
    have htroot : Matrix.trace (rootSL F).val = 1 := by
      change Matrix.trace (matrix F ⟨0,0,1⟩) = 1
      simp [matrix, Matrix.trace, Fin.sum_univ_three, CharTwo.add_self_eq_zero]
    have ht : Matrix.trace (g * rootSL F * g⁻¹).val = 1 := by
      change Matrix.trace (g.val * (rootSL F).val * g⁻¹.val) = 1
      rw [Matrix.trace_mul_cycle]
      have hi : g⁻¹.val * g.val = 1 := congrArg Subtype.val (inv_mul_cancel g)
      rw [hi, one_mul, htroot]
    rw [he, Matrix.trace_smul, htroot, smul_eq_mul, mul_one] at ht
    have he' : g * rootSL F * g⁻¹ = rootSL F :=
      Subtype.ext (by simpa [ht] using he)
    exact mul_inv_eq_iff_eq_mul.mp he'
  · intro h
    exact congrArg (projection F) h

theorem centralizer_map [CharP F 2] :
    (centralizerSL F).map (projection F) = centralizer F := by
  rw [← centralizer_comap]
  exact Subgroup.map_comap_eq_self_of_surjective (projection_surjective F) _

/-- The diagonal torus centralizing the marked highest root. -/
def torusSL : Fˣ →* SL(3,F) where
  toFun a := ⟨Matrix.diagonal ![(a : F), (↑a⁻¹ : F)^2, (a : F)], by
    simp only [Matrix.det_diagonal, Fin.prod_univ_three, Fin.isValue,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simp [pow_two]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  map_mul' a b := by
    apply Subtype.ext
    change Matrix.diagonal ![(↑(a*b) : F), (↑(a*b)⁻¹ : F)^2, (↑(a*b) : F)] =
      Matrix.diagonal ![(a : F), (↑a⁻¹ : F)^2, (a : F)] *
        Matrix.diagonal ![(b : F), (↑b⁻¹ : F)^2, (b : F)]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp [mul_pow, mul_comm]

@[simp] theorem torusSL_coe (a : Fˣ) :
    (torusSL F a).val = Matrix.diagonal ![(a : F), (↑a⁻¹ : F)^2, (a : F)] := rfl

theorem torusSL_mem_centralizerSL (a : Fˣ) : torusSL F a ∈ centralizerSL F := by
  rw [mem_centralizerSL_iff]
  simp

/-- The centralizing torus in the projective centralizer, with its scalar
kernel retained. -/
def torus : Fˣ →* centralizer F :=
  ((projection F).comp (torusSL F)).codRestrict (centralizer F) (fun a => by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    exact congrArg (projection F)
      (Subgroup.mem_centralizer_singleton_iff.mp (torusSL_mem_centralizerSL F a)))

theorem torusSL_conjugate (a : Fˣ) (u : U F) :
    torusSL F a * specialLinear F u * (torusSL F a)⁻¹ =
      specialLinear F ⟨(a : F)^3 * u.x, (↑a⁻¹ : F)^3 * u.y, u.c⟩ := by
  rw [← map_inv]
  apply Subtype.ext
  change Matrix.diagonal _ * matrix F u * Matrix.diagonal _ =
    matrix F ⟨(a : F)^3 * u.x, (↑a⁻¹ : F)^3 * u.y, u.c⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix, Matrix.diagonal_mul, Matrix.mul_diagonal,
      pow_succ, mul_assoc, mul_left_comm, mul_comm, a.ne_zero]
  field_simp

theorem torus_conjugate (a : Fˣ) (u : U F) :
    torus F a * unipotentInCentralizer F u * (torus F a)⁻¹ =
      unipotentInCentralizer F
        ⟨(a : F)^3 * u.x, (↑a⁻¹ : F)^3 * u.y, u.c⟩ := by
  apply Subtype.ext
  exact congrArg (projection F) (torusSL_conjugate F a u)

/-- Precisely the cube roots of unity disappear from the centralizing torus. -/
theorem torus_eq_one_iff (a : Fˣ) : torus F a = 1 ↔ a ^ 3 = 1 := by
  have he : torus F a = 1 ↔ projection F (torusSL F a) = 1 :=
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  rw [he, ← MonoidHom.mem_ker, projection_ker, SpecialLinearGroup.mem_center_iff]
  constructor
  · rintro ⟨r,_,hr⟩
    have h0 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 0 0) hr
    have h1 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 1 1) hr
    simp only [torusSL_coe, Matrix.scalar, Matrix.diagonal_apply_eq,
      Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    have hh := congrArg (fun x : F => x * (a : F)^2) (h0.symm.trans h1)
    have hi : (↑a⁻¹ : F)^2 * (a : F)^2 = 1 := by simp
    rw [hi] at hh
    apply Units.ext
    simpa [pow_succ, mul_comm] using hh
  · intro h
    have hv : (a : F)^3 = 1 := congrArg Units.val h
    have ha : (a : F) = (↑a⁻¹ : F)^2 := by
      apply mul_right_cancel₀ (pow_ne_zero 2 a.ne_zero)
      calc
        (a : F) * (a : F)^2 = 1 := by simpa [pow_succ, mul_comm] using hv
        _ = (↑a⁻¹ : F)^2 * (a : F)^2 := by simp
    refine ⟨(a : F), by simpa using hv, ?_⟩
    rw [torusSL_coe]
    change Matrix.diagonal (fun _ => (a : F)) = _
    apply congrArg Matrix.diagonal
    funext i
    fin_cases i
    · rfl
    · exact ha
    · rfl

/-- The actual centralizer torus generates the whole unipotent image in
the prime-to-p residual whenever its cube acts nontrivially. -/
theorem unipotent_le_primeToResidual_of_torus (p : ℕ) (a : Fˣ) {k : ℕ}
    (ha : a ^ (p ^ k) = 1) (hcube : a ^ 3 ≠ 1) :
    (unipotentInCentralizer F).range ≤ Subgroup.primeToResidual p (centralizer F) := by
  have hfirst : (a : F)^3 ≠ 1 := fun h => hcube (Units.ext h)
  have hsecond : (↑a⁻¹ : F)^3 ≠ 1 := by
    intro h
    have hi : (a⁻¹)^3 = 1 := Units.ext h
    have hh := congrArg Inv.inv hi
    exact hcube (by simpa only [← inv_pow, inv_inv, inv_one] using hh)
  apply range_le_primeToResidual_of_scalar_roots F p (unipotentInCentralizer F)
    (torus F a) (by rw [← map_pow, ha, map_one])
    ((a : F)^3) ((↑a⁻¹ : F)^3) hfirst hsecond
  · intro x
    simpa only [firstRoot, MonoidHom.coe_mk, OneHom.coe_mk,
      toAdd_ofAdd, mul_zero] using torus_conjugate F a (⟨x,0,0⟩ : U F)
  · intro x
    simpa only [secondRoot, MonoidHom.coe_mk, OneHom.coe_mk,
      toAdd_ofAdd, mul_zero] using torus_conjugate F a (⟨0,x,0⟩ : U F)

end Matrix.PSL3.EvenInnerCentralizers
