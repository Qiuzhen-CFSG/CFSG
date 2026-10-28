module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow.Normalizer
public import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# The diagonal quotient of the unitary-four flag stabilizer

The first diagonal entry a and the product ab of the first two entries give
a surjective homomorphism from the whole flag stabilizer to Fˣ × (F^σ)ˣ.
The unitary equations and determinant one force ab into the fixed field.
The kernel is exactly the upper-unitriangular Sylow subgroup. Explicit
matrices diag(a, b/a, σ(a)/b, σ(a)⁻¹) lift every pair of torus parameters,
so the literal quotient has order (|F| - 1)(|F^σ| - 1).

These are the diagonal factors of the U₄(q) flag overlap used in
Aschbacher--Smith F.1.4--12, printed pp.260--264 of `refs/quasithin.pdf`.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
variable (F : Type*) [Field F] [CharP F 2] [Finite F]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "B" => borelSU F (form F σ hσ)
local notation "U" => upper F σ hσ

omit [CharP F 2] in
private theorem diagonal_relations (a : B) :
    σ (a.val.val.val 0 0) * a.val.val.val 3 3 = 1 ∧
    σ (a.val.val.val 1 1) * a.val.val.val 2 2 = 1 ∧
    a.val.val.val 0 0 * a.val.val.val 1 1 * a.val.val.val 2 2 * a.val.val.val 3 3 = 1 := by
  have ht := (mem_borel_iff_triangular F σ hσ a.val).mp a.property
  have hu := a.val.property.1
  change (form F σ hσ).conjTranspose a.val.val.val * gram F * a.val.val.val = gram F at hu
  have h03 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 3) hu
  have h12 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 1 2) hu
  have h10 := ht (by decide : (0 : Fin 4) < 1)
  have h20 := ht (by decide : (0 : Fin 4) < 2)
  have h30 := ht (by decide : (0 : Fin 4) < 3)
  have h21 := ht (by decide : (1 : Fin 4) < 2)
  have h31 := ht (by decide : (1 : Fin 4) < 3)
  have h32 := ht (by decide : (2 : Fin 4) < 3)
  have hd : a.val.val.val.det = 1 := congrArg Units.val a.val.property.2
  rw [Matrix.det_of_isUpperTriangular ht] at hd
  exact ⟨by simpa [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_succ,h10,h20,h30] using h03,
    by simpa [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_succ,h21,h31,h32] using h12,
    by simpa [Fin.prod_univ_succ, mul_assoc] using hd⟩

omit [CharP F 2] in
private theorem firstTwo_fixed (a : B) :
    σ (a.val.val.val 0 0 * a.val.val.val 1 1) =
      a.val.val.val 0 0 * a.val.val.val 1 1 := by
  obtain ⟨h03,h12,hd⟩ := diagonal_relations F σ hσ a
  have h3 : a.val.val.val 3 3 ≠ 0 := right_ne_zero_of_mul_eq_one h03
  have h2 : a.val.val.val 2 2 ≠ 0 := right_ne_zero_of_mul_eq_one h12
  apply mul_right_cancel₀ (mul_ne_zero h2 h3)
  rw [map_mul]
  calc
    _ = (σ (a.val.val.val 0 0) * a.val.val.val 3 3) *
      (σ (a.val.val.val 1 1) * a.val.val.val 2 2) := by ring
    _ = 1 := by rw [h03,h12,mul_one]
    _ = _ := by simpa [mul_assoc] using hd.symm

private def firstDiagonal : B →* F where
  toFun a := diagonal F σ hσ a 0
  map_one' := congrFun (map_one (diagonal F σ hσ)) 0
  map_mul' a b := congrFun (map_mul (diagonal F σ hσ) a b) 0

private def firstTwoDiagonal : B →* FixedField F σ where
  toFun a := ⟨a.val.val.val 0 0 * a.val.val.val 1 1, firstTwo_fixed F σ hσ a⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change diagonal F σ hσ (a*b) 0 * diagonal F σ hσ (a*b) 1 = _
    rw [map_mul]
    change (a.val.val.val 0 0 * b.val.val.val 0 0) *
      (a.val.val.val 1 1 * b.val.val.val 1 1) = _
    change _ = (a.val.val.val 0 0 * a.val.val.val 1 1) *
      (b.val.val.val 0 0 * b.val.val.val 1 1)
    ring

/-- The two independent diagonal coordinates are a in Fˣ and ab in (F^σ)ˣ. -/
def torusCharacter : B →* Fˣ × (FixedField F σ)ˣ :=
  (firstDiagonal F σ hσ).toHomUnits.prod (firstTwoDiagonal F σ hσ).toHomUnits

omit [CharP F 2] in
theorem torusCharacter_fst_val (a : B) :
    ((torusCharacter F σ hσ a).1 : F) = a.val.val.val 0 0 := by rfl

omit [CharP F 2] in
theorem torusCharacter_snd_val (a : B) :
    (((torusCharacter F σ hσ a).2 : FixedField F σ) : F) =
      a.val.val.val 0 0 * a.val.val.val 1 1 := by rfl

theorem torusCharacter_ker : (torusCharacter F σ hσ).ker = (U).subgroupOf B := by
  ext a
  change torusCharacter F σ hσ a = 1 ↔ a.val ∈ U
  rw [mem_upper_iff_entries]
  constructor
  · intro h
    have h0 : a.val.val.val 0 0 = 1 := congrArg (fun x : Fˣ × (FixedField F σ)ˣ =>
      (x.1 : F)) h
    have h01 : a.val.val.val 0 0 * a.val.val.val 1 1 = 1 :=
      congrArg (fun x : Fˣ × (FixedField F σ)ˣ => ((x.2 : FixedField F σ) : F)) h
    have h1 : a.val.val.val 1 1 = 1 := by simpa [h0] using h01
    obtain ⟨h03,h12,_⟩ := diagonal_relations F σ hσ a
    have h2 : a.val.val.val 2 2 = 1 := by simpa [h1] using h12
    have h3 : a.val.val.val 3 3 = 1 := by simpa [h0] using h03
    refine ⟨fun i j hij => (mem_borel_iff_triangular F σ hσ a.val).mp a.property hij, ?_⟩
    intro i
    fin_cases i <;> assumption
  · rintro ⟨_,hd⟩
    apply Prod.ext
    · apply Units.ext
      exact hd 0
    · apply Units.ext
      apply Subtype.ext
      change a.val.val.val 0 0 * a.val.val.val 1 1 = 1
      rw [hd 0, hd 1, mul_one]

/-- A diagonal special unitary lift of each pair of torus coordinates. -/
def torusLift (a : Fˣ) (b : (FixedField F σ)ˣ) : B := by
  let d : Fin 4 → F := ![(a : F), ((b : FixedField F σ) : F) / a,
    σ a / ((b : FixedField F σ) : F), (σ a)⁻¹]
  have ha : (a : F) ≠ 0 := a.ne_zero
  have hb : ((b : FixedField F σ) : F) ≠ 0 := by exact_mod_cast b.ne_zero
  have hsa : σ (a : F) ≠ 0 := by simp
  have hsb : σ ((b : FixedField F σ) : F) = ((b : FixedField F σ) : F) :=
    (b : FixedField F σ).property
  have hd : (Matrix.diagonal d).det = 1 := by
    rw [Matrix.det_diagonal]
    simp [d, Fin.prod_univ_succ]
    field_simp
  let g : SU F (form F σ hσ) :=
    ⟨GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d) (by rw [hd]; exact one_ne_zero),
      by
        change (form F σ hσ).conjTranspose (Matrix.diagonal d) * gram F *
          Matrix.diagonal d = gram F
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
            Fin.sum_univ_succ, d, ha,hb,hsa,hsb,hσ (a : F)],
      Units.ext hd⟩
  refine ⟨g, (mem_borel_iff_triangular F σ hσ g).mpr ?_⟩
  exact Matrix.blockTriangular_diagonal d

omit [CharP F 2] in
theorem torusCharacter_lift (a : Fˣ) (b : (FixedField F σ)ˣ) :
    torusCharacter F σ hσ (torusLift F σ hσ a b) = (a,b) := by
  apply Prod.ext
  · apply Units.ext
    rfl
  · apply Units.ext
    apply Subtype.ext
    change (a : F) * (((b : FixedField F σ) : F) / a) = _
    field_simp

omit [CharP F 2] in
theorem torusCharacter_surjective : Function.Surjective (torusCharacter F σ hσ) :=
  fun ⟨a,b⟩ => ⟨torusLift F σ hσ a b, torusCharacter_lift F σ hσ a b⟩

/-- The full flag quotient by its unitriangular subgroup is the actual diagonal torus. -/
def borelQuotientEquivTorus : (B ⧸ (U).subgroupOf B) ≃* Fˣ × (FixedField F σ)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (torusCharacter_ker F σ hσ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (torusCharacter F σ hσ)
      (torusCharacter_surjective F σ hσ))

theorem borel_quotient_card : Nat.card (B ⧸ (U).subgroupOf B) =
    (Nat.card F - 1) * (Nat.card (FixedField F σ) - 1) := by
  rw [Nat.card_congr (borelQuotientEquivTorus F σ hσ).toEquiv, Nat.card_prod,
    Nat.card_units, Nat.card_units]

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
