module

public import Theory.SpecificGroups.ClassicalUnitary.StandardForm
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Four-dimensional unitary flag coordinates

The antidiagonal Hermitian form has an isotropic coordinate point contained
in an isotropic coordinate plane. We construct their setwise stabilizers and
prove explicit matrix-entry membership tests and distinctness. In characteristic
two the projection from SU₄ to its image in PGL is injective: its scalar kernel
has fourth power one, so Frobenius injectivity makes it trivial.

This is the geometric starting point for the unitary-four case of
Aschbacher--Smith, F.1.12(I)(6), printed pp. 263--264. No Sylow, unipotent
radical, local quotient, or outer-automorphism assertion is made here.
-/

open Matrix BenderSuzuki.MatrixGroups
open scoped Pointwise
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
variable (F : Type*) [Field F]
def gram : Matrix (Fin 4) (Fin 4) F :=
  !![0,0,0,1; 0,0,1,0; 0,1,0,0; 1,0,0,0]
theorem gram_sq : gram F * gram F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [gram, Matrix.mul_apply, Fin.sum_univ_succ]
theorem gram_det_ne_zero : (gram F).det ≠ 0 := by
  have h := congrArg Matrix.det (gram_sq F)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact (mul_ne_zero_iff.mp (h ▸ one_ne_zero)).1

def form (σ : F ≃+* F) (hσ : Function.Involutive σ) : HermitianForm 4 F where
  conj := σ
  conj_involutive := hσ
  form := gram F
  form_hermitian := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [gram]
  form_nondegenerate := gram_det_ne_zero F

variable (J : HermitianForm 4 F)
abbrev SU := J.specialSubgroup
abbrev PSU := ProjectiveSpecialUnitaryMatrixGroup J

def project : SU F J →* PSU F J :=
  (ProjGenLinGroup.mk.comp J.specialSubgroup.subtype).codRestrict _ (by
    intro a
    exact ⟨a.val, a.property, rfl⟩)

/-- The image model contains exactly the projective classes of special unitary matrices. -/
theorem project_surjective : Function.Surjective (project F J) := by
  rintro ⟨g, a, ha, rfl⟩
  exact ⟨⟨a, ha⟩, rfl⟩

variable [Finite F] [CharP F 2]
theorem project_injective : Function.Injective (project F J) := by
  apply (injective_iff_map_eq_one (project F J)).mpr
  intro a ha
  have h : ProjGenLinGroup.mk a.val = 1 := congrArg Subtype.val ha
  obtain ⟨c, hc⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
    (ProjGenLinGroup.mk_eq_one.mp h)
  have hd : (a.val : Matrix (Fin 4) (Fin 4) F).det = 1 :=
    congrArg Units.val a.property.2
  rw [← hc] at hd
  have hp : c ^ 4 = 1 := by simpa using hd
  have he : c = 1 := (iterateFrobeniusEquiv F 2 2).injective (by
    change c ^ (2 ^ 2) = (1 : F) ^ (2 ^ 2)
    simpa using hp)
  apply Subtype.ext
  apply Units.ext
  rw [← hc, he]
  simp


/-- The first coordinate line, isotropic for `form`. -/
def pointSpace : Submodule F (Fin 4 → F) where
  carrier := {v | v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0}
  zero_mem' := by simp
  add_mem' := by rintro v w ⟨h1,h2,h3⟩ ⟨k1,k2,k3⟩; simp_all
  smul_mem' := by rintro c v ⟨h1,h2,h3⟩; simp_all

def planeSpace : Submodule F (Fin 4 → F) where
  carrier := {v | v 2 = 0 ∧ v 3 = 0}
  zero_mem' := by simp
  add_mem' := by rintro v w ⟨h2,h3⟩ ⟨k2,k3⟩; simp_all
  smul_mem' := by rintro c v ⟨h2,h3⟩; simp_all

omit [Finite F] [CharP F 2] in
theorem point_le_plane : pointSpace F ≤ planeSpace F := fun _ h => ⟨h.2.1, h.2.2⟩

def pointParabolicSU : Subgroup (SU F J) :=
  (MulAction.stabilizer (GL (Fin 4) F) (pointSpace F : Set (Fin 4 → F))).comap
    J.specialSubgroup.subtype

def planeParabolicSU : Subgroup (SU F J) :=
  (MulAction.stabilizer (GL (Fin 4) F) (planeSpace F : Set (Fin 4 → F))).comap
    J.specialSubgroup.subtype

def borelSU : Subgroup (SU F J) := pointParabolicSU F J ⊓ planeParabolicSU F J

omit [CharP F 2] in
theorem mem_pointParabolicSU (a : SU F J) : a ∈ pointParabolicSU F J ↔
    a.val.val 1 0 = 0 ∧ a.val.val 2 0 = 0 ∧ a.val.val 3 0 = 0 := by
  change a.val ∈ MulAction.stabilizer (GL (Fin 4) F) _ ↔ _
  rw [MulAction.mem_stabilizer_set' (Set.toFinite _)]
  change (∀ ⦃v : Fin 4 → F⦄, v 1 = 0 ∧ v 2 = 0 ∧ v 3 = 0 →
    (a.val.val.mulVec v) 1 = 0 ∧ (a.val.val.mulVec v) 2 = 0 ∧
      (a.val.val.mulVec v) 3 = 0) ↔ _
  constructor
  · intro h
    simpa [mulVec, dotProduct, Fin.sum_univ_succ] using
      h (v := ![1,0,0,0]) (by simp)
  · rintro ⟨h1,h2,h3⟩ v ⟨v1,v2,v3⟩
    simp [mulVec, dotProduct, Fin.sum_univ_succ, h1,h2,h3,v1,v2,v3]

omit [CharP F 2] in
theorem mem_planeParabolicSU (a : SU F J) : a ∈ planeParabolicSU F J ↔
    a.val.val 2 0 = 0 ∧ a.val.val 3 0 = 0 ∧
      a.val.val 2 1 = 0 ∧ a.val.val 3 1 = 0 := by
  change a.val ∈ MulAction.stabilizer (GL (Fin 4) F) _ ↔ _
  rw [MulAction.mem_stabilizer_set' (Set.toFinite _)]
  change (∀ ⦃v : Fin 4 → F⦄, v 2 = 0 ∧ v 3 = 0 →
    (a.val.val.mulVec v) 2 = 0 ∧ (a.val.val.mulVec v) 3 = 0) ↔ _
  constructor
  · intro h
    have h0 := h (v := ![1,0,0,0]) (by simp)
    have h1 := h (v := ![0,1,0,0]) (by simp)
    simp only [mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1
    simpa using And.intro h0.1 (And.intro h0.2 h1)
  · rintro ⟨h20,h30,h21,h31⟩ v ⟨v2,v3⟩
    simp [mulVec, dotProduct, Fin.sum_univ_succ, h20,h30,h21,h31,v2,v3]


omit [Finite F] [CharP F 2] in
theorem plane_isotropic (σ : F ≃+* F) (v w : Fin 4 → F)
    (hv : v ∈ planeSpace F) (hw : w ∈ planeSpace F) :
    dotProduct (fun i => σ (v i)) ((gram F).mulVec w) = 0 := by
  obtain ⟨hv2,hv3⟩ := hv
  obtain ⟨hw2,hw3⟩ := hw
  simp [gram, dotProduct, mulVec, Fin.sum_univ_succ, hv2,hv3,hw2,hw3]

private def swapPairsMatrix : Matrix (Fin 4) (Fin 4) F :=
  !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0]

omit [Finite F] [CharP F 2] in
private theorem swapPairs_sq : swapPairsMatrix F * swapPairsMatrix F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [swapPairsMatrix, Matrix.mul_apply, Fin.sum_univ_succ]

private def swapPairs (σ : F ≃+* F) (hσ : Function.Involutive σ) :
    SU F (form F σ hσ) := by
  let a : GL (Fin 4) F := ⟨swapPairsMatrix F, swapPairsMatrix F,
    swapPairs_sq F, swapPairs_sq F⟩
  refine ⟨a, ?_, ?_⟩
  · change (form F σ hσ).conjTranspose (swapPairsMatrix F) * gram F *
      swapPairsMatrix F = gram F
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [form, gram, swapPairsMatrix, HermitianForm.conjTranspose,
        Matrix.mul_apply, Fin.sum_univ_succ]
  · apply Units.ext
    have h := congrArg Matrix.det (swapPairs_sq F)
    rw [Matrix.det_mul, Matrix.det_one] at h
    apply (iterateFrobeniusEquiv F 2 1).injective
    change (swapPairsMatrix F).det ^ (2 ^ 1) = (1 : F) ^ (2 ^ 1)
    simpa [pow_two] using h

theorem parabolicsSU_ne (σ : F ≃+* F) (hσ : Function.Involutive σ) :
    pointParabolicSU F (form F σ hσ) ≠ planeParabolicSU F (form F σ hσ) := by
  intro h
  have hm : swapPairs F σ hσ ∈ planeParabolicSU F (form F σ hσ) := by
    rw [mem_planeParabolicSU]
    simp [swapPairs, swapPairsMatrix]
  have hn : swapPairs F σ hσ ∉ pointParabolicSU F (form F σ hσ) := by
    rw [mem_pointParabolicSU]
    simp [swapPairs, swapPairsMatrix]
  exact hn (h ▸ hm)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
