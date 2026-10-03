module

public import BenderSuzuki.SE.Final
public import Theory.Comparator.Defs
public import BenderSuzuki.MatrixGroups.SuzukiModel

/-!
# Bender–Suzuki classification in the shared finite-group models

This module translates the strongly embedded subgroup classification proved in
`BenderSuzuki.SE.Final` into the common involution, strong-embedding and matrix
model definitions exported by `Theory.Comparator.Defs`. The translation
identifies the Suzuki generators and the projective unitary model, and then
transports each of the three alternatives by group isomorphisms.

The definitions have one shared owner so this endpoint can be imported together
with the Stellmacher local analysis and the other classification ingredients.
The public theorem and all model names retain their existing statements.
The mathematical source is Bender–Suzuki, as developed in the preceding
`BenderSuzuki.SE` modules.
-/

universe u

open Matrix
open BenderSuzuki.MatrixGroups

private theorem benderSuzuki_isStronglyEmbedded
    {X : Type u} [Group X] [Finite X] {M : Subgroup X}
    (hM : IsStronglyEmbedded M) :
    BenderSuzuki.IsStronglyEmbedded M := by
  refine ⟨hM.1, ?_, ?_⟩
  · rcases hM.2.1 with ⟨x, hxM, hx⟩
    exact ⟨x, hxM, hx⟩
  · intro g hg x hxM hxright
    have hginv : g⁻¹ ∉ M := by
      intro hginv
      apply hg
      simpa using M.inv_mem hginv
    apply hM.2.2 g⁻¹ hginv x
    refine ⟨hxM, ?_⟩
    simpa [BenderSuzuki.PFchapter1section1.rightConjugate,
      Subgroup.conjBy] using hxright

private noncomputable def generalLinearEquivOfRingEquiv
    {ι K L : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] [Field L] (e : K ≃+* L) :
    GL ι K ≃* GL ι L :=
  Units.mapEquiv e.mapMatrix.toMulEquiv

@[simp] private theorem generalLinearEquivOfRingEquiv_apply
    {ι K L : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] [Field L] (e : K ≃+* L) (A : GL ι K) (i j : ι) :
    (generalLinearEquivOfRingEquiv e A : Matrix ι ι L) i j =
      e ((A : Matrix ι ι K) i j) :=
  rfl

private def projectiveGeneralLinearEquivOfRingEquiv
    {ι K L : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] [Field L] (e : K ≃+* L) :
    ProjGenLinGroup ι K ≃* ProjGenLinGroup ι L := by
  let f := ProjGenLinGroup.map (n := ι) e.toRingHom
  let g := ProjGenLinGroup.map (n := ι) e.symm.toRingHom
  apply MonoidHom.toMulEquiv f g
  · apply MonoidHom.ext
    intro x
    rcases ProjGenLinGroup.mk_surjective x with ⟨A, rfl⟩
    apply congrArg ProjGenLinGroup.mk
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp
  · apply MonoidHom.ext
    intro x
    rcases ProjGenLinGroup.mk_surjective x with ⟨A, rfl⟩
    apply congrArg ProjGenLinGroup.mk
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp

private theorem projectiveGeneralLinearEquivOfRingEquiv_mk
    {ι K L : Type*} [Fintype ι] [DecidableEq ι]
    [Field K] [Field L] (e : K ≃+* L) (A : GL ι K) :
    projectiveGeneralLinearEquivOfRingEquiv e (ProjGenLinGroup.mk A) =
      ProjGenLinGroup.mk (generalLinearEquivOfRingEquiv e A) := by
  rfl

/-- A standard projective special unitary group of exponent `n` is equivalent to `PSU3Model n`. -/
public theorem projectiveSpecialUnitary_equiv_psu3Model
    {E : Type} [Field E] [Finite E]
    (J : HermitianForm 3 E) (n : ℕ) (hn : 2 ≤ n)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hEcard : Nat.card E = (2 ^ n) ^ 2)
    (hfixedCard : Nat.card {z : E // J.conj z = z} = 2 ^ n) :
    Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃* PSU3Model n) := by
  let K := GaloisField 2 (2 * n)
  let S_E : Matrix (Fin 3) (Fin 3) E :=
    !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  let S_K : Matrix (Fin 3) (Fin 3) K :=
    !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  let U : Set (GL (Fin 3) K) :=
    {A |
      (Matrix.of fun i j ↦
          (A : Matrix (Fin 3) (Fin 3) K) j i ^ (2 ^ n)) *
          S_K * (A : Matrix (Fin 3) (Fin 3) K) = S_K ∧
        Matrix.GeneralLinearGroup.det A = 1}
  let : Fintype E := Fintype.ofFinite E
  let : Fintype K := Fintype.ofFinite K
  have hKcard : Nat.card K = (2 ^ n) ^ 2 := by
    calc
      Nat.card K = 2 ^ (2 * n) := by
        simpa [K] using GaloisField.card 2 (2 * n) (by omega)
      _ = 2 ^ (n * 2) := by rw [Nat.mul_comm]
      _ = (2 ^ n) ^ 2 := by rw [pow_mul]
  let eF : E ≃+* K :=
    FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
        hEcard, hKcard])
  let eGL : GL (Fin 3) E ≃* GL (Fin 3) K :=
    generalLinearEquivOfRingEquiv eF
  let ePGL : ProjGenLinGroup (Fin 3) E ≃*
      ProjGenLinGroup (Fin 3) K :=
    projectiveGeneralLinearEquivOfRingEquiv eF
  have hconj (x : E) : J.conj x = x ^ (2 ^ n) :=
    BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius
      J (2 ^ n) hEcard hfixedCard x
  have hformMap : J.form.map eF = S_K := by
    change J.form = S_E at hJ
    rw [hJ]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [S_E, S_K]
  have hconjTransposeMap (A : GL (Fin 3) E) :
      (J.conjTranspose (A : Matrix (Fin 3) (Fin 3) E)).map eF =
        Matrix.of fun i j ↦
          (eGL A : Matrix (Fin 3) (Fin 3) K) j i ^ (2 ^ n) := by
    ext i j
    simp [HermitianForm.conjTranspose, hconj, eGL]
  have hmatrixMap (A : GL (Fin 3) E) :
      (A : Matrix (Fin 3) (Fin 3) E).map eF =
        (eGL A : Matrix (Fin 3) (Fin 3) K) := by
    rfl
  have hspecial_iff (A : GL (Fin 3) E) :
      A ∈ J.specialSubgroup ↔ eGL A ∈ U := by
    constructor
    · intro hA
      rcases (J.mem_specialSubgroup_iff A).mp hA with ⟨hunit, hdet⟩
      constructor
      · have hmap := congrArg (fun M : Matrix (Fin 3) (Fin 3) E ↦
            M.map eF) hunit
        simp only [Matrix.map_mul] at hmap
        rw [hconjTransposeMap A, hformMap, hmatrixMap A] at hmap
        exact hmap
      · change Matrix.GeneralLinearGroup.det
          (Matrix.GeneralLinearGroup.map eF.toRingHom A) = 1
        rw [Matrix.GeneralLinearGroup.map_det, hdet, map_one]
    · rintro ⟨hunit, hdet⟩
      apply (J.mem_specialSubgroup_iff A).mpr
      constructor
      · refine eF.mapMatrix.injective ?_
        change (J.conjTranspose (A : Matrix (Fin 3) (Fin 3) E) *
          J.form * (A : Matrix (Fin 3) (Fin 3) E)).map eF =
            J.form.map eF
        simp only [Matrix.map_mul]
        rw [hconjTransposeMap A, hformMap, hmatrixMap A]
        exact hunit
      · change Matrix.GeneralLinearGroup.det
          (Matrix.GeneralLinearGroup.map eF.toRingHom A) = 1 at hdet
        rw [Matrix.GeneralLinearGroup.map_det] at hdet
        apply Units.ext
        refine eF.injective ?_
        simpa using congrArg Units.val hdet
  have hU : U =
      (J.specialSubgroup.map eGL.toMonoidHom : Set (GL (Fin 3) K)) := by
    ext A
    change A ∈ U ↔ A ∈ J.specialSubgroup.map eGL.toMonoidHom
    rw [Subgroup.mem_map_equiv, hspecial_iff]
    simp
  have hspecial :
      J.specialSubgroup.map eGL.toMonoidHom = Subgroup.closure U := by
    rw [hU, Subgroup.closure_eq]
  have hcomp :
      ePGL.toMonoidHom.comp ProjGenLinGroup.mk =
        ProjGenLinGroup.mk.comp eGL.toMonoidHom := by
    ext A
    exact projectiveGeneralLinearEquivOfRingEquiv_mk eF A
  have hprojective :
      (J.specialSubgroup.map ProjGenLinGroup.mk).map ePGL.toMonoidHom =
        (Subgroup.closure U).map ProjGenLinGroup.mk := by
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hspecial]
  have hmodel :
      (J.specialSubgroup.map ProjGenLinGroup.mk).map ePGL.toMonoidHom =
        PSU3Model n := by
    simpa [PSU3Model, U, S_K, K] using hprojective
  exact ⟨(ePGL.subgroupMap
    (J.specialSubgroup.map ProjGenLinGroup.mk)).trans
      (MulEquiv.subgroupCongr hmodel)⟩

/-- **The Bender-Suzuki theorem.** -/
public theorem bender_suzuki {X : Type u} [Group X] [Finite X] [IsSimpleGroup X] (M : Subgroup X)
    (hM : IsStronglyEmbedded M) : IsSimpleBenderGroup X := by
  have hclassification : BenderSuzuki.IsSimpleBenderGroup X :=
    BenderSuzuki.theorem_SE_simple M
      (benderSuzuki_isStronglyEmbedded hM) inferInstance
  rcases hclassification with ⟨⟨n, hn, hmodel⟩⟩ | ⟨⟨n, hn, hmodel⟩⟩ |
      ⟨⟨n, hn, E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard,
        hmodel⟩⟩
  · rcases hmodel with ⟨e⟩
    exact IsSimpleBenderGroup.isPSL2 n hn e
  · rcases hmodel with ⟨e⟩
    exact IsSimpleBenderGroup.isSuzuki n hn
      (e.trans (MulEquiv.subgroupCongr
        (szModel_eq_suzukiMatrixGroup n)).symm)
  · let : Field E := hEfield
    let : Finite E := hEfinite
    rcases hmodel with ⟨e⟩
    rcases projectiveSpecialUnitary_equiv_psu3Model
        J n hn hJ hEcard hfixedCard with ⟨ePSU⟩
    exact IsSimpleBenderGroup.isPSU3 n hn (e.trans ePSU)
