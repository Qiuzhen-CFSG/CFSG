module

public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Mathlib.Algebra.CharP.Two

/-!
# A fixed-field SL₂ subgroup in a unitary torus centralizer

For the standard antidiagonal Hermitian form in dimension three over a field
of characteristic two, SL₂ over the involution's fixed field embeds into the
centralizer of every norm-one torus element in the actual projective special
unitary matrix group. No finiteness or nontriviality hypothesis on the
involution or torus element is needed.

The block matrix `!![a, 0, b; 0, 1, 0; c, 0, d]` has determinant one. Its
fixed coefficients and characteristic two turn the Hermitian preservation
identity into the SL₂ determinant identity. Equality after projectivization
means equality up to a scalar; the middle diagonal entry one forces that
scalar to be one. A norm-one torus element has equal outer diagonal entries,
so it commutes with this entire block subgroup.

This is the standard rank-one block calculation, expressed using the actual
Hermitian matrix model and the torus from Huppert, *Endliche Gruppen I*,
II.10.12, as formalized in the imported source module. It supplies the local
subgroup needed by the even-characteristic unitary exclusion in the N-group
classification.
-/

open scoped Matrix

namespace BenderSuzuki.MatrixGroups

universe u

variable {K : Type u} [Field K] (J : HermitianForm 3 K)

private abbrev F := FixedBy.subfield K J.conj
private abbrev SL := Matrix.SpecialLinearGroup (Fin 2) (F J)

private def block (A : SL J) : Matrix (Fin 3) (Fin 3) K :=
  !![(A 0 0 : K), 0, (A 0 1 : K); 0, 1, 0; (A 1 0 : K), 0, (A 1 1 : K)]

private theorem det_two (A : SL J) :
    (A 0 0 : K) * (A 1 1 : K) - (A 0 1 : K) * (A 1 0 : K) = 1 := by
  have h := congrArg (fun x : F J => (x : K)) A.property
  simpa only [Matrix.det_fin_two, Subfield.coe_sub, Subfield.coe_mul,
    Subfield.coe_one] using h

private theorem fixed (x : F J) : J.conj (x : K) = (x : K) := x.property

private theorem block_det (A : SL J) : (block J A).det = 1 := by
  simpa [block, Matrix.det_fin_three] using det_two J A

private def blockGL (A : SL J) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (block J A) (by rw [block_det]; exact one_ne_zero)

variable [CharP K 2]

private theorem block_unitary (A : SL J)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    J.conjTranspose (block J A) * J.form * block J A = J.form := by
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [block, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, fixed]
  · rw [mul_comm, CharTwo.add_self_eq_zero]
  · simpa [CharTwo.sub_eq_add, mul_comm, add_comm] using det_two J A
  · simpa [CharTwo.sub_eq_add, mul_comm, add_comm] using det_two J A
  · rw [mul_comm, CharTwo.add_self_eq_zero]

private def blockSU (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) : SL J →* J.specialSubgroup :=
  { toFun := fun A => ⟨blockGL J A, by
      apply (J.mem_specialSubgroup_iff _).mpr
      constructor
      · exact block_unitary J A hJ
      · ext
        exact block_det J A⟩
    map_one' := by
      apply Subtype.ext
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change block J 1 i j = (1 : Matrix (Fin 3) (Fin 3) K) i j
      fin_cases i <;> fin_cases j <;> simp [block]
    map_mul' := by
      intro A B
      apply Subtype.ext
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      change block J (A * B) i j = (block J A * block J B) i j
      fin_cases i <;> fin_cases j <;>
        simp [block, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
          Fin.sum_univ_three] }

private def blockPSU (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    SL J →* ProjectiveSpecialUnitaryMatrixGroup J :=
  let f : SL J →* Matrix.ProjGenLinGroup (Fin 3) K :=
    Matrix.ProjGenLinGroup.mk.comp (J.specialSubgroup.subtype.comp (blockSU J hJ))
  f.codRestrict (ProjectiveSpecialUnitaryMatrixGroup J) (fun A =>
    Subgroup.mem_map_of_mem Matrix.ProjGenLinGroup.mk (blockSU J hJ A).property)

private theorem blockPSU_injective (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Function.Injective (blockPSU J hJ) := by
  intro A B h
  have hp := congrArg (fun x : ProjectiveSpecialUnitaryMatrixGroup J =>
    (x : Matrix.ProjGenLinGroup (Fin 3) K)) h
  change Matrix.ProjGenLinGroup.mk (blockGL J A) =
    Matrix.ProjGenLinGroup.mk (blockGL J B) at hp
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have hmiddle := congrArg (fun g : GL (Fin 3) K =>
    (g : Matrix (Fin 3) (Fin 3) K) 1 1) hu
  have huval : (u : K) = 1 := by
    simpa [blockGL, block, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar] using hmiddle
  have huone : u = 1 := Units.ext huval
  rw [huone, map_one, mul_one] at hu
  have hmat := congrArg (fun g : GL (Fin 3) K =>
    (g : Matrix (Fin 3) (Fin 3) K)) hu
  change block J A = block J B at hmat
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  apply Subtype.ext
  fin_cases i <;> fin_cases j
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 0) hmat
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 0 2) hmat
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 2 0) hmat
  · exact congrArg (fun M : Matrix (Fin 3) (Fin 3) K => M 2 2) hmat

omit [CharP K 2] in
private theorem blockGL_commutes (A : SL J) (k : Kˣ)
    (hk : J.conj (k : K) = (k : K)⁻¹) :
    blockGL J A * External.hermitianTorusGL J k =
      External.hermitianTorusGL J k * blockGL J A := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change (block J A * External.hermitianTorusMatrix J k) i j =
    (External.hermitianTorusMatrix J k * block J A) i j
  fin_cases i <;> fin_cases j <;>
    simp [block, External.hermitianTorusMatrix, hk, Matrix.mul_apply,
      Fin.sum_univ_three, mul_comm]

private theorem blockPSU_mem_centralizer
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (A : SL J) (k : Kˣ)
    (hk : J.conj (k : K) = (k : K)⁻¹) :
    blockPSU J hJ A ∈ Subgroup.centralizer
      ({External.hermitianTorusPSU J hJ k} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) := by
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  apply Subtype.ext
  change Matrix.ProjGenLinGroup.mk (blockGL J A) *
    Matrix.ProjGenLinGroup.mk (External.hermitianTorusGL J k) =
    Matrix.ProjGenLinGroup.mk (External.hermitianTorusGL J k) *
      Matrix.ProjGenLinGroup.mk (blockGL J A)
  rw [← map_mul, ← map_mul, blockGL_commutes J A k hk]

/-- The fixed-field SL₂ embeds in the centralizer of a norm-one torus element
of the projective special unitary group in characteristic two. -/
public theorem exists_sl2_embedding_centralizing_norm_one_torus
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (k : Kˣ)
    (hk : J.conj (k : K) = (k : K)⁻¹) :
    ∃ f : Matrix.SpecialLinearGroup (Fin 2) (FixedBy.subfield K J.conj) →*
      Subgroup.centralizer ({External.hermitianTorusPSU J hJ k} :
        Set (ProjectiveSpecialUnitaryMatrixGroup J)), Function.Injective f := by
  let f := (blockPSU J hJ).codRestrict
    (Subgroup.centralizer ({External.hermitianTorusPSU J hJ k} :
      Set (ProjectiveSpecialUnitaryMatrixGroup J)))
    (fun A => blockPSU_mem_centralizer J hJ A k hk)
  refine ⟨f, ?_⟩
  intro A B h
  exact blockPSU_injective J hJ (congrArg Subtype.val h)

end BenderSuzuki.MatrixGroups
