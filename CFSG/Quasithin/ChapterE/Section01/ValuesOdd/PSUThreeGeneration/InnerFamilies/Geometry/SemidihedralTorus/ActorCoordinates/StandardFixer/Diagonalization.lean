module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.ActorCoordinates.StandardFixer.Coordinates

/-!
# Exact diagonal representatives for the pointwise sign fixer

Use the three determinant-one sign matrices with a unique positive entry.
Each is fixed by every field automorphism. If a unitary semilinear formula
fixes their projective images, conjugation by its unitary representative
fixes them already in SU₃: the odd scalar kernel gives unique square-one
lifts. The resulting exact matrix commutation equations kill every
off-diagonal entry in odd characteristic. The diagonal entries are units
and satisfy the original Hermitian norm equations.

The sign construction follows `SU3.OddThreeLocal.Monomial.LocalCore.SignSubgroup`.
The odd-kernel argument also applies to unitary representatives outside SU₃,
so it preserves outer diagonal elements. This is the pointwise-fixer matrix
calculation for Aschbacher--Smith E.1.14(7), printed p.214, A.3.21(a)--(b),
printed p.55, and Aschbacher (1982), Lemma 4.11. Simultaneous normalization
of a two-subgroup remains a separate group-theoretic step.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus.StandardFixer
variable {F : Type*} [Field F]
open UnitaryThree.OddTorusNormalizer

private def coordinateSigns (i : Fin 3) : Fin 3 → Bool := fun k => decide (k ≠ i)

private theorem coordinateSign_val (i : Fin 3) :
    (signGL (F := F) (coordinateSigns i)).val = Matrix.diagonal (fun k => if k = i then 1 else -1) := by
  change Matrix.diagonal (fun k => ((if coordinateSigns i k then -1 else 1 : Fˣ) : F)) = _
  apply congrArg Matrix.diagonal
  funext k
  by_cases h : k = i <;> simp [coordinateSigns, h]

private theorem coordinateSign_sq (i : Fin 3) :
    signGL (F := F) (coordinateSigns i) ^ 2 = 1 := by
  apply Units.ext
  simp only [pow_two, Units.val_mul, coordinateSign_val, Matrix.diagonal_mul_diagonal, Units.val_one]
  convert Matrix.diagonal_one using 1
  congr 1
  funext k
  split_ifs <;> simp

private def coordinateSignSpecial (J : HermitianForm 3 F) (hJ : J.form = 1) (i : Fin 3) :
    J.specialSubgroup := ⟨signGL (coordinateSigns i), by
  constructor
  · apply (diagonal_mem_unitary J hJ _).2
    intro k
    by_cases h : k = i <;> simp [coordinateSigns, h]
  · apply Units.ext
    change (signGL (F := F) (coordinateSigns i)).val.det = 1
    rw [coordinateSign_val, Matrix.det_diagonal]
    fin_cases i <;> simp [Fin.prod_univ_three]⟩

private theorem coordinateSignSpecial_sq (J : HermitianForm 3 F) (hJ : J.form = 1) (i : Fin 3) :
    coordinateSignSpecial J hJ i ^ 2 = 1 := Subtype.ext (coordinateSign_sq i)

private theorem unitary_commutes_coordinateSigns [Finite F]
    (J : HermitianForm 3 F) (hJ : J.form = 1)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (σ : F ≃+* F)
    (u : J.unitarySubgroup)
    (ha : ∀ x : ProjectiveSpecialUnitaryMatrixGroup J,
      (a x).val = ProjGenLinGroup.mk u.val * ProjGenLinGroup.map σ.toRingHom x.val *
        (ProjGenLinGroup.mk u.val)⁻¹)
    (hfix : ∀ x ∈ standardFour J, a x = x) (i : Fin 3) :
    u.val * signGL (coordinateSigns i) = signGL (coordinateSigns i) * u.val := by
  let s := coordinateSignSpecial J hJ i
  have hs : J.specialToProjective s ∈ standardFour J :=
    subset_closure ⟨coordinateSigns i, J.specialToProjective_apply_val s⟩
  have himage : J.specialToProjective (J.specialUnitaryConj u s) = J.specialToProjective s := by
    apply Subtype.ext
    have hh := congrArg Subtype.val (hfix _ hs)
    rw [ha, J.specialToProjective_apply_val, ProjGenLinGroup.map_mk] at hh
    change ProjGenLinGroup.mk u.val * ProjGenLinGroup.mk
      (GeneralLinearGroup.map σ.toRingHom (signGL (coordinateSigns i))) *
      (ProjGenLinGroup.mk u.val)⁻¹ = _ at hh
    rw [map_signGL] at hh
    simpa only [J.specialToProjective_apply_val, J.specialUnitaryConj_val, map_mul, map_inv,
      s, coordinateSignSpecial] using hh
  have heq : J.specialUnitaryConj u s = s := by
    apply OddCentralLifting.involution_lift_unique J.specialToProjective
      J.odd_card_specialToProjective_ker J.specialToProjective_ker_le_center _
      (coordinateSignSpecial_sq J hJ i) himage
    apply Subtype.ext
    change (J.specialUnitaryConj u s).val ^ 2 = 1
    rw [J.specialUnitaryConj_val, conj_pow]
    have hsq : s.val ^ 2 = 1 := congrArg Subtype.val (coordinateSignSpecial_sq J hJ i)
    rw [hsq]
    simp
  have heq' : u.val * signGL (coordinateSigns i) * u.val⁻¹ = signGL (coordinateSigns i) := by
    simpa only [J.specialUnitaryConj_val, s, coordinateSignSpecial] using congrArg Subtype.val heq
  exact (mul_inv_eq_iff_eq_mul).mp heq'

/-- Every semilinear automorphism fixing all standard signs has a diagonal
unitary representative. Outer diagonal automorphisms are retained. -/
theorem diagonal_form_of_fixes_standardFour [Finite F]
    (J : HermitianForm 3 F) (hJ : J.form = 1) (h2 : (2 : F) ≠ 0)
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)) (σ : F ≃+* F)
    (hσ : σ = 1 ∨ σ = J.conj) (ha : J.HasUnitarySemilinearForm a σ)
    (hfix : ∀ x ∈ standardFour J, a x = x) : HasDiagonalSemilinearForm J a := by
  obtain ⟨u, hu⟩ := ha
  have hdiag (i j : Fin 3) (hij : i ≠ j) : u.val.val i j = 0 := by
    have h := unitary_commutes_coordinateSigns J hJ a σ u hu hfix i
    have hm := congrArg (fun g : GL (Fin 3) F => g.val i j) h
    change (u.val.val * (signGL (F := F) (coordinateSigns i)).val : Matrix (Fin 3) (Fin 3) F) i j =
      ((signGL (F := F) (coordinateSigns i)).val * u.val.val : Matrix (Fin 3) (Fin 3) F) i j at hm
    rw [coordinateSign_val] at hm
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Ne.symm hij] at hm
    have hh : (2 : F) * u.val.val i j = 0 := by linear_combination -hm
    exact (mul_eq_zero.mp hh).resolve_left h2
  have hmatrix : u.val.val = Matrix.diagonal (fun i => u.val.val i i) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp
    · simp [h, hdiag i j h]
  have hnonzero (i : Fin 3) : u.val.val i i ≠ 0 := by
    have hi : IsUnit (fun i => u.val.val i i) :=
      Matrix.isUnit_diagonal.mp (hmatrix ▸ u.val.isUnit)
    exact (hi.map (Pi.evalMonoidHom _ i)).ne_zero
  let d : Fin 3 → Fˣ := fun i => Units.mk0 (u.val.val i i) (hnonzero i)
  have hud : u.val = diagonalHom d := by
    apply Units.ext
    exact hmatrix
  refine ⟨d, σ, (diagonal_mem_unitary J hJ d).1 (hud ▸ u.property), hσ, ?_⟩
  intro x
  simpa only [hud] using hu x

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.SemidihedralTorus.StandardFixer
