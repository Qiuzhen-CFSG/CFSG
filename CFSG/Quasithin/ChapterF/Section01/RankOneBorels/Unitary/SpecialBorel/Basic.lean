module

public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary.FieldParameters
public import BenderSuzuki.External.Huppert.II.theorem_10_12

/-!
# Concrete SU₃ root group, torus, and projective projection

For the antidiagonal Hermitian form, the root and torus are the ranges of
Huppert's actual matrix homomorphisms. The projection to PSU₃ is surjective;
its kernel consists of scalar matrices and lies in the torus. In particular,
the kernel is central and has odd order in characteristic two.

Source: Huppert II.10.12; Aschbacher–Smith F.1.3(1), printed pp.259–260.
-/

noncomputable section
open BenderSuzuki BenderSuzuki.MatrixGroups
open External
namespace CFSG.Quasithin.ChapterF.Source.Unitary

variable {F : Type*} [Field F] (J : HermitianForm 3 F)

/-- The actual special-to-projective-unitary projection. -/
@[expose] public def suProjection :
    J.specialSubgroup →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (Matrix.ProjGenLinGroup.mk.comp J.specialSubgroup.subtype).codRestrict _
    (fun x => Subgroup.mem_map_of_mem _ x.property)

public theorem suProjection_surjective : Function.Surjective (suProjection J) := by
  rintro ⟨y, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The kernel is exactly the scalar special unitary matrices. -/
public theorem mem_suProjection_ker (x : J.specialSubgroup) :
    x ∈ (suProjection J).ker ↔
      (x : GL (Fin 3) F) ∈ Subgroup.center (GL (Fin 3) F) := by
  change suProjection J x = 1 ↔ _
  rw [Subtype.ext_iff]
  exact Matrix.ProjGenLinGroup.mk_eq_one

public theorem suProjection_ker_central :
    (suProjection J).ker ≤ Subgroup.center J.specialSubgroup := by
  intro x hx
  rw [Subgroup.mem_center_iff] at *
  intro y
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp ((mem_suProjection_ker J x).mp hx) y

variable (hstandard : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

/-- The concrete upper unitriangular subgroup in SU₃. -/
public abbrev suRoot : Subgroup J.specialSubgroup :=
  (hermitianUnipotentSU J hstandard).range

/-- The concrete diagonal torus in SU₃. -/
public abbrev suTorus : Subgroup J.specialSubgroup :=
  (hermitianTorusSU J hstandard).range

public theorem suProjection_comp_root :
    (suProjection J).comp (hermitianUnipotentSU J hstandard) =
      hermitianUnipotentPSU J hstandard := rfl

public theorem suProjection_comp_torus :
    (suProjection J).comp (hermitianTorusSU J hstandard) =
      hermitianTorusPSU J hstandard := rfl

public theorem suRoot_map_projection :
    (suRoot J hstandard).map (suProjection J) =
      (hermitianUnipotentPSU J hstandard).range := by
  rw [← MonoidHom.range_comp]
  rfl

public theorem suTorus_map_projection :
    (suTorus J hstandard).map (suProjection J) =
      (hermitianTorusPSU J hstandard).range := by
  rw [← MonoidHom.range_comp]
  rfl

public theorem suRoot_injective : Function.Injective (hermitianUnipotentSU J hstandard) := by
  intro z w h
  apply Subtype.ext
  apply Prod.ext
  · have h01 := congrArg
      (fun x : J.specialSubgroup => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1) h
    simpa [hermitianUnipotentSU, hermitianUnipotentGL, hermitianUnipotentMatrix] using h01
  · have h02 := congrArg
      (fun x : J.specialSubgroup => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2) h
    simpa [hermitianUnipotentSU, hermitianUnipotentGL, hermitianUnipotentMatrix] using h02

public theorem suTorus_injective : Function.Injective (hermitianTorusSU J hstandard) := by
  intro k l h
  apply Units.ext
  have h22 := congrArg
    (fun x : J.specialSubgroup => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2) h
  simpa [hermitianTorusSU, hermitianTorusGL, hermitianTorusMatrix] using h22

public theorem suRoot_disjoint_torus : Disjoint (suRoot J hstandard) (suTorus J hstandard) := by
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  rintro x ⟨⟨z, rfl⟩, k, hk⟩
  have h22 := congrArg
    (fun x : J.specialSubgroup => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2) hk
  have hk1 : k = 1 := Units.ext (by
    simpa [hermitianTorusSU, hermitianTorusGL, hermitianTorusMatrix,
      hermitianUnipotentSU, hermitianUnipotentGL, hermitianUnipotentMatrix] using h22)
  simpa [hk1] using hk.symm

public theorem suTorus_normalizes_root :
    suTorus J hstandard ≤ Subgroup.normalizer (suRoot J hstandard : Set J.specialSubgroup) := by
  have hc (k : Fˣ) (z : hermitianUnipotentCoord J) :
      hermitianTorusSU J hstandard k * hermitianUnipotentSU J hstandard z *
        (hermitianTorusSU J hstandard k)⁻¹ =
      hermitianUnipotentSU J hstandard (hermitianTorusAction J k z) := by
    apply mul_inv_eq_iff_eq_mul.mpr
    apply Subtype.ext
    exact hermitianTorusGL_mul_unipotent J k z
  rintro _ ⟨k, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨hermitianTorusAction J k z, (hc k z).symm⟩
  · rintro ⟨z, hz⟩
    have hh := congrArg (fun a =>
      (hermitianTorusSU J hstandard k)⁻¹ * a * hermitianTorusSU J hstandard k) hz
    have hi := hc k⁻¹ z
    simp only [map_inv, inv_inv] at hi
    refine ⟨hermitianTorusAction J k⁻¹ z, ?_⟩
    rw [← hi, hh]
    simp [mul_assoc]

/-- Every scalar special unitary matrix occurs in the specified diagonal torus. -/
public theorem suProjection_ker_le_torus :
    (suProjection J).ker ≤ suTorus J hstandard := by
  intro x hx
  have hxc := (mem_suProjection_ker J x).mp hx
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hxc
  obtain ⟨k, hk⟩ := hxc
  have hspecial := (J.mem_specialSubgroup_iff (x : GL (Fin 3) F)).mp x.property
  rw [← hk] at hspecial
  have hu := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A 0 2) hspecial.1
  have hn : J.conj (k : F) * (k : F) = 1 := by
    simpa [hstandard, HermitianForm.conjTranspose, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_three] using hu
  have hd := congrArg (fun a : Fˣ => (a : F)) hspecial.2
  have hcube : (k : F) ^ 3 = 1 := by
    simpa [Matrix.GeneralLinearGroup.det, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.det_fin_three, pow_succ, pow_two] using hd
  have h0 : (J.conj (k : F))⁻¹ = (k : F) := by
    apply inv_eq_of_mul_eq_one_right
    exact hn
  have hci : J.conj (k : F) = (k : F)⁻¹ := eq_inv_of_mul_eq_one_left hn
  have h1 : J.conj (k : F) * (k : F)⁻¹ = (k : F) := by
    rw [hci]
    field_simp
    simpa [pow_succ, pow_two] using hcube.symm
  refine ⟨k, ?_⟩
  apply Subtype.ext
  rw [← hk]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  change hermitianTorusMatrix J k i j = (Matrix.scalar (Fin 3) (k : F)) i j
  fin_cases i <;> fin_cases j <;>
    simp [hermitianTorusMatrix, Matrix.scalar_apply, h0, h1]

variable [Finite F]

public theorem suTorus_cyclic : IsCyclic (suTorus J hstandard) :=
  isCyclic_of_surjective (hermitianTorusSU J hstandard).rangeRestrict
    (hermitianTorusSU J hstandard).rangeRestrict_surjective

omit [Finite F] in
public theorem suTorus_card : Nat.card (suTorus J hstandard) = Nat.card F - 1 := by
  rw [← Nat.card_congr (MonoidHom.ofInjective (suTorus_injective J hstandard)).toEquiv]
  exact Nat.card_units F

omit [Finite F] in
public theorem suTorus_odd (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) : Odd (Nat.card (suTorus J hstandard)) := by
  rw [suTorus_card, hcard]
  have he : Even (2 ^ n) := even_two.pow_of_ne_zero (by omega)
  have hp : 0 < (2 ^ n) ^ 2 := by positivity
  exact Nat.Even.sub_odd (by omega) (he.pow_of_ne_zero (by decide)) odd_one

omit [Finite F] in
include hstandard in
/-- The scalar kernel has odd order, since it is contained in the odd torus. -/
public theorem suProjection_ker_odd (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) : Odd (Nat.card (suProjection J).ker) :=
  Odd.of_dvd_nat (suTorus_odd J hstandard n hn hcard)
    (Subgroup.card_dvd_of_le (suProjection_ker_le_torus J hstandard))

omit [Finite F] in
/-- The root meets the scalar kernel trivially. -/
public theorem suRoot_disjoint_kernel :
    Disjoint (suRoot J hstandard) (suProjection J).ker :=
  (suRoot_disjoint_torus J hstandard).mono_right (suProjection_ker_le_torus J hstandard)

omit [Finite F] in
/-- The full preimage of the projective root includes the scalar kernel. -/
public theorem projective_root_preimage :
    (hermitianUnipotentPSU J hstandard).range.comap (suProjection J) =
      suRoot J hstandard ⊔ (suProjection J).ker := by
  rw [← suRoot_map_projection, Subgroup.comap_map_eq]

omit [Finite F] in
/-- The genuine quotient by scalar special unitary matrices is PSU₃. -/
public def suProjectiveQuotientEquiv :
    J.specialSubgroup ⧸ (suProjection J).ker ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  QuotientGroup.quotientKerEquivOfSurjective _ (suProjection_surjective J)

end CFSG.Quasithin.ChapterF.Source.Unitary
