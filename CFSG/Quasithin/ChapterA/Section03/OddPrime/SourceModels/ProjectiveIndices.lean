module

public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.Carriers
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Torus
public import Theory.SpecificGroups.SU3.ExtensionBorel.PGU
public import Theory.SpecificGroups.SU3.ProjectiveOuterInvolutions.NormalForm.Diagonal
public import Theory.LinearAlgebra.Hermitian.ProjectivePairTransport
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Tactic

/-!
# The index-three projective comparisons

The maps in this file are the maps in the source carriers.  In particular the
unitary comparison uses `componentInPGU`, whose domain is the literal image of
the determinant-one subgroup in PGL.  The order calculation is a quotient
calculation: determinants give the full unitary group over the special group,
while scalars are the kernels of the two projectivizations.

Source: Aschbacher--Smith, A.3.18(2), printed pp.51--52; the matrix order
calculations are the determinant-modulo-cubes calculation in GLS3, §2.7 and
the special-projective kernel calculation in GLS3, §6.1.
-/

@[expose] public section
noncomputable section

open scoped MatrixGroups
open Matrix Subgroup
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter1.Section02.LocalModels

namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels

private abbrev PGL3 (F : Type*) [Field F] := Matrix.ProjGenLinGroup (Fin 3) F
private abbrev PSL3 (F : Type*) [Field F] := Matrix.ProjectiveSpecialLinearGroup (Fin 3) F

private theorem card_fixed_of_square_card {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (q : ℕ) (hcard : Nat.card E = q ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ q) :
    Nat.card {x : E // J.conj x = x} = q := by
  classical
  let K : Subfield E := J.conj.toRingHom.eqLocusField (RingHom.id E)
  have hq : 1 < q := by
    have hE : 1 < Nat.card E := Finite.one_lt_card
    rw [hcard] at hE
    nlinarith
  have hmem (u : Eˣ) : u ∈ rootsOfUnity (q - 1) E ↔ J.conj (u : E) = u := by
    rw [mem_rootsOfUnity]
    constructor
    · intro hu
      have hv := congrArg Units.val hu
      change (u : E) ^ (q - 1) = 1 at hv
      rw [hconj, ← Nat.sub_add_cancel (show 1 ≤ q by omega), pow_succ, hv, one_mul]
    · intro hu
      apply Units.ext
      change (u : E) ^ (q - 1) = 1
      apply mul_right_cancel₀ (Units.ne_zero u)
      rw [one_mul, ← pow_succ, Nat.sub_add_cancel (show 1 ≤ q by omega), ← hconj, hu]
  let f : Kˣ →* rootsOfUnity (q - 1) E :=
    (Units.map K.subtype.toMonoidHom).codRestrict _ (fun u => by
      apply (hmem _).2
      exact u.val.property)
  have hf : Function.Bijective f := by
    constructor
    · intro u v huv
      apply Units.ext
      apply Subtype.ext
      exact congrArg (fun z : rootsOfUnity (q - 1) E => (z.val : E)) huv
    · intro u
      let x : K := ⟨u.val, (hmem u.val).1 u.property⟩
      have hx : x ≠ 0 := by
        intro hx
        exact Units.ne_zero u.val (congrArg Subtype.val hx)
      refine ⟨Units.mk0 x hx, ?_⟩
      apply Subtype.ext
      apply Units.ext
      rfl
  have hk : Nat.card K - 1 = q - 1 := by
    rw [← Nat.card_units K, Nat.card_congr (MulEquiv.ofBijective f hf).toEquiv,
      rootsOfUnity_eq_ker, IsCyclic.card_powMonoidHom_ker, Nat.card_units, hcard]
    apply Nat.gcd_eq_right
    rw [show q ^ 2 - 1 = (q + 1) * (q - 1) by
      simpa [mul_comm] using Nat.sq_sub_sq q 1]
    exact dvd_mul_left _ _
  change Nat.card K = q
  have hp : 0 < Nat.card K := Nat.card_pos
  omega

private theorem card_center_gl {F : Type*} [Field F] [Finite F] :
    Nat.card (Subgroup.center (GL (Fin 3) F)) = Nat.card F - 1 := by
  let s : Fˣ →* GL (Fin 3) F := GeneralLinearGroup.scalar (Fin 3)
  have hs : Function.Injective s := by
    intro a b hab
    apply Units.ext
    have h := congrArg (fun M : GL (Fin 3) F =>
      (M : Matrix (Fin 3) (Fin 3) F) 0 0) hab
    simpa [s, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h
  let e : Fˣ ≃* s.range := MulEquiv.ofBijective s.rangeRestrict
    ⟨fun _ _ h => hs (congrArg Subtype.val h), s.rangeRestrict_surjective⟩
  calc
    Nat.card (Subgroup.center (GL (Fin 3) F)) = Nat.card s.range := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
    _ = Nat.card Fˣ := (Nat.card_congr e.toEquiv).symm
    _ = Nat.card F - 1 := Nat.card_units F

private theorem card_pgl_mul_center {F : Type*} [Field F] [Finite F] :
    Nat.card (GL (Fin 3) F) = Nat.card (PGL3 F) * (Nat.card F - 1) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (GL (Fin 3) F)), card_center_gl]
  rfl

private theorem gcd_three_sub_one {q : ℕ} (hmod : q % 3 = 1) :
    Nat.gcd 3 (q - 1) = 3 := by
  have hzero : (q - 1) % 3 = 0 := by omega
  have hdvd : 3 ∣ q - 1 := (Nat.dvd_iff_mod_eq_zero).2 hzero
  exact Nat.dvd_antisymm (Nat.gcd_dvd_left _ _) (Nat.dvd_gcd (dvd_refl _) hdvd)

private theorem gcd_three_add_one {q : ℕ} (hmod : q % 3 = 2) :
    Nat.gcd 3 (q + 1) = 3 := by
  have hzero : (q + 1) % 3 = 0 := by omega
  have hdvd : 3 ∣ q + 1 := (Nat.dvd_iff_mod_eq_zero).2 hzero
  exact Nat.dvd_antisymm (Nat.gcd_dvd_left _ _) (Nat.dvd_gcd (dvd_refl _) hdvd)

/-- The literal `PSL₃` component has index three in `PGL₃`. -/
public theorem card_pgl_three_eq_three_mul_psl
    {F : Type*} [Field F] [Finite F] (hmod : Nat.card F % 3 = 1) :
    Nat.card (Matrix.ProjGenLinGroup (Fin 3) F) =
      3 * Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := by
  let : Fintype F := Fintype.ofFinite F
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hps := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  have hgl : Nat.card (GL (Fin 3) F) =
      ∏ i : Fin 3, (Nat.card F ^ 3 - Nat.card F ^ (i : ℕ)) := by
    simpa only [Nat.card_eq_fintype_card] using (Matrix.card_GL_field (𝔽 := F) 3)
  rw [← hgl, card_pgl_mul_center, gcd_three_sub_one hmod] at hps
  apply Nat.eq_of_mul_eq_mul_right (show 0 < Nat.card F - 1 by omega)
  simpa only [mul_comm] using hps.symm

private def standardForm {E : Type*} [Field E] (J : HermitianForm 3 E) :
    HermitianForm 3 E :=
  { conj := J.conj
    conj_involutive := J.conj_involutive
    form := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
    form_hermitian := by intro i j; fin_cases i <;> fin_cases j <;> simp
    form_nondegenerate := by simp [Matrix.det_fin_three] }

private def antiDiagonalMatrix {E : Type*} [Field E] (d : Eˣ) :
    Matrix (Fin 3) (Fin 3) E := !![0, 0, 1; 0, -(d : E), 0; 1, 0, 0]

private theorem antiDiagonal_det {E : Type*} [Field E] (d : Eˣ) :
    Matrix.det (antiDiagonalMatrix d) = (d : E) := by
  simp [antiDiagonalMatrix, Matrix.det_fin_three]

private theorem antiDiagonal_unitary {E : Type*} [Field E]
    (J : HermitianForm 3 E) (d : Eˣ) (hd : J.conj (d : E) * d = 1) :
    Matrix.GeneralLinearGroup.mkOfDetNeZero (antiDiagonalMatrix d)
        (by rw [antiDiagonal_det]; exact Units.ne_zero d) ∈
      (standardForm J).unitarySubgroup := by
  rw [(standardForm J).mem_unitarySubgroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [antiDiagonalMatrix, standardForm, HermitianForm.conjTranspose,
      Matrix.mul_apply, Fin.sum_univ_three, hd]

private def detNormHom {E : Type*} [Field E] (J : HermitianForm 3 E) :
    (standardForm J).unitarySubgroup →*
      BenderSuzuki.MatrixGroups.HermitianForm.EvenInner.normOne (standardForm J) where
  toFun u :=
    ⟨GeneralLinearGroup.det u.1, by
      change J.conj (GeneralLinearGroup.det u.1 : E) =
        (GeneralLinearGroup.det u.1 : E)⁻¹
      exact eq_inv_of_mul_eq_one_left
        ((standardForm J).unitary_det_norm_one u)
    ⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    simp

private theorem detNormHom_surjective {E : Type*} [Field E]
    (J : HermitianForm 3 E) : Function.Surjective (detNormHom J) := by
  intro d
  let d' : Eˣ := d.1
  let A : GL (Fin 3) E :=
    GeneralLinearGroup.mkOfDetNeZero (antiDiagonalMatrix d')
      (by rw [antiDiagonal_det]; exact Units.ne_zero d')
  have hA : A ∈ (standardForm J).unitarySubgroup := by
    apply antiDiagonal_unitary J d'
    have hd : J.conj (d' : E) = (d' : E)⁻¹ := d.property
    rw [hd]
    simp
  refine ⟨⟨A, hA⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  simp [detNormHom, A, d', antiDiagonal_det]

private def specialToDetKernel {E : Type*} [Field E] (J : HermitianForm 3 E) :
    (standardForm J).specialSubgroup ≃*
      (detNormHom J).ker :=
  { toFun := fun A =>
      ⟨⟨A.1, (standardForm J).specialSubgroup_le_unitarySubgroup A.property⟩,
        by
          simpa [detNormHom] using
            ((standardForm J).mem_specialSubgroup_iff A.1).mp A.property |>.2⟩
    invFun := fun A =>
      ⟨A.1.1, (standardForm J).mem_specialSubgroup_iff A.1.1 |>.mpr
        ⟨A.1.2, by
          simpa [detNormHom] using congrArg Subtype.val A.property⟩⟩
    left_inv := by intro A; rfl
    right_inv := by intro A; rfl
    map_mul' := by intro A B; rfl }

private theorem scalar_unitary_iff {E : Type*} [Field E]
    (J : HermitianForm 3 E) (d : Eˣ) :
    GeneralLinearGroup.scalar (Fin 3) d ∈ (standardForm J).unitarySubgroup ↔
      J.conj (d : E) * d = 1 := by
  constructor
  · intro h
    rw [(standardForm J).mem_unitarySubgroup_iff] at h
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 1) h
    simpa [standardForm, HermitianForm.conjTranspose,
      GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.mul_apply,
      Fin.sum_univ_three] using hh
  · exact fun h => (standardForm J).scalar_mem_unitary_of_norm_one d h

private def scalarToUnitaryKernel {E : Type*} [Field E]
    (J : HermitianForm 3 E) :
    BenderSuzuki.MatrixGroups.HermitianForm.EvenInner.normOne (standardForm J) →*
      (HermitianForm.ExtensionBorel.unitaryToPGU (standardForm J)).ker where
  toFun d :=
    ⟨⟨GeneralLinearGroup.scalar (Fin 3) d.val,
      (scalar_unitary_iff J d.val).mpr (by
        have hd : J.conj (d.val : E) = (d.val : E)⁻¹ := d.property
        rw [hd]
        simp)⟩,
      by
        apply Subtype.ext
        exact ProjGenLinGroup.mk_scalar d.val⟩
  map_one' := by
    apply Subtype.ext
    apply Subtype.ext
    simp
  map_mul' d e := by
    apply Subtype.ext
    apply Subtype.ext
    simp [map_mul]

private theorem scalarToUnitaryKernel_bijective {E : Type*} [Field E]
    (J : HermitianForm 3 E) : Function.Bijective (scalarToUnitaryKernel J) := by
  constructor
  · intro d e h
    apply Subtype.ext
    apply Units.ext
    have hh := congrArg (fun A : (HermitianForm.ExtensionBorel.unitaryToPGU
        (standardForm J)).ker =>
      (A.1.1 : Matrix (Fin 3) (Fin 3) E) 0 0) h
    simpa [scalarToUnitaryKernel, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] using hh
  · intro A
    have hmk : ProjGenLinGroup.mk A.1.1 = 1 :=
      congrArg Subtype.val (MonoidHom.mem_ker.mp A.property)
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hmk
    obtain ⟨d, hd⟩ := hmk
    have hdu : J.conj (d : E) * d = 1 := by
      have hs := (scalar_unitary_iff J d).mp (hd ▸ A.1.property)
      exact hs
    have hdn : d ∈ BenderSuzuki.MatrixGroups.HermitianForm.EvenInner.normOne
        (standardForm J) := eq_inv_of_mul_eq_one_left hdu
    refine ⟨⟨d, hdn⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hd

private noncomputable def scalarToUnitaryKernelEquiv {E : Type*} [Field E]
    (J : HermitianForm 3 E) :
    BenderSuzuki.MatrixGroups.HermitianForm.EvenInner.normOne (standardForm J) ≃*
      (HermitianForm.ExtensionBorel.unitaryToPGU (standardForm J)).ker :=
  MulEquiv.ofBijective (scalarToUnitaryKernel J) (scalarToUnitaryKernel_bijective J)

private theorem card_pgu_standard_eq_three_mul_psu {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (q : ℕ) (hcard : Nat.card E = q ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ q) (hmod : q % 3 = 2) :
    Nat.card (HermitianForm.ExtensionBorel.projectiveUnitary (standardForm J)) =
      3 * Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup
        (standardForm J)) := by
  let J₀ := standardForm J
  let : NeZero 3 := ⟨by decide⟩
  have hnorm : Nat.card (BenderSuzuki.MatrixGroups.HermitianForm.EvenInner.normOne J₀) = q + 1 :=
    BenderSuzuki.MatrixGroups.HermitianForm.EvenInner.normOne_card J₀ hcard hconj
  have hdet0 := (detNormHom J).ker.card_mul_index
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (detNormHom_surjective J), Subgroup.card_top] at hdet0
  have hdet : Nat.card J₀.specialSubgroup * (q + 1) = Nat.card J₀.unitarySubgroup := by
    rw [← Nat.card_congr (specialToDetKernel J).toEquiv, hnorm] at hdet0
    exact hdet0
  have hproj0 := (HermitianForm.ExtensionBorel.unitaryToPGU J₀).ker.card_mul_index
  rw [Subgroup.index_ker,
    MonoidHom.range_eq_top.mpr (HermitianForm.ExtensionBorel.unitaryToPGU_surjective J₀),
    Subgroup.card_top] at hproj0
  have hproj : (q + 1) *
      Nat.card (HermitianForm.ExtensionBorel.projectiveUnitary J₀) =
      Nat.card J₀.unitarySubgroup := by
    rw [← Nat.card_congr (scalarToUnitaryKernelEquiv J).toEquiv, hnorm] at hproj0
    exact hproj0
  have hPSU : Nat.card J₀.specialSubgroup =
      3 * Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J₀) := by
    let f := Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel.project J₀
    have hk := f.ker.card_mul_index
    rw [Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr
        (Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel.project_surjective J₀),
      Subgroup.card_top,
      Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel.card_project_kernel
        J₀ hconj hcard] at hk
    rw [gcd_three_add_one hmod] at hk
    simpa [Nat.mul_comm] using hk.symm
  have hPS : Nat.card (HermitianForm.ExtensionBorel.projectiveUnitary J₀) =
      Nat.card J₀.specialSubgroup := by
    have heq : Nat.card J₀.specialSubgroup * (q + 1) =
        Nat.card (HermitianForm.ExtensionBorel.projectiveUnitary J₀) * (q + 1) := by
      calc
        Nat.card J₀.specialSubgroup * (q + 1) = Nat.card J₀.unitarySubgroup := hdet
        _ = (q + 1) * Nat.card (HermitianForm.ExtensionBorel.projectiveUnitary J₀) := hproj.symm
        _ = Nat.card (HermitianForm.ExtensionBorel.projectiveUnitary J₀) * (q + 1) := by ring
    apply Nat.eq_of_mul_eq_mul_right (show 0 < q + 1 by omega)
    exact heq.symm
  exact hPS.trans hPSU

/-- The general projective unitary group has three times the order of PSU₃. -/
public theorem card_pgu_three_eq_three_mul_psu {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (q : ℕ) (hcard : Nat.card E = q ^ 2)
    (hconj : ∀ x : E, J.conj x = x ^ q) (hmod : q % 3 = 2) :
    Nat.card (HermitianForm.ExtensionBorel.projectiveUnitary J) =
      3 * Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := by
  let J₀ := standardForm J
  have hfixedJ : Nat.card {x : E // J.conj x = x} = q :=
    card_fixed_of_square_card J q hcard hconj
  have hfixed0 : Nat.card {x : E // J₀.conj x = x} = q := by
    exact card_fixed_of_square_card J₀ q hcard hconj
  obtain ⟨e, heU, heS⟩ :=
    HermitianForm.ProjectivePairTransport.exists_projective_pair_equiv_of_card J J₀ q hcard hfixedJ hcard hfixed0
  have hUmap : (J.unitarySubgroup.map ProjGenLinGroup.mk).map e =
      J₀.unitarySubgroup.map ProjGenLinGroup.mk := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (heU y).2 hy
    · intro hx
      exact ⟨e.symm x, (heU _).1 (by simpa using hx), e.apply_symm_apply x⟩
  have hSmap : (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J).map e =
      BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J₀ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (heS y).2 hy
    · intro hx
      exact ⟨e.symm x, (heS _).1 (by simpa using hx), e.apply_symm_apply x⟩
  let eU : HermitianForm.ExtensionBorel.projectiveUnitary J ≃*
      HermitianForm.ExtensionBorel.projectiveUnitary J₀ :=
    (e.subgroupMap (J.unitarySubgroup.map ProjGenLinGroup.mk)).trans
      (MulEquiv.subgroupCongr hUmap)
  let eS : BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J ≃*
      BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J₀ :=
    (e.subgroupMap (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)).trans
      (MulEquiv.subgroupCongr hSmap)
  calc
    Nat.card (HermitianForm.ExtensionBorel.projectiveUnitary J) =
        Nat.card (HermitianForm.ExtensionBorel.projectiveUnitary J₀) :=
      Nat.card_congr eU.toEquiv
    _ = 3 * Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J₀) :=
      card_pgu_standard_eq_three_mul_psu J q hcard hconj hmod
    _ = 3 * Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := by
      rw [Nat.card_congr eS.toEquiv]

/-- The component embedding has the literal `PSU` group as its range. -/
public theorem card_componentInPGU_range {E : Type*} [Field E]
    (J : HermitianForm 3 E) :
    Nat.card (HermitianForm.ExtensionBorel.componentInPGU J).range =
      Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := by
  let e : BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J ≃*
      (HermitianForm.ExtensionBorel.componentInPGU J).range :=
    MulEquiv.ofBijective (HermitianForm.ExtensionBorel.componentInPGU J).rangeRestrict
      ⟨fun a b h =>
        HermitianForm.ExtensionBorel.componentInPGU_injective J
          (congrArg Subtype.val h),
        (HermitianForm.ExtensionBorel.componentInPGU J).rangeRestrict_surjective⟩
  exact (Nat.card_congr e.toEquiv).symm

/-- The genuine PGU₃ has index three over the literal component embedding. -/
public theorem card_projectiveUnitary_eq_three_mul_component_range
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E) (q : ℕ)
    (hcard : Nat.card E = q ^ 2) (hconj : ∀ x : E, J.conj x = x ^ q)
    (hmod : q % 3 = 2) :
    Nat.card (HermitianForm.ExtensionBorel.projectiveUnitary J) =
      3 * Nat.card (HermitianForm.ExtensionBorel.componentInPGU J).range := by
  calc
    Nat.card (HermitianForm.ExtensionBorel.projectiveUnitary J) =
        3 * Nat.card (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      card_pgu_three_eq_three_mul_psu J q hcard hconj hmod
    _ = 3 * Nat.card (HermitianForm.ExtensionBorel.componentInPGU J).range := by
      rw [card_componentInPGU_range]

private theorem index_range_eq_three {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Injective f) (hc : Nat.card H = 3 * Nat.card G) :
    f.range.index = 3 := by
  have hr : Nat.card G = Nat.card f.range := Nat.card_congr (Equiv.ofInjective f hf)
  have hi := f.range.card_mul_index
  rw [← hr, hc] at hi
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := G))
  simpa only [mul_comm] using hi

/-- Index of the range of the canonical PSL₃ → PGL₃ map. -/
public theorem psl_three_toPGL_range_index
    {F : Type*} [Field F] [Finite F] (hmod : Nat.card F % 3 = 1) :
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 3) (R := F)).range.index = 3 := by
  exact index_range_eq_three _ ProjectiveSpecialLinearGroup.toPGL_injective
    (card_pgl_three_eq_three_mul_psl hmod)

/-- Index of the original PSU₃ component in the actual PGU₃ carrier. -/
public theorem componentInPGU_range_index
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E) (q : ℕ)
    (hcard : Nat.card E = q ^ 2) (hconj : ∀ x : E, J.conj x = x ^ q)
    (hmod : q % 3 = 2) :
    (HermitianForm.ExtensionBorel.componentInPGU J).range.index = 3 := by
  let : Finite (ProjGenLinGroup (Fin 3) E) :=
    Finite.of_surjective ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  exact index_range_eq_three _ (HermitianForm.ExtensionBorel.componentInPGU_injective J)
    (card_pgu_three_eq_three_mul_psu J q hcard hconj hmod)

/-- Signed model comparison, with the two model witnesses chosen independently. -/
public theorem card_pgl_sign_eq_three_mul_psl_sign
    {S R : Type*} [Group S] [Group R] (unitary : Bool) (q : ℕ)
    (hS : IsPSLSign S unitary 3 q)
    (hR : IsPGLSign R unitary q) (hsign : SignedCongruence unitary q) :
    Nat.card R = 3 * Nat.card S := by
  cases unitary with
  | false =>
      obtain ⟨F, _, _, hF, ⟨eF⟩⟩ := hS
      obtain ⟨K, _, _, hK, ⟨eK⟩⟩ := hR
      have hmod : q % 3 = 1 := by simpa [SignedCongruence] using hsign
      let : Fintype F := Fintype.ofFinite F
      let : Fintype K := Fintype.ofFinite K
      let ef : F ≃+* K := FiniteField.ringEquivOfCardEq (by
        simpa only [← Nat.card_eq_fintype_card] using hF.trans hK.symm)
      have hs : Nat.card (PSL3 F) = Nat.card (PSL3 K) :=
        Nat.card_congr (Atlas.fieldEquivPSL 3 ef).toEquiv
      calc
        Nat.card R = Nat.card (PGL3 K) := Nat.card_congr eK.toEquiv
        _ = 3 * Nat.card (PSL3 K) :=
          card_pgl_three_eq_three_mul_psl (by simpa only [hK] using hmod)
        _ = 3 * Nat.card S := by rw [← hs, Nat.card_congr eF.toEquiv]
  | true =>
      obtain ⟨F, _, _, J, hF, hconjF, ⟨eF⟩⟩ := hS
      obtain ⟨K, _, _, J', hK, hconjK, ⟨eK⟩⟩ := hR
      have hmod : q % 3 = 2 := by simpa [SignedCongruence] using hsign
      obtain ⟨e, _, heS⟩ :=
        HermitianForm.ProjectivePairTransport.exists_projective_pair_equiv_of_card
          J J' q hF (card_fixed_of_square_card J q hF hconjF)
          hK (card_fixed_of_square_card J' q hK hconjK)
      have hmap : (ProjectiveSpecialUnitaryMatrixGroup J).map e =
          ProjectiveSpecialUnitaryMatrixGroup J' := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact (heS y).2 hy
        · intro hx
          exact ⟨e.symm x, (heS _).1 (by simpa using hx), e.apply_symm_apply x⟩
      have hs : Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) =
          Nat.card (ProjectiveSpecialUnitaryMatrixGroup J') :=
        Nat.card_congr ((e.subgroupMap _).trans (MulEquiv.subgroupCongr hmap)).toEquiv
      calc
        Nat.card R = Nat.card (HermitianForm.ExtensionBorel.projectiveUnitary J') :=
          Nat.card_congr eK.toEquiv
        _ = 3 * Nat.card (ProjectiveSpecialUnitaryMatrixGroup J') :=
          card_pgu_three_eq_three_mul_psu J' q hK hconjK hmod
        _ = 3 * Nat.card S := by rw [← hs, Nat.card_congr eF.toEquiv]

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels
