module
public import GorensteinWalter.ProjectiveSemilinear
public import GorensteinWalter.PGL2MapInjective
public import GorensteinWalter.PGL2DeterminantSquare
public import GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Projective descent for the quadratic semilinear local calculation

A coefficient-fixed projective matrix can be normalized by one nonzero
entry, giving an actual matrix over the fixed field. In an odd quadratic
extension every fixed-field scalar is a square upstairs, so the entire
embedded PGL₂ of the fixed field lies in the canonical PSL₂ layer.

Adapted from the intrinsic descent proof in Chapter15's
`SquareFields/CoefficientFixed.lean`, with its numerical congruence replaced
by the exact oddness hypothesis used by the proof. No later chapter is imported.
The marked embedding is used by `FullEscape.FieldCentralizer` to identify
the actual field-involution centralizer, including the fixed fields of
orders three and five.

Source: Aschbacher–Smith, A.2.3(2) and E.1.14(6), printed pp.33 and 214.
-/

public section
noncomputable section
open GorensteinWalter Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape
variable {F : Type*} [Field F]

private theorem mem_fixed_field_iff (σ : F ≃+* F) (x : F) :
    x ∈ FixedPoints.subfield (Subgroup.zpowers σ) F ↔ σ x = x := by
  change x ∈ MulAction.fixedPoints (Subgroup.zpowers σ) F ↔ σ x = x
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro h
    exact h ⟨σ, Subgroup.mem_zpowers σ⟩
  · intro h τ
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp τ.property
    change (τ : F ≃+* F) x = x
    rw [← hz]
    exact MulAction.mem_fixedBy_zpow (g := σ) (a := x) h z

private theorem scalar_entry (g : GL (Fin 2) F) (u : Fˣ) (i j : Fin 2) :
    (g * GeneralLinearGroup.scalar (Fin 2) u) i j = g.val i j * u := by
  change ((g : Matrix (Fin 2) (Fin 2) F) * Matrix.scalar (Fin 2) (u : F)) i j = _
  simp [Matrix.scalar, Matrix.mul_diagonal]

private theorem coefficient_mk (σ : F ≃+* F) (g : GL (Fin 2) F) :
    pgl2FieldAut F σ (ProjGenLinGroup.mk g) =
      ProjGenLinGroup.mk (GeneralLinearGroup.map σ.toRingHom g) :=
  pgl2RingEquiv_mk σ g

/-- Normalize a nonzero entry to descend every fixed projective class. -/
theorem projective_descent (σ : F ≃+* F) (x : PGL2 F) (hx : pgl2FieldAut F σ x = x) :
    x ∈ (ProjGenLinGroup.map (n := Fin 2)
      (FixedPoints.subfield (Subgroup.zpowers σ) F).subtype).range := by
  classical
  let K := FixedPoints.subfield (Subgroup.zpowers σ) F
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
  have hx' : ProjGenLinGroup.mk g =
      ProjGenLinGroup.mk (GeneralLinearGroup.map σ.toRingHom g) := by
    simpa only [coefficient_mk] using hx.symm
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hx'
  have he (i j : Fin 2) : σ (g.val i j) = g.val i j * (u : F) := by
    have h := congrArg (fun A : GL (Fin 2) F => A i j) hu
    simpa [scalar_entry] using h.symm
  obtain ⟨i, j, ha⟩ : ∃ i j, g.val i j ≠ 0 := by
    by_contra! h
    have hz : g.val = 0 := by ext i j; exact h i j
    have := g.det_ne_zero
    simp [hz] at this
  have hratio (k l : Fin 2) : σ (g.val k l / g.val i j) = g.val k l / g.val i j := by
    calc
      σ (g.val k l / g.val i j) = σ (g.val k l) / σ (g.val i j) := map_div₀ σ _ _
      _ = (g.val k l * (u : F)) / (g.val i j * (u : F)) :=
        congrArg₂ (fun a b : F => a / b) (he k l) (he i j)
      _ = g.val k l / g.val i j := mul_div_mul_right _ _ (Units.ne_zero u)
  let B : Matrix (Fin 2) (Fin 2) K := fun k l =>
    ⟨g.val k l / g.val i j, (mem_fixed_field_iff σ _).mpr (hratio k l)⟩
  have hB : B.map K.subtype = (g.val i j)⁻¹ • g.val := by
    ext k l
    change g.val k l / g.val i j = (g.val i j)⁻¹ * g.val k l
    rw [div_eq_mul_inv, mul_comm]
  have hdet : B.det ≠ 0 := by
    intro hz
    have hh := congrArg K.subtype hz
    rw [RingHom.map_det] at hh
    change (B.map K.subtype).det = 0 at hh
    rw [hB, Matrix.det_smul] at hh
    have hn := g.det_ne_zero
    simp only [Fintype.card_fin] at hh
    exact (mul_ne_zero (pow_ne_zero _ (inv_ne_zero ha)) hn) hh
  let b := GeneralLinearGroup.mkOfDetNeZero B hdet
  refine ⟨ProjGenLinGroup.mk b, ?_⟩
  rw [ProjGenLinGroup.map_mk, ProjGenLinGroup.mk_eq_mk_iff]
  refine ⟨Units.mk0 (g.val i j) ha, ?_⟩
  apply GeneralLinearGroup.ext
  intro k l
  rw [scalar_entry]
  change g.val k l / g.val i j * g.val i j = g.val k l
  exact div_mul_cancel₀ _ ha

/-- Classes defined over the fixed field are coefficient-fixed upstairs. -/
theorem fixed_image (σ : F ≃+* F)
    (x : PGL2 (FixedPoints.subfield (Subgroup.zpowers σ) F)) :
    pgl2FieldAut F σ (ProjGenLinGroup.map
      (FixedPoints.subfield (Subgroup.zpowers σ) F).subtype x) =
    ProjGenLinGroup.map (FixedPoints.subfield (Subgroup.zpowers σ) F).subtype x := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
  rw [ProjGenLinGroup.map_mk, coefficient_mk]
  congr 1
  apply GeneralLinearGroup.ext
  intro i j
  exact (mem_fixed_field_iff σ _).mp (g.val i j).property

variable [Finite F]

/-- Every element of the fixed field is a square in the quadratic field. -/
theorem square_upstairs {p : ℕ} (hodd : Odd p) (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    (a : FixedPoints.subfield (Subgroup.zpowers σ) F) : IsSquare (a : F) := by
  classical
  let K := FixedPoints.subfield (Subgroup.zpowers σ) F
  let := Fintype.ofFinite F
  let := Fintype.ofFinite K
  have hK : Fintype.card K = p := by
    rw [← Nat.card_eq_fintype_card]
    have hc := nat_card_eq_fixedSubfield_card_pow_orderOf F σ
    rw [hF, hσ] at hc
    nlinarith
  have hcard : Fintype.card F = p ^ 2 := by rwa [← Nat.card_eq_fintype_card]
  have hchar : ringChar F ≠ 2 := by
    intro h
    have hmod := FiniteField.even_card_of_char_two h
    rw [hcard] at hmod
    have ho : Odd (p ^ 2) := hodd.pow
    exact ho.not_two_dvd_nat (Nat.dvd_of_mod_eq_zero hmod)
  by_cases ha : a = 0
  · simp [ha]
  have haF : (a : F) ≠ 0 := by exact_mod_cast ha
  apply (FiniteField.isSquare_iff hchar haF).mpr
  have hpow : (a : F) ^ (p - 1) = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hK] at h
    exact congrArg K.subtype h
  obtain ⟨k, hk⟩ := hodd
  have hp1 : p - 1 = 2 * k := by omega
  have heq : p ^ 2 = 2 * ((p - 1) * (k + 1)) + 1 := by
    rw [hp1, hk]
    ring
  have he : p ^ 2 / 2 = (p - 1) * (k + 1) := by omega
  rw [hcard, he, pow_mul, hpow, one_pow]

/-- Every descended projective class has square determinant upstairs. -/
theorem image_mem_psl {p : ℕ} (hodd : Odd p) (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    (x : PGL2 (FixedPoints.subfield (Subgroup.zpowers σ) F)) :
    ProjGenLinGroup.map (FixedPoints.subfield (Subgroup.zpowers σ) F).subtype x ∈
      (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
  rw [ProjGenLinGroup.map_mk, pgl2_mk_mem_psl2_range_iff_det_isSquare]
  have h := square_upstairs hodd hF σ hσ (g.det :
    FixedPoints.subfield (Subgroup.zpowers σ) F)
  simpa only [GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe,
    Subfield.subtype_apply] using h

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.FullEscape
