module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.Models
public import GorensteinWalter.PGL2MapInjective
public import GorensteinWalter.PGL2DeterminantSquare

/-!
# Fixed projective matrices in the canonical quadratic extension

A coefficient-fixed projective matrix descends after normalizing a nonzero
entry. Every element of the fixed field is a square in the odd quadratic
field, so the entire descended PGL₂ lies in the canonical PSL₂ layer.
The resulting direct product is the literal centralizer of the pure field
involution in `PureField.innerModel`, with its two coordinate maps retained.

The descent proof is adapted from the repository's Chapter15 `CoefficientFixed`
module, without its unnecessary congruence restriction and without importing
that later chapter. This is the subfield-centralizer input to the E.1.14(6)
calculation, including p=3 and p=5; it does not assert local E-generation.
Source: Aschbacher--Smith, E.1.2 and E.1.14(6), printed pp.210 and 214.
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape
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
theorem projective_fixed_image (σ : F ≃+* F)
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
theorem fixedField_isSquare {p : ℕ} (hodd : Odd p) (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    (a : FixedPoints.subfield (Subgroup.zpowers σ) F) : IsSquare (a : F) := by
  classical
  let K := FixedPoints.subfield (Subgroup.zpowers σ) F
  let := Fintype.ofFinite F
  let := Fintype.ofFinite K
  have hK : Fintype.card K = p := by
    rw [← Nat.card_eq_fintype_card]
    exact PureField.fixedSubfield_card hF σ
      ((orderOf_eq_prime_iff (x := σ)).mp hσ).1
      ((orderOf_eq_prime_iff (x := σ)).mp hσ).2
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
theorem fixed_image_mem_psl {p : ℕ} (hodd : Odd p) (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    (x : PGL2 (FixedPoints.subfield (Subgroup.zpowers σ) F)) :
    ProjGenLinGroup.map (FixedPoints.subfield (Subgroup.zpowers σ) F).subtype x ∈
      (ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
  rw [ProjGenLinGroup.map_mk, pgl2_mk_mem_psl2_range_iff_det_isSquare]
  have h := fixedField_isSquare hodd hF σ hσ (g.det :
    FixedPoints.subfield (Subgroup.zpowers σ) F)
  simpa only [GeneralLinearGroup.map_det, Units.coe_map, MonoidHom.coe_coe,
    Subfield.subtype_apply] using h


/-- Coefficient inclusion from the actual fixed field. -/
@[expose] def fixedProjectiveMap (σ : F ≃+* F) :
    PGL2 (FixedPoints.subfield (zpowers σ) F) →* PGL2 F :=
  ProjGenLinGroup.map (FixedPoints.subfield (zpowers σ) F).subtype

omit [Finite F] in
/-- The projective fixed-field inclusion is faithful. -/
theorem fixedProjectiveMap_injective (σ : F ≃+* F) :
    Function.Injective (fixedProjectiveMap σ) :=
  pgl2_map_injective_of_injective _ Subtype.val_injective

omit [Finite F] in
private theorem fixed_image_zpowers (σ : F ≃+* F) (τ : zpowers σ)
    (x : PGL2 (FixedPoints.subfield (zpowers σ) F)) :
    pgl2FieldAut F τ (fixedProjectiveMap σ x) = fixedProjectiveMap σ x := by
  obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective x
  change pgl2FieldAut F τ (ProjGenLinGroup.map _ (ProjGenLinGroup.mk g)) =
    ProjGenLinGroup.map _ (ProjGenLinGroup.mk g)
  rw [ProjGenLinGroup.map_mk, coefficient_mk]
  congr 1
  apply GeneralLinearGroup.ext
  intro i j
  exact (MulAction.mem_fixedPoints.mp (g.val i j).property) τ

/-- The two marked coordinates of the field-involution centralizer. -/
@[expose] def fixedProductMap (σ : F ≃+* F) :
    PGL2 (FixedPoints.subfield (zpowers σ) F) × zpowers σ →* PGammaL2 F where
  toFun x := ⟨fixedProjectiveMap σ x.1, x.2⟩
  map_one' := SemidirectProduct.ext (map_one _) rfl
  map_mul' x y := SemidirectProduct.ext (by
    change fixedProjectiveMap σ (x.1 * y.1) =
      fixedProjectiveMap σ x.1 * pgl2FieldAut F x.2 (fixedProjectiveMap σ y.1)
    rw [fixed_image_zpowers, map_mul]) rfl

omit [Finite F] in
/-- The product comparison retains both matrix and field coordinates. -/
theorem fixedProductMap_injective (σ : F ≃+* F) :
    Function.Injective (fixedProductMap σ) := by
  intro x y h
  apply Prod.ext
  · exact fixedProjectiveMap_injective σ (congrArg SemidirectProduct.left h)
  · exact Subtype.ext (congrArg SemidirectProduct.right h)

/-- The descended product actually lies in the specified inner model. -/
theorem fixedProductMap_mem_innerModel {p : ℕ} (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    (x : PGL2 (FixedPoints.subfield (zpowers σ) F) × zpowers σ) :
    fixedProductMap σ x ∈ innerModel F σ := by
  have hL : SemidirectProduct.inl (fixedProjectiveMap σ x.1) ∈ pGammaL2PSLRange F := by
    obtain ⟨y, hy⟩ := fixed_image_mem_psl hodd hF σ hσ x.1
    exact (mem_pGammaL2PSLRange_iff F _).mpr ⟨y, congrArg SemidirectProduct.inl hy⟩
  have hR : (SemidirectProduct.inr (x.2 : F ≃+* F) : PGammaL2 F) ∈
      zpowers (SemidirectProduct.inr σ) := by
    obtain ⟨z, hz⟩ := mem_zpowers_iff.mp x.2.property
    rw [← hz, map_zpow]
    exact zpow_mem (mem_zpowers _) z
  simpa only [innerModel, fixedProductMap, MonoidHom.coe_mk, OneHom.coe_mk,
    SemidirectProduct.mk_eq_inl_mul_inr] using mul_mem_sup hL hR

/-- A canonical element of the inner model: the pure coefficient involution. -/
@[expose] def pure (σ : F ≃+* F) : innerModel F σ :=
  ⟨SemidirectProduct.inr σ,
    (le_sup_right : zpowers (SemidirectProduct.inr σ) ≤ innerModel F σ) (mem_zpowers _)⟩

/-- Membership in the literal centralizer of the marked involution is exactly
membership in the descended product, not just an abstract group-type tag. -/
theorem mem_pureCentralizer_iff {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hne : σ ≠ 1)
    (x : innerModel F σ) :
    x ∈ centralizer ({pure σ} : Set (innerModel F σ)) ↔
      (x : PGammaL2 F) ∈ (fixedProductMap σ).range := by
  constructor
  · intro hx
    have he : (SemidirectProduct.inr σ : PGammaL2 F) * (x : PGammaL2 F) =
        (x : PGammaL2 F) * SemidirectProduct.inr σ := by
      exact congrArg Subtype.val ((mem_centralizer_iff.mp hx) _ (Set.mem_singleton _))
    have hl : pgl2FieldAut F σ (x : PGammaL2 F).left = (x : PGammaL2 F).left := by
      simpa using congrArg SemidirectProduct.left he
    obtain ⟨y, hy⟩ := projective_descent σ _ hl
    have hr : (x : PGammaL2 F).right ∈ zpowers σ := by
      rcases fieldAut_eq_one_or hp hF σ hne (x : PGammaL2 F).right with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_zpowers _
    exact ⟨(y, ⟨_, hr⟩), SemidirectProduct.ext hy rfl⟩
  · rintro ⟨y, hy⟩
    rw [mem_centralizer_iff]
    intro a ha
    rcases Set.mem_singleton_iff.mp ha with rfl
    apply Subtype.ext
    change (SemidirectProduct.inr σ : PGammaL2 F) * (x : PGammaL2 F) =
      (x : PGammaL2 F) * SemidirectProduct.inr σ
    rw [← hy]
    apply SemidirectProduct.ext
    · simpa only [fixedProductMap, fixedProjectiveMap, MonoidHom.coe_mk, OneHom.coe_mk,
        SemidirectProduct.mul_left, SemidirectProduct.left_inr,
        SemidirectProduct.right_inr, one_mul, map_one, mul_one] using
        projective_fixed_image σ y.1
    · change σ * (y.2 : F ≃+* F) = (y.2 : F ≃+* F) * σ
      obtain ⟨z, hz⟩ := mem_zpowers_iff.mp y.2.property
      rw [← hz]
      exact (Commute.refl σ).zpow_right z

/-- The full centralizer in the actual inner model is PGL₂ of the fixed
field times the actual cyclic field factor. -/
noncomputable def pureCentralizerEquiv {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    centralizer ({pure σ} : Set (innerModel F σ)) ≃*
      PGL2 (FixedPoints.subfield (zpowers σ) F) × zpowers σ := by
  have hne := ((orderOf_eq_prime_iff (x := σ)).mp hσ).2
  let f : (PGL2 (FixedPoints.subfield (zpowers σ) F) × zpowers σ) →*
      innerModel F σ := (fixedProductMap σ).codRestrict _
        (fixedProductMap_mem_innerModel hodd hF σ hσ)
  let j : (PGL2 (FixedPoints.subfield (zpowers σ) F) × zpowers σ) →*
      centralizer ({pure σ} : Set (innerModel F σ)) := f.codRestrict _ (fun x =>
        (mem_pureCentralizer_iff hp hF σ hne (f x)).mpr ⟨x, rfl⟩)
  exact (MulEquiv.ofBijective j ⟨fun x y h => fixedProductMap_injective σ
    (congrArg (fun z : centralizer ({pure σ} : Set (innerModel F σ)) =>
      ((z : innerModel F σ) : PGammaL2 F)) h), fun x : centralizer ({pure σ} : Set (innerModel F σ)) => by
      obtain ⟨y, hy⟩ := (mem_pureCentralizer_iff hp hF σ hne x.val).mp x.property
      exact ⟨y, Subtype.ext (Subtype.ext hy)⟩⟩).symm

/-- The inverse comparison is the literal marked matrix-and-field inclusion. -/
theorem pureCentralizerEquiv_symm_coe {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    (x : PGL2 (FixedPoints.subfield (zpowers σ) F) × zpowers σ) :
    (((pureCentralizerEquiv hp hodd hF σ hσ).symm x : innerModel F σ) : PGammaL2 F) =
      fixedProductMap σ x := by rfl

/-- The exact order of the literal pure-field centralizer. -/
theorem pureCentralizer_card {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hF : Nat.card F = p ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2) :
    Nat.card (centralizer ({pure σ} : Set (innerModel F σ))) = 2 * p * (p ^ 2 - 1) := by
  rw [Nat.card_congr (pureCentralizerEquiv hp hodd hF σ hσ).toEquiv,
    Nat.card_prod, Nat.card_zpowers, hσ, pgl2_card_formula]
  rw [fixedSubfield_card hF σ ((orderOf_eq_prime_iff (x := σ)).mp hσ).1
    ((orderOf_eq_prime_iff (x := σ)).mp hσ).2]
  ring

/-- The geometric pair needed by the subfield route: two literal involution
centralizers containing one Sylow, generating the canonical inner model,
and isomorphic to one another. Construction of this pair is a separate
obligation; the definition does not assert its existence. -/
@[expose] def HasSubfieldCentralizerPair (σ : F ≃+* F) : Prop :=
  ∃ (T : Sylow 2 (innerModel F σ)) (z : innerModel F σ),
    orderOf (z * pure σ) = 2 ∧
    (T : Subgroup (innerModel F σ)) ≤ centralizer ({pure σ} : Set (innerModel F σ)) ∧
    (T : Subgroup (innerModel F σ)) ≤ centralizer ({z * pure σ} : Set (innerModel F σ)) ∧
    centralizer ({pure σ} : Set (innerModel F σ)) ⊔
      centralizer ({z * pure σ} : Set (innerModel F σ)) = ⊤ ∧
    Nonempty (centralizer ({z * pure σ} : Set (innerModel F σ)) ≃*
      centralizer ({pure σ} : Set (innerModel F σ)))

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape
