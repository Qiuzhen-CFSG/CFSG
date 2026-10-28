module

public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.Coordinates

/-!
# The scalar quotient of an orthogonal-frame torus

The map from the explicit SU₃ pair coordinates into the actual projective
group has kernel `{(a,a) | a³=1}`. The map `(a,b) ↦ (a/b,b³)` has exactly
the same kernel and is onto the product of the norm-one group and its cubic
power image. The first isomorphism theorem therefore gives the two cyclic
factors, of orders `q+1` and `(q+1)/gcd(3,q+1)`.

The full scalar kernel of SU₃ → PSU₃ lies in every frame torus. Consequently
the inverse image of the projective frame torus is exactly the special torus;
this supplies the literal subgroup comparison needed to lift normalizers.

Source: GLS4, Chapter 4, Lemma 3.11(b), and Chapter 2, Lemma 17.4,
`refs/KGroup/GLS4/{Chapter4,Chapter2}.tex`.
-/

public section

open Matrix Subgroup BenderSuzuki.MatrixGroups
open HermitianForm HermitianForm.IdentityGram HermitianForm.EvenInner
namespace UnitaryThree.OddTorusNormalizer
variable {E : Type*} [Field E]

@[expose] def projectivePairHom (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    (normOne J × normOne J) →* ProjectiveSpecialUnitaryMatrixGroup J :=
  J.specialToProjective.comp (specialPairHom J P)

theorem projectivePairHom_range (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    (projectivePairHom J P).range = projectiveFrameTorus J P := by
  rw [projectivePairHom, MonoidHom.range_comp, specialPairHom_range, projectiveFrameTorus]

theorem projectivePairHom_eq_one_iff (J : HermitianForm 3 E) (P : OrthogonalFrame J)
    (x : normOne J × normOne J) :
    projectivePairHom J P x = 1 ↔ x.1 = x.2 ∧ x.2 ^ 3 = 1 := by
  have hproj : projectivePairHom J P x = 1 ↔
      ProjGenLinGroup.mk (diagonalHom (pairDiagonal J x)) = 1 := by
    constructor
    · intro hx
      have hp := congrArg Subtype.val hx
      change (J.specialToProjective (specialPairHom J P x)).val = 1 at hp
      rw [J.specialToProjective_apply_val] at hp
      change ProjGenLinGroup.mk
        (P.val * diagonalHom (pairDiagonal J x) * P.val⁻¹) = 1 at hp
      apply (MulAut.conj (ProjGenLinGroup.mk P.val)).injective
      simpa only [MulAut.conj_apply, map_one, map_mul, map_inv] using hp
    · intro hx
      apply Subtype.ext
      change (J.specialToProjective (specialPairHom J P x)).val = 1
      rw [J.specialToProjective_apply_val]
      change ProjGenLinGroup.mk
        (P.val * diagonalHom (pairDiagonal J x) * P.val⁻¹) = 1
      simp only [map_mul, map_inv, hx, mul_one, mul_inv_cancel]
  rw [hproj, ProjGenLinGroup.mk_eq_one,
    GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  constructor
  · rintro ⟨c, hc⟩
    have h0 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 0) hc
    have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 1 1) hc
    have h2 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 2) hc
    simp only [diagonalHom, MonoidHom.coe_mk, OneHom.coe_mk, pairDiagonal,
      Matrix.diagonal_apply_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.scalar_apply] at h0 h1 h2
    have hab : x.1 = x.2 := Subtype.ext (Units.ext (h0.symm.trans h1))
    refine ⟨hab, ?_⟩
    have hh : (x.2 * x.2)⁻¹ = x.2 := by
      apply Subtype.ext
      apply Units.ext
      simpa [hab] using h2.symm.trans h1
    have hh' := inv_eq_iff_mul_eq_one.mp hh
    simpa only [pow_succ, pow_zero, one_mul] using hh'
  · rintro ⟨hab, hcube⟩
    refine ⟨(x.2.val : E), ?_⟩
    have hi : (x.2 * x.2)⁻¹ = x.2 := by
      apply inv_eq_iff_mul_eq_one.mpr
      simpa only [pow_succ, pow_zero, one_mul] using hcube
    have hiE : (x.2.val : E)⁻¹ * (x.2.val : E)⁻¹ = (x.2.val : E) := by
      simpa using congrArg (fun k : normOne J => (k.val : E)) hi
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagonalHom, pairDiagonal, Matrix.scalar_apply, hab,
        hiE]

@[expose] def pairQuotientHom (J : HermitianForm 3 E) :
    (normOne J × normOne J) →*
      normOne J × (powMonoidHom 3 : normOne J →* normOne J).range where
  toFun x := (x.1 / x.2, (powMonoidHom 3).rangeRestrict x.2)
  map_one' := by simp
  map_mul' x y := by ext <;> simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

theorem pairQuotientHom_surjective (J : HermitianForm 3 E) :
    Function.Surjective (pairQuotientHom J) := by
  rintro ⟨a, b⟩
  obtain ⟨c, hc⟩ := (powMonoidHom 3 : normOne J →* normOne J).rangeRestrict_surjective b
  refine ⟨(a * c, c), ?_⟩
  apply Prod.ext
  · simp [pairQuotientHom]
  · exact hc

theorem pairQuotientHom_ker (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    (pairQuotientHom J).ker = (projectivePairHom J P).ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, projectivePairHom_eq_one_iff]
  change (x.1 / x.2, (powMonoidHom 3).rangeRestrict x.2) = (1, 1) ↔ _
  rw [Prod.mk.injEq, div_eq_one]
  apply and_congr_right
  intro _
  exact Subtype.ext_iff

noncomputable def projectiveFrameTorusEquivNormOne
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    projectiveFrameTorus J P ≃*
      normOne J × (powMonoidHom 3 : normOne J →* normOne J).range :=
  (MulEquiv.subgroupCongr (projectivePairHom_range J P).symm).trans
    ((QuotientGroup.quotientKerEquivRange (projectivePairHom J P)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (pairQuotientHom_ker J P).symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective (pairQuotientHom J)
          (pairQuotientHom_surjective J))))

noncomputable def projectiveFrameTorusEquivCyclic [Finite E]
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (q : ℕ)
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    projectiveFrameTorus J P ≃*
      Multiplicative (ZMod (q + 1)) ×
        Multiplicative (ZMod ((q + 1) / Nat.gcd 3 (q + 1))) := by
  have hc := normOne_card J hcard
    (BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J q hcard hfixed)
  have hc3 : Nat.card (powMonoidHom 3 : normOne J →* normOne J).range =
      (q + 1) / Nat.gcd 3 (q + 1) := by
    rw [IsCyclic.card_powMonoidHom_range, hc, Nat.gcd_comm]
  let e3 := (zmodCyclicMulEquiv (inferInstance :
    IsCyclic (powMonoidHom 3 : normOne J →* normOne J).range)).symm.trans
      (MulEquiv.cast (M := fun n => Multiplicative (ZMod n)) hc3)
  exact (projectiveFrameTorusEquivNormOne J P).trans
    ((normOneEquivZMod J q hcard hfixed).prodCongr e3)

/-- The actual projective kernel is the diagonal cubic subgroup. -/
def projectivePairKernelEquiv (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    (projectivePairHom J P).ker ≃* (powMonoidHom 3 : normOne J →* normOne J).ker where
  toFun x := ⟨x.val.2, ((projectivePairHom_eq_one_iff J P x.val).mp x.property).2⟩
  invFun x := ⟨(x.val, x.val), (projectivePairHom_eq_one_iff J P _).mpr ⟨rfl, x.property⟩⟩
  left_inv x := Subtype.ext (Prod.ext
    ((projectivePairHom_eq_one_iff J P x.val).mp x.property).1.symm rfl)
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem projectivePairHom_ker_card [Finite E]
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (q : ℕ)
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    Nat.card (projectivePairHom J P).ker = Nat.gcd 3 (q + 1) := by
  rw [Nat.card_congr (projectivePairKernelEquiv J P).toEquiv,
    IsCyclic.card_powMonoidHom_ker,
    normOne_card J hcard
      (BenderSuzuki.External.huppert_II_10_4_conj_eq_frobenius J q hcard hfixed),
    Nat.gcd_comm]

theorem specialToProjective_ker_le_frameTorus
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    J.specialToProjective.ker ≤ specialFrameTorus J P := by
  intro x hx
  have hp : ProjGenLinGroup.mk x.val = 1 := by
    simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using congrArg Subtype.val hx
  have hc := ProjGenLinGroup.mk_eq_one.mp hp
  obtain ⟨c, he⟩ := (show x.val ∈ (GeneralLinearGroup.scalar (Fin 3)).range by
    rwa [← GeneralLinearGroup.center_eq_range_scalar])
  refine ⟨fun _ => c, ?_⟩
  have hd : diagonalHom (fun _ : Fin 3 => c) = x.val := by
    rw [← he]
    apply Units.ext
    rfl
  change diagonalHom (fun _ : Fin 3 => c) = P.val⁻¹ * x.val * (P.val⁻¹)⁻¹
  rw [hd, inv_inv, (Subgroup.mem_center_iff.mp hc P.val⁻¹)]
  simp [mul_assoc]

theorem projectiveFrameTorus_comap
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    (projectiveFrameTorus J P).comap J.specialToProjective = specialFrameTorus J P := by
  rw [projectiveFrameTorus, Subgroup.comap_map_eq,
    sup_eq_left.mpr (specialToProjective_ker_le_frameTorus J P)]

theorem projectiveFrameTorus_card [Finite E]
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) (q : ℕ)
    (hcard : Nat.card E = q ^ 2)
    (hfixed : Nat.card {x : E // J.conj x = x} = q) :
    Nat.card (projectiveFrameTorus J P) =
      (q + 1) * ((q + 1) / Nat.gcd 3 (q + 1)) := by
  rw [Nat.card_congr (projectiveFrameTorusEquivCyclic J P q hcard hfixed).toEquiv,
    Nat.card_prod, Nat.card_congr Multiplicative.toAdd,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, Nat.card_zmod]

/-- Normalizer membership lifts exactly along the actual special-to-projective map. -/
theorem projectiveFrameTorus_normalizer_comap
    (J : HermitianForm 3 E) (P : OrthogonalFrame J) :
    (normalizer (projectiveFrameTorus J P)).comap J.specialToProjective =
      normalizer (specialFrameTorus J P) := by
  rw [Subgroup.comap_normalizer_eq_of_surjective _ J.specialToProjective_surjective,
    projectiveFrameTorus_comap]

end UnitaryThree.OddTorusNormalizer
