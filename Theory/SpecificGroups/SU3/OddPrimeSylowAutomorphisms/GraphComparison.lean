module

public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Mathlib.Algebra.Ring.Action.End

/-!
# Entrywise fixed points of projective SU₃ in arbitrary characteristic

An entrywise projective action lifts to the actual special unitary group.
For a projective fixed point represented by `x`, its discrepancy `k` lies in
the scalar kernel and has cube one. The matrix `x * k²` is a fixed lift.
A fixed scalar has both square and cube one, so this lift is unique. Thus
projectivization is an isomorphism between the two fixed subgroups, with no
characteristic restriction.

For the antidiagonal Gram matrix, restrict every fixed matrix entry to the
actual fixed subfield. The unitary equation then becomes the orthogonal
equation for the same antidiagonal matrix, and determinant one is preserved.
This gives an injective homomorphism into the actual ternary special
orthogonal group and the resulting cardinal divisibility.

The fixed-lift construction extends the characteristic-two comparison in
`Theory.SpecificGroups.SU3.ProjectiveGraphFixed`; the scalar kernel is handled
by `SpecialProjectiveComparison`. Source: the graph-automorphism alternative
of Aschbacher–Smith, *The Classification of Quasithin Groups*, F.6.18(10)–(11),
printed pp.309–310, and its use in 15.4.18, printed pp.1162–1163.
Arbitrary-automorphism coverage and the orthogonal order bound are separate
mathematical obligations, not assertions of this module.
-/

open Matrix
namespace BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow

universe u
variable {E : Type u} [Field E] (J : HermitianForm 3 E)

/-- The determinant-one isometry group of this form is the split ternary
special orthogonal group. Its conjugation is the identity. -/
@[expose] public def splitOrthogonalForm (F : Type*) [Field F] : HermitianForm 3 F where
  conj := 1
  conj_involutive := fun _ => rfl
  form := !![0, 0, 1; 0, 1, 0; 1, 0, 0]
  form_hermitian := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  form_nondegenerate := by simp [Matrix.det_fin_three]

variable {γ : MulAut (ProjectiveSpecialUnitaryMatrixGroup J)}

/-- Lift a specified entrywise projective action to the actual special group. -/
public def specialEntrywiseAut (hγ : J.IsEntrywiseConjugation γ) :
    MulAut J.specialSubgroup where
  toFun x := ⟨GeneralLinearGroup.map J.conj.toRingHom x.val, by
    obtain ⟨y, hy, _⟩ := hγ x
    have he : GeneralLinearGroup.map J.conj.toRingHom x.val = y.val := Units.ext hy.symm
    rw [he]
    exact y.property⟩
  invFun x := ⟨GeneralLinearGroup.map J.conj.toRingHom x.val, by
    obtain ⟨y, hy, _⟩ := hγ x
    have he : GeneralLinearGroup.map J.conj.toRingHom x.val = y.val := Units.ext hy.symm
    rw [he]
    exact y.property⟩
  left_inv x := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact J.conj_involutive _
  right_inv x := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    exact J.conj_involutive _
  map_mul' x y := Subtype.ext (map_mul _ _ _)

@[simp] public theorem specialEntrywiseAut_val (hγ : J.IsEntrywiseConjugation γ)
    (x : J.specialSubgroup) :
    (specialEntrywiseAut J hγ x).val.val = x.val.val.map J.conj := by rfl

public theorem specialEntrywiseAut_involutive (hγ : J.IsEntrywiseConjugation γ) :
    Function.Involutive (specialEntrywiseAut J hγ) := by
  intro x
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact J.conj_involutive _

public theorem specialEntrywiseAut_projective (hγ : J.IsEntrywiseConjugation γ)
    (x : J.specialSubgroup) :
    J.specialToProjective (specialEntrywiseAut J hγ x) = γ (J.specialToProjective x) := by
  obtain ⟨y, hy, hxy⟩ := hγ x
  rw [hxy]
  congr 1
  exact Subtype.ext (Units.ext hy.symm)

/-- The scalar kernel has no nonidentity entrywise fixed element. This holds
in every characteristic: its scalars have both square and cube equal to one. -/
public theorem fixed_scalar_eq_one (hγ : J.IsEntrywiseConjugation γ)
    (x : J.specialSubgroup) (hx : J.specialToProjective x = 1)
    (hfix : specialEntrywiseAut J hγ x = x) : x = 1 := by
  have hz : x.val ∈ Subgroup.center (GL (Fin 3) E) := by
    apply ProjGenLinGroup.mk_eq_one.mp
    simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
      congrArg Subtype.val hx
  rw [GeneralLinearGroup.center_eq_range_scalar] at hz
  obtain ⟨d, hd⟩ := hz
  have hdfix : J.conj (d : E) = d := by
    have he := congrArg (fun z : J.specialSubgroup => z.val.val 0 0) hfix
    change J.conj (x.val.val 0 0) = x.val.val 0 0 at he
    simpa [← hd, GeneralLinearGroup.coe_scalar] using he
  have hd2 : d ^ 2 = 1 := by
    apply Units.ext
    have hu := (J.mem_unitarySubgroup_iff _).mp x.property.1
    rw [← hd] at hu
    have hscalar : J.conjTranspose (GeneralLinearGroup.scalar (Fin 3) d).val =
        Matrix.scalar (Fin 3) (d : E) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [HermitianForm.conjTranspose, GeneralLinearGroup.coe_scalar, hdfix]
      · simp [HermitianForm.conjTranspose, GeneralLinearGroup.coe_scalar, hij, Ne.symm hij]
    rw [hscalar] at hu
    have hentry (i j : Fin 3) : ((d : E) ^ 2 - 1) * J.form i j = 0 := by
      have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M i j) hu
      simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_mul, Matrix.mul_diagonal] at he
      linear_combination he
    have hdz : (d : E) ^ 2 - 1 = 0 := by
      by_contra hne
      have hzero : J.form = 0 := by
        ext i j
        exact (mul_eq_zero.mp (hentry i j)).resolve_left hne
      exact J.form_nondegenerate (by rw [hzero, Matrix.det_zero])
    exact sub_eq_zero.mp hdz
  have hd3 : d ^ 3 = 1 := by
    have hdet := x.property.2
    change GeneralLinearGroup.det x.val = 1 at hdet
    rw [← hd, GeneralLinearGroup.det_scalar] at hdet
    simpa using hdet
  have hd1 : d = 1 := by simpa [pow_succ, hd2] using hd3
  apply Subtype.ext
  rw [← hd, hd1, map_one]
  rfl

/-- Projectivization on the entrywise fixed special subgroup. -/
public def fixedProjectiveHom (hγ : J.IsEntrywiseConjugation γ) :
    (specialEntrywiseAut J hγ).fixedSubgroup →* γ.fixedSubgroup :=
  (J.specialToProjective.comp (specialEntrywiseAut J hγ).fixedSubgroup.subtype).codRestrict _ (by
    intro x
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    change γ (J.specialToProjective x.val) = J.specialToProjective x.val
    rw [← specialEntrywiseAut_projective J hγ,
      (MulAut.mem_fixedSubgroup _ _).mp x.property])

public theorem fixedProjectiveHom_injective (hγ : J.IsEntrywiseConjugation γ) :
    Function.Injective (fixedProjectiveHom J hγ) := by
  apply (fixedProjectiveHom J hγ).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro x hx
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  apply fixed_scalar_eq_one J hγ x.val
  · exact congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  · exact (MulAut.mem_fixedSubgroup _ _).mp x.property

/-- A projective fixed point has a fixed representative after multiplying its
lift by the square of its discrepancy in the scalar kernel. -/
public theorem fixedProjectiveHom_surjective (hγ : J.IsEntrywiseConjugation γ) :
    Function.Surjective (fixedProjectiveHom J hγ) := by
  intro b
  obtain ⟨x, hx⟩ := J.specialToProjective_surjective b.val
  let a := specialEntrywiseAut J hγ
  let k := x⁻¹ * a x
  have hk : J.specialToProjective k = 1 := by
    change J.specialToProjective (x⁻¹ * a x) = 1
    rw [map_mul, map_inv, specialEntrywiseAut_projective, hx,
      (MulAut.mem_fixedSubgroup _ _).mp b.property, inv_mul_cancel]
  have hk3 : k ^ 3 = 1 :=
    congrArg Subtype.val (J.specialToProjective_ker_cube ⟨k, hk⟩)
  have hki : k⁻¹ = k ^ 2 := by
    calc
      k⁻¹ = k⁻¹ * (k * k ^ 2) := by rw [← pow_succ', hk3, mul_one]
      _ = k ^ 2 := by group
  have hck : a k = k⁻¹ := by
    simp [k, a, map_mul, map_inv, specialEntrywiseAut_involutive J hγ x]
  have hcx : a x = x * k := by simp [k]
  have hz : a (x * k ^ 2) = x * k ^ 2 := by
    rw [map_mul, map_pow, hck, hcx]
    calc
      x * k * (k⁻¹) ^ 2 = x * k⁻¹ := by group
      _ = x * k ^ 2 := by rw [hki]
  refine ⟨⟨x * k ^ 2, (MulAut.mem_fixedSubgroup _ _).mpr hz⟩, Subtype.ext ?_⟩
  change J.specialToProjective (x * k ^ 2) = b.val
  simp [map_mul, map_pow, hk, hx]

/-- The projective and special entrywise fixed groups are isomorphic in every
characteristic, using the actual scalar quotient. -/
public noncomputable def projectiveFixedEquivSpecial
    (hγ : J.IsEntrywiseConjugation γ) :
    γ.fixedSubgroup ≃* (specialEntrywiseAut J hγ).fixedSubgroup :=
  (MulEquiv.ofBijective (fixedProjectiveHom J hγ)
    ⟨fixedProjectiveHom_injective J hγ, fixedProjectiveHom_surjective J hγ⟩).symm

private abbrev F := FixedBy.subfield E J.conj

private def fixedMatrix (hγ : J.IsEntrywiseConjugation γ)
    (x : (specialEntrywiseAut J hγ).fixedSubgroup) : Matrix (Fin 3) (Fin 3) (F J) :=
  fun i j => ⟨x.val.val.val i j, by
    exact congrArg (fun z : J.specialSubgroup => z.val.val i j)
      ((MulAut.mem_fixedSubgroup _ _).mp x.property)⟩

private theorem fixedMatrix_det (hγ : J.IsEntrywiseConjugation γ)
    (x : (specialEntrywiseAut J hγ).fixedSubgroup) : (fixedMatrix J hγ x).det = 1 := by
  apply (F J).subtype.injective
  rw [RingHom.map_det, map_one]
  exact congrArg Units.val x.val.property.2

private def fixedGL (hγ : J.IsEntrywiseConjugation γ)
    (x : (specialEntrywiseAut J hγ).fixedSubgroup) : GL (Fin 3) (F J) :=
  GeneralLinearGroup.mkOfDetNeZero (fixedMatrix J hγ x)
    (by rw [fixedMatrix_det]; exact one_ne_zero)

private theorem fixedGL_mem_orthogonal
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hγ : J.IsEntrywiseConjugation γ)
    (x : (specialEntrywiseAut J hγ).fixedSubgroup) :
    fixedGL J hγ x ∈ (splitOrthogonalForm (F J)).specialSubgroup := by
  apply ((splitOrthogonalForm (F J)).mem_specialSubgroup_iff _).mpr
  constructor
  · change (fixedMatrix J hγ x).transpose * (splitOrthogonalForm (F J)).form *
        fixedMatrix J hγ x = (splitOrthogonalForm (F J)).form
    apply Matrix.map_injective (F J).subtype.injective
    have hm : (fixedMatrix J hγ x).map (F J).subtype = x.val.val.val := rfl
    have hf : (splitOrthogonalForm (F J)).form.map (F J).subtype = J.form := by
      rw [hJ]
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have hadj : J.conjTranspose x.val.val.val = x.val.val.val.transpose := by
      ext i j
      exact (fixedMatrix J hγ x j i).property
    dsimp only
    simp only [Matrix.map_mul, Matrix.transpose_map, hm, hf]
    rw [← hadj]
    exact (J.mem_specialSubgroup_iff _).mp x.val.property |>.1
  · apply Units.ext
    exact fixedMatrix_det J hγ x

/-- Restrict the entries of an entrywise fixed special-unitary matrix to the
actual fixed subfield; its Hermitian equation becomes an orthogonal equation. -/
public def specialFixedToOrthogonal
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hγ : J.IsEntrywiseConjugation γ) :
    (specialEntrywiseAut J hγ).fixedSubgroup →*
      (splitOrthogonalForm (FixedBy.subfield E J.conj)).specialSubgroup where
  toFun x := ⟨fixedGL J hγ x, fixedGL_mem_orthogonal J hJ hγ x⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    change (1 : Matrix (Fin 3) (Fin 3) E) i j =
      ((1 : Matrix (Fin 3) (Fin 3) (F J)) i j : E)
    exact (congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M i j)
      (map_one ((F J).subtype.mapMatrix))).symm
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    apply Matrix.ext
    intro i j
    apply Subtype.ext
    change (x.val.val.val * y.val.val.val) i j =
      (F J).subtype ((fixedMatrix J hγ x * fixedMatrix J hγ y) i j)
    simp only [Matrix.mul_apply, map_sum, map_mul]
    rfl

public theorem specialFixedToOrthogonal_injective
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hγ : J.IsEntrywiseConjugation γ) :
    Function.Injective (specialFixedToOrthogonal J hJ hγ) := by
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  ext i j
  exact congrArg (fun z : (splitOrthogonalForm (F J)).specialSubgroup =>
    (z.val.val i j : E)) he

/-- Embed the projective fixed subgroup in the actual fixed-field ternary
orthogonal matrix group. The scalar-kernel comparison is part of the map. -/
public noncomputable def projectiveFixedToOrthogonal
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hγ : J.IsEntrywiseConjugation γ) :
    γ.fixedSubgroup →*
      (splitOrthogonalForm (FixedBy.subfield E J.conj)).specialSubgroup :=
  (specialFixedToOrthogonal J hJ hγ).comp
    (projectiveFixedEquivSpecial J hγ).toMonoidHom

public theorem projectiveFixedToOrthogonal_injective
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hγ : J.IsEntrywiseConjugation γ) :
    Function.Injective (projectiveFixedToOrthogonal J hJ hγ) :=
  (specialFixedToOrthogonal_injective J hJ hγ).comp
    (projectiveFixedEquivSpecial J hγ).injective

/-- Lagrange's theorem for the concrete orthogonal embedding. -/
public theorem card_projectiveFixed_dvd_orthogonal
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hγ : J.IsEntrywiseConjugation γ) :
    Nat.card γ.fixedSubgroup ∣
      Nat.card (splitOrthogonalForm (FixedBy.subfield E J.conj)).specialSubgroup :=
  Subgroup.card_dvd_of_injective (projectiveFixedToOrthogonal J hJ hγ)
    (projectiveFixedToOrthogonal_injective J hJ hγ)


end BenderSuzuki.MatrixGroups.HermitianForm.OddPrimeSylow
