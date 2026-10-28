module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverBinary
public import Theory.SpecificGroups.SU3.EvenSemilinear.SpecialCoverage
public import Theory.FieldTheory.ScalarTwistedFixedPoints
public import Theory.SpecificGroups.SU3.FixedFieldTwo

/-!
# Diagonal marking on the full binary unitary cover

A cubic coefficient automorphism fixes the norm-one cube roots. For the
same cube-one semilinear actor, its twisted matrix cube is a fixed unitary
scalar. Finite-field norm surjectivity and the injective square map in
characteristic two lift this scalar inside the norm-one subgroup. Rescaling
therefore gives a unitary matrix cocycle. Cubic matrix descent produces a
basis; its Gram matrix descends to the fixed field, where Hermitian
normalization makes that basis orthonormal.

The scalar cubic and an independent diagonal cubic in this basis are fixed
by the original automorphism on SU₃. The disjoint outside element of order
three would increase their rank to three, contradicting SQTK. Thus every
binary unitary cover actor has the required actual unitary matrix marking,
including actors initially given with both diagonal and field factors.
The solvable q = 2 endpoint is excluded using inherited quasisimplicity.

Combined with CoverBinary, this supplies the diagonal marking for every
remaining signed cover. The literal star quotient, residual product and
complement remain unchanged. OddRankSource applies the refinement to the
original Cartan extension. Exact Singer centralizers and conjugacy of all
outside subgroups of order three remain source obligations.

Source: Aschbacher–Smith A.3.18, printed pp.51–53. Cubic matrix descent uses
the attributed GLS3 4.9.1(d) development in StandardCubicFixedNine.Descent;
finite Hermitian normalization uses the proved Huppert II.10.4 theorem.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
open scoped MatrixGroups
open HermitianForm HermitianForm.BorelTorus.SemilinearActors
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverUnitaryBinary
section Models
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem unit_sq_injective : Function.Injective (fun x : Fˣ => x^2) := by
  intro x y h
  apply Units.ext
  exact CharTwo.sq_injective (congrArg Units.val h)

/-- Norm lifting within the actual norm-one scalars, rather than all field units. -/
theorem exists_unitary_cubic_norm (J : HermitianForm 3 F)
    (σ : F ≃+* F) (hs : orderOf σ = 3)
    (c : Fˣ) (hc : Units.map σ.toMonoidHom c = c)
    (hcn : Units.map J.conj.toMonoidHom c * c = 1) :
    ∃ t : Fˣ, Units.map J.conj.toMonoidHom t * t = 1 ∧
      t * Units.map σ.toMonoidHom t * Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t) = c := by
  obtain ⟨s,hsn⟩ := Matrix.PSL3.StandardCubicFixedNine.Descent.exists_cubic_norm σ hs c hc
  let S := Units.map σ.toMonoidHom
  let C := Units.map J.conj.toMonoidHom
  have hcomm (x : Fˣ) : S (C x) = C (S x) := by
    apply Units.ext
    exact field_conj_commute J σ x
  have hC (x : Fˣ) : C (C x) = x := by
    apply Units.ext
    exact J.conj_involutive x
  obtain ⟨t,ht⟩ := (Finite.surjective_of_injective unit_sq_injective) (s / C s)
  change t^2 = s / C s at ht
  change s * S s * S (S s) = c at hsn
  have hn : C t * t = 1 := by
    apply unit_sq_injective
    change (C t * t)^2 = 1^2
    rw [mul_pow,←map_pow,ht,map_div,hC]
    simp [div_eq_mul_inv,mul_assoc]
  refine ⟨t,hn,unit_sq_injective ?_⟩
  change (t * S t * S (S t))^2 = c^2
  rw [mul_pow,mul_pow,←map_pow,←map_pow,←map_pow,ht]
  change s / C s * S (s / C s) * S (S (s / C s)) = c^2
  simp only [map_div,hcomm]
  have he : s / C s * (S s / C (S s)) * (S (S s) / C (S (S s))) =
      (s * S s * S (S s)) / C (s * S s * S (S s)) := by
    simp only [map_mul,div_mul_div_comm]
  rw [he,hsn]
  have hc' : C c = c⁻¹ := (mul_eq_one_iff_eq_inv).mp hcn
  rw [hc',div_inv_eq_mul,pow_two]

omit [Finite F] [CharP F 2] in
private theorem adjoint_mul (J : HermitianForm 3 F) (A B : Matrix (Fin 3) (Fin 3) F) :
    J.conjTranspose (A*B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A*B)).transpose = _
  rw [map_mul,transpose_mul]
  rfl

private def gram (J : HermitianForm 3 F) (P : GL (Fin 3) F) : HermitianForm 3 F where
  conj := J.conj
  conj_involutive := J.conj_involutive
  form := J.conjTranspose P.val*J.form*P.val
  form_hermitian := by
    let : _root_.Star F := ⟨J.conj⟩
    let : InvolutiveStar F := ⟨J.conj_involutive⟩
    let : StarMul F := ⟨fun a b => by change J.conj (a*b)=J.conj b*J.conj a; rw [map_mul,mul_comm]⟩
    let : StarRing F := ⟨fun a b => by change J.conj (a+b)=J.conj a+J.conj b; rw [map_add]⟩
    have h : (J.conjTranspose P.val*J.form*P.val).IsHermitian :=
      Matrix.isHermitian_conjTranspose_mul_mul P.val (Matrix.IsHermitian.ext J.form_hermitian)
    exact h.apply
  form_nondegenerate := by
    have ha : (J.conjTranspose P.val).det=J.conj P.val.det := by
      change ((P.val.map J.conj).transpose).det=_
      rw [Matrix.det_transpose]
      exact (J.conj.map_det P.val).symm
    rw [Matrix.det_mul,Matrix.det_mul,ha]
    exact mul_ne_zero (mul_ne_zero (by simpa using P.det_ne_zero) J.form_nondegenerate) P.det_ne_zero


omit [CharP F 2] in
/-- A unitary cubic cocycle has an orthonormal descent basis. -/
theorem unitary_cocycle_frame (J : HermitianForm 3 F) (σ : F ≃+* F)
    (hs : orderOf σ = 3) (hJ : J.form.map σ = J.form)
    (hnontriv : ∃ z : F, σ z = z ∧ J.conj z ≠ z)
    (A : GL (Fin 3) F) (hAu : A ∈ J.unitarySubgroup)
    (hA : A * GeneralLinearGroup.map σ.toRingHom A *
      GeneralLinearGroup.map σ.toRingHom (GeneralLinearGroup.map σ.toRingHom A) = 1) :
    ∃ P : GL (Fin 3) F, A * GeneralLinearGroup.map σ.toRingHom P = P ∧
      J.conjTranspose P.val * J.form * P.val = 1 := by
  classical
  obtain ⟨P,hP⟩ := Matrix.PSL3.StandardCubicFixedNine.Descent.linear_cocycle_descent σ hs A hA
  let E := FixedBy.subfield F σ
  let τ : E ≃+* E := {
    toFun := fun x => ⟨J.conj x.val, by
      change σ (J.conj x.val) = J.conj x.val
      rw [field_conj_commute J σ x.val]
      exact congrArg J.conj x.property⟩
    invFun := fun x => ⟨J.conj x.val, by
      change σ (J.conj x.val) = J.conj x.val
      rw [field_conj_commute J σ x.val]
      exact congrArg J.conj x.property⟩
    left_inv := fun x => Subtype.ext (J.conj_involutive x.val)
    right_inv := fun x => Subtype.ext (J.conj_involutive x.val)
    map_mul' := fun x y => Subtype.ext (map_mul J.conj x.val y.val)
    map_add' := fun x y => Subtype.ext (map_add J.conj x.val y.val) }
  have ht : Function.Involutive τ := fun x => Subtype.ext (J.conj_involutive x.val)
  have hne : τ ≠ RingEquiv.refl E := by
    intro he
    obtain ⟨z,hz,hnz⟩ := hnontriv
    exact hnz (congrArg Subtype.val (DFunLike.congr_fun he ⟨z,hz⟩))
  let K := gram J P
  have hmap (M : Matrix (Fin 3) (Fin 3) F) :
      (J.conjTranspose M).map σ = J.conjTranspose (M.map σ) := by
    ext i j
    exact field_conj_commute J σ (M j i)
  have hfix : K.form.map σ = K.form := by
    change (J.conjTranspose P.val * J.form * P.val).map σ = _
    rw [Matrix.map_mul,Matrix.map_mul,hmap,hJ]
    have hpres := (J.mem_unitarySubgroup_iff A).mp hAu
    have hp : A.val * P.val.map σ = P.val := congrArg Units.val hP
    calc
      J.conjTranspose (P.val.map σ) * J.form * P.val.map σ =
          J.conjTranspose (P.val.map σ) * (J.conjTranspose A.val * J.form * A.val) * P.val.map σ := by rw [hpres]
      _ = J.conjTranspose (A.val * P.val.map σ) * J.form * (A.val * P.val.map σ) := by
        rw [adjoint_mul]
        simp only [Matrix.mul_assoc]
      _ = K.form := by rw [hp]; rfl
  let B : Matrix (Fin 3) (Fin 3) E := fun i j => ⟨K.form i j, show σ (K.form i j) = K.form i j from
    congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i j) hfix⟩
  have hB : B.map E.subtype = K.form := rfl
  let J₀ : HermitianForm 3 E := {
    conj := τ
    conj_involutive := ht
    form := B
    form_hermitian := fun i j => Subtype.ext (K.form_hermitian i j)
    form_nondegenerate := by
      intro he
      apply K.form_nondegenerate
      rw [←hB]
      change (E.subtype.mapMatrix B).det = 0
      rw [←RingHom.map_det,he,map_zero] }
  let q := Nat.card (FixedBy.subfield E τ)
  have hcard : Nat.card E = q^2 := (FiniteField.card_involution_fixed_sq τ ht hne).symm
  have hfixed : Nat.card {x : E // J₀.conj x=x} = q := rfl
  obtain ⟨Q,hQ⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis 3 J₀ q hcard hfixed
  let Q' := GeneralLinearGroup.map E.subtype Q
  have hQfix : GeneralLinearGroup.map σ.toRingHom Q' = Q' := by
    apply Units.ext
    ext i j
    exact (Q.val i j).property
  have hQP : J.conjTranspose Q'.val * K.form * Q'.val = 1 := by
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M.map E.subtype) hQ
    simp only [Matrix.map_mul,Matrix.map_one E.subtype (map_zero E.subtype) (map_one E.subtype)] at hh
    exact hh
  refine ⟨P*Q',?_,?_⟩
  · rw [map_mul,hQfix,←mul_assoc,hP]
  · change J.conjTranspose (P.val*Q'.val) * J.form * (P.val*Q'.val) = 1
    rw [adjoint_mul]
    calc
      J.conjTranspose Q'.val * J.conjTranspose P.val * J.form * (P.val * Q'.val) =
          J.conjTranspose Q'.val * K.form * Q'.val := by
        change _ = J.conjTranspose Q'.val * (J.conjTranspose P.val * J.form * P.val) * Q'.val
        simp only [Matrix.mul_assoc]
      _ = 1 := hQP

omit [CharP F 2] in
private theorem field_unitary (J : HermitianForm 3 F) (σ : F ≃+* F)
    (hJ : J.form.map σ = J.form) (u : GL (Fin 3) F) (hu : u ∈ J.unitarySubgroup) :
    GeneralLinearGroup.map σ.toRingHom u ∈ J.unitarySubgroup := by
  have hadj : J.conjTranspose (u.val.map σ) = (J.conjTranspose u.val).map σ := by
    ext i j
    exact (field_conj_commute J σ (u.val j i)).symm
  rw [J.mem_unitarySubgroup_iff]
  change J.conjTranspose (u.val.map σ) * J.form * u.val.map σ = J.form
  rw [hadj,←hJ,←Matrix.map_mul,←Matrix.map_mul]
  exact congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M.map σ)
    ((J.mem_unitarySubgroup_iff u).mp hu)

omit [Finite F] [CharP F 2] in
private theorem scalar_unitary (J : HermitianForm 3 F) (c : Fˣ) :
    GeneralLinearGroup.scalar (Fin 3) c ∈ J.unitarySubgroup ↔
      Units.map J.conj.toMonoidHom c * c = 1 := by
  have hadj : J.conjTranspose (Matrix.scalar (Fin 3) (c : F)) =
      Matrix.scalar (Fin 3) (J.conj (c : F)) := by
    ext i j
    by_cases h : i=j
    · subst j; simp [HermitianForm.conjTranspose,Matrix.scalar_apply]
    · simp [HermitianForm.conjTranspose,Matrix.scalar_apply,h,Ne.symm h]
  rw [J.mem_unitarySubgroup_iff]
  change J.conjTranspose (Matrix.scalar (Fin 3) (c : F)) * J.form *
    Matrix.scalar (Fin 3) (c : F) = J.form ↔ _
  rw [hadj]
  constructor
  · intro h
    obtain ⟨j,hj⟩ : ∃ j, J.form 0 j ≠ 0 := by
      by_contra! h
      exact J.form_nondegenerate (Matrix.det_eq_zero_of_row_eq_zero 0 h)
    have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 j) h
    simp only [Matrix.scalar_apply,Matrix.mul_diagonal,Matrix.diagonal_mul] at he
    apply Units.ext
    change J.conj (c : F) * (c : F) = 1
    apply mul_right_cancel₀ hj
    calc (J.conj (c : F) * (c : F)) * J.form 0 j =
        J.conj (c : F) * J.form 0 j * (c : F) := by ring
         _ = 1 * J.form 0 j := by simpa using he
  · intro h
    have hh : J.conj (c : F) * (c : F) = 1 := congrArg Units.val h
    ext i j
    simp only [Matrix.scalar_apply,Matrix.mul_diagonal,Matrix.diagonal_mul]
    calc J.conj (c : F) * J.form i j * (c : F) =
        (J.conj (c : F) * (c : F)) * J.form i j := by ring
         _ = J.form i j := by rw [hh,one_mul]

omit [Finite F] [CharP F 2] in
private theorem scalar_injective :
    Function.Injective (GeneralLinearGroup.scalar (Fin 3) : Fˣ →* _) := by
  intro a b h
  apply Units.ext
  simpa using congrArg (fun g : GL (Fin 3) F => g.val 0 0) h

omit [Finite F] in
private theorem scalar_twisted_cube (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hne : ∃ z : F, J.conj z ≠ z)
    (α : MulAut J.specialSubgroup) (hα : α ^ 3 = 1)
    (σ : F ≃+* F) (hs : σ ^ 3 = 1) (u : J.unitarySubgroup)
    (hu : ∀ x : J.specialSubgroup,
      (α x).val = u.val * GeneralLinearGroup.map σ.toRingHom x.val * u.val⁻¹) :
    ∃ c : Fˣ, u.val * GeneralLinearGroup.map σ.toRingHom u.val *
      GeneralLinearGroup.map σ.toRingHom (GeneralLinearGroup.map σ.toRingHom u.val) =
        GeneralLinearGroup.scalar (Fin 3) c ∧ Units.map σ.toMonoidHom c = c := by
  let S : GL (Fin 3) F →* GL (Fin 3) F := GeneralLinearGroup.map σ.toRingHom
  let N := u.val * S u.val * S (S u.val)
  have hS (m : GL (Fin 3) F) : S (S (S m)) = m := by
    apply Units.ext
    ext i j
    exact DFunLike.congr_fun hs (m.val i j)
  have hN : N ∈ center (GL (Fin 3) F) := by
    apply J.projective_centralizer_scalar hJ hne
    intro x
    obtain ⟨y,rfl⟩ := J.specialToProjective_surjective x
    have hh := congrArg (fun b : MulAut J.specialSubgroup => (b y).val) hα
    change (α (α (α y))).val = y.val at hh
    rw [hu,hu,hu] at hh
    change u.val * S (u.val * S (u.val * S y.val * u.val⁻¹) * u.val⁻¹) * u.val⁻¹ = y.val at hh
    simp only [map_mul,map_inv,hS] at hh
    have he : N * y.val * N⁻¹ = y.val := by
      simpa only [N,_root_.mul_inv_rev,mul_assoc] using hh
    have he' := congrArg ProjGenLinGroup.mk he
    apply (mul_inv_eq_iff_eq_mul).mp
    simpa only [map_mul,map_inv,J.specialToProjective_apply_val] using he'
  rw [GeneralLinearGroup.center_eq_range_scalar] at hN
  obtain ⟨c,hc⟩ := hN
  refine ⟨c,hc.symm,scalar_injective ?_⟩
  change GeneralLinearGroup.scalar (Fin 3) (Units.map σ.toRingHom.toMonoidHom c) = _
  have hmapc := GeneralLinearGroup.map_scalar (n := Fin 3) σ.toRingHom c
  change S (GeneralLinearGroup.scalar (Fin 3) c) =
    GeneralLinearGroup.scalar (Fin 3) (Units.map σ.toRingHom.toMonoidHom c) at hmapc
  rw [←hmapc,hc]
  change S N = N
  simp only [N,map_mul,hS]
  have he := congrArg (fun x => u.val⁻¹ * x * u.val) hc
  rw [←GeneralLinearGroup.scalar_commute c u.val⁻¹,mul_assoc,inv_mul_cancel,mul_one] at he
  simpa only [N,mul_assoc,inv_mul_cancel_left,hc] using he.symm

/-- Descent retains the original cubic actor and gives its matrix formula
in an orthonormal basis over the fixed field. -/
theorem semilinear_frame (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (α : MulAut J.specialSubgroup) (hα : α ^ 3 = 1)
    (σ : F ≃+* F) (hs : orderOf σ = 3)
    (hnontriv : ∃ z : F, σ z = z ∧ J.conj z ≠ z)
    (hf : J.HasSpecialUnitarySemilinearForm α σ) :
    ∃ P : GL (Fin 3) F, J.conjTranspose P.val * J.form * P.val = 1 ∧
      ∀ x : J.specialSubgroup,
        P⁻¹ * (α x).val * P = GeneralLinearGroup.map σ.toRingHom (P⁻¹ * x.val * P) := by
  obtain ⟨u,hu⟩ := hf
  have hmap : J.form.map σ = J.form := by
    rw [hJ]; ext i j; fin_cases i <;> fin_cases j <;> simp
  obtain ⟨c,hc,hfix⟩ := scalar_twisted_cube J hJ
    (by obtain ⟨z,_,hz⟩ := hnontriv; exact ⟨z,hz⟩) α hα σ
    (hs ▸ pow_orderOf_eq_one σ) u hu
  have hcu : GeneralLinearGroup.scalar (Fin 3) c ∈ J.unitarySubgroup := hc ▸
    J.unitarySubgroup.mul_mem (J.unitarySubgroup.mul_mem u.property
      (field_unitary J σ hmap u.val u.property))
      (field_unitary J σ hmap _ (field_unitary J σ hmap u.val u.property))
  have hcn := (scalar_unitary J c).mp hcu
  obtain ⟨t,htn,ht⟩ := exists_unitary_cubic_norm J σ hs c⁻¹
    (by rw [map_inv,hfix]) (by rw [map_inv]; simpa only [_root_.mul_inv_rev,inv_one,mul_comm] using congrArg (fun x : Fˣ => x⁻¹) hcn)
  let A := GeneralLinearGroup.scalar (Fin 3) t * u.val
  have hAu : A ∈ J.unitarySubgroup :=
    J.unitarySubgroup.mul_mem ((scalar_unitary J t).mpr htn) u.property
  have hA : A * GeneralLinearGroup.map σ.toRingHom A *
      GeneralLinearGroup.map σ.toRingHom (GeneralLinearGroup.map σ.toRingHom A) = 1 := by
    simp only [A,map_mul,GeneralLinearGroup.map_scalar]
    have hmul (a b : Fˣ) (m n : GL (Fin 3) F) :
        (GeneralLinearGroup.scalar (Fin 3) a * m) * (GeneralLinearGroup.scalar (Fin 3) b * n) =
          GeneralLinearGroup.scalar (Fin 3) (a*b) * (m*n) := by
      rw [map_mul]
      exact (show Commute m (GeneralLinearGroup.scalar (Fin 3) b) from
        (GeneralLinearGroup.scalar_commute b m).symm).mul_mul_mul_comm _ _
    rw [hmul,hmul]
    change GeneralLinearGroup.scalar (Fin 3)
      (t * Units.map σ.toMonoidHom t * Units.map σ.toMonoidHom (Units.map σ.toMonoidHom t)) *
      (u.val * GeneralLinearGroup.map σ.toRingHom u.val *
        GeneralLinearGroup.map σ.toRingHom (GeneralLinearGroup.map σ.toRingHom u.val)) = 1
    rw [ht,hc,←map_mul,inv_mul_cancel,map_one]
  obtain ⟨P,hP,hgram⟩ := unitary_cocycle_frame J σ hs hmap hnontriv A hAu hA
  have hform (x : J.specialSubgroup) :
      (α x).val = A * GeneralLinearGroup.map σ.toRingHom x.val * A⁻¹ := by
    rw [hu]
    dsimp only [A]
    rw [_root_.mul_inv_rev]
    have hct := GeneralLinearGroup.scalar_commute t
      (u.val * GeneralLinearGroup.map σ.toRingHom x.val * u.val⁻¹)
    calc u.val * GeneralLinearGroup.map σ.toRingHom x.val * u.val⁻¹ =
          GeneralLinearGroup.scalar (Fin 3) t *
          (u.val * GeneralLinearGroup.map σ.toRingHom x.val * u.val⁻¹) *
          (GeneralLinearGroup.scalar (Fin 3) t)⁻¹ := by rw [hct,mul_inv_cancel_right]
         _ = _ := by group
  refine ⟨P,hgram,fun x => ?_⟩
  have he : A = P * (GeneralLinearGroup.map σ.toRingHom P)⁻¹ :=
    (eq_mul_inv_iff_mul_eq).mpr hP
  rw [hform,he,map_mul,map_mul,map_inv]
  group


private theorem fixes_cubic_scalar {F : Type*} [Field F] (σ : F ≃+* F) (hs : σ ^ 3 = 1)
    (u : F) (hu : u ^ 3 = 1) (hne : u ≠ 1) : σ u = u := by
  have hp : IsPrimitiveRoot u 3 := IsPrimitiveRoot.iff_orderOf.mpr
    (orderOf_eq_prime hu hne)
  obtain ⟨k, hk, he⟩ := hp.eq_pow_of_pow_eq_one (show σ u ^ 3 = 1 by rw [← map_pow, hu, map_one])
  have hne' : σ u ≠ 1 := by simpa using hne
  have hs' : σ (σ (σ u)) = u := DFunLike.congr_fun hs u
  interval_cases k
  · exact (hne' (by simpa using he.symm)).elim
  · simpa using he.symm
  · have h2 : σ u = u ^ 2 := he.symm
    rw [h2, map_pow, h2, map_pow, map_pow, h2] at hs'
    have h8 : ((u ^ 2) ^ 2) ^ 2 = u ^ 2 := by
      calc ((u ^ 2) ^ 2) ^ 2 = u ^ 3 * u ^ 3 * u ^ 2 := by ring
           _ = u ^ 2 := by rw [hu]; simp
    rw [h8] at hs'
    have hu0 : u ≠ 0 := by intro he; simp [he] at hu
    have h1 : u = 1 := by
      apply mul_right_cancel₀ hu0
      simpa only [pow_two, one_mul] using hs'
    exact (hne h1).elim

omit [Finite F] [CharP F 2] in
private theorem diagonal_unitary (u : F) (hu : u ^ 3 = 1)
    (J : HermitianForm 3 F) (hJ : J.form = 1) (hnorm : J.conj u * u = 1) :
    SpecialLinearGroup.toGL (Theory.SpecificGroups.SignedThreeCubicRank.diagonal u hu) ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  refine ⟨?_, SpecialLinearGroup.coeToGL_det _⟩
  rw [hJ, mul_one]
  change J.conjTranspose (Theory.SpecificGroups.SignedThreeCubicRank.diagonal u hu).val * (Theory.SpecificGroups.SignedThreeCubicRank.diagonal u hu).val = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Theory.SpecificGroups.SignedThreeCubicRank.diagonal, HermitianForm.conjTranspose, Matrix.mul_apply, Fin.sum_univ_three, hnorm]
  calc J.conj u ^ 2 * u ^ 2 = (J.conj u * u) ^ 2 := by ring
       _ = 1 := by rw [hnorm]; simp


/-- The original cubic semilinear actor fixes two independent cubics
in the full special-unitary cover. -/
theorem unitary_field_fixed_rank (J : HermitianForm 3 F)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : Odd n) (hF : Nat.card F = (2^n)^2)
    (hc : ∀ x, J.conj x = x^(2^n))
    (α : MulAut J.specialSubgroup) (hα : α^3=1)
    (σ : F ≃+* F) (hs : orderOf σ = 3)
    (hf : J.HasSpecialUnitarySemilinearForm α σ) :
    2 ≤ primeRank 3 α.fixedSubgroup := by
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := EvenInner.normOne J) 3 (by
    rw [EvenInner.normOne_card J hF hc]
    apply Nat.dvd_of_mod_eq_zero
    have hh : 2^n % 3 = 2 := by
      rw [Nat.BinaryTorusParity.two_pow_mod_three,if_neg]
      have hh := Nat.odd_iff.mp hn
      omega
    omega)
  have hu3 : (u.val : F)^3=1 := congrArg (fun t : EvenInner.normOne J => (t.val : F))
    (hu ▸ pow_orderOf_eq_one u)
  have hu1 : (u.val : F) ≠ 1 := by
    intro he
    have he' : u=1 := Subtype.ext (Units.ext he)
    rw [he',orderOf_one] at hu
    omega
  have hnorm : J.conj (u.val : F) * (u.val : F) = 1 := by
    rw [show J.conj (u.val : F) = (u.val : F)⁻¹ from u.property]
    exact inv_mul_cancel₀ (Units.ne_zero _)
  have hfix := fixes_cubic_scalar σ (hs ▸ pow_orderOf_eq_one σ) (u.val : F) hu3 hu1
  have hconj : J.conj (u.val : F) ≠ (u.val : F) := by
    intro he
    rw [he] at hnorm
    apply hu1
    calc (u.val : F) = ((u.val : F) * (u.val : F)) * (u.val : F) := by rw [hnorm,one_mul]
         _ = 1 := by simpa only [pow_succ,pow_zero,one_mul] using hu3
  obtain ⟨P,hP,hframe⟩ := semilinear_frame J hJ α hα σ hs ⟨u.val,hfix,hconj⟩ hf
  let D := SpecialLinearGroup.toGL (Theory.SpecificGroups.SignedThreeCubicRank.diagonal (u.val : F) hu3)
  let Z := SpecialLinearGroup.toGL (Theory.SpecificGroups.SignedThreeCubicRank.scalar (u.val : F) hu3)
  have hD : D ∈ (IdentityGram.identityGram J).specialSubgroup :=
    diagonal_unitary (u.val : F) hu3 _ rfl hnorm
  have hZ : Z ∈ (IdentityGram.identityGram J).specialSubgroup := by
    have hZe : Z = GeneralLinearGroup.scalar (Fin 3) u.val := by apply Units.ext; rfl
    rw [hZe]
    apply (UniversalCover.scalar_mem_special_iff _ _).mpr
    exact ⟨hnorm,congrArg (fun t : EvenInner.normOne J => t.val) (hu ▸ pow_orderOf_eq_one u)⟩
  have hDfix : GeneralLinearGroup.map σ.toRingHom D = D := by
    apply Units.ext
    ext i j
    change σ ((Theory.SpecificGroups.SignedThreeCubicRank.diagonal (u.val : F) hu3).val i j) =
      (Theory.SpecificGroups.SignedThreeCubicRank.diagonal (u.val : F) hu3).val i j
    fin_cases i <;> fin_cases j <;>
      simp [Theory.SpecificGroups.SignedThreeCubicRank.diagonal,hfix]
  have hZfix : GeneralLinearGroup.map σ.toRingHom Z = Z := by
    apply Units.ext
    ext i j
    change σ ((Theory.SpecificGroups.SignedThreeCubicRank.scalar (u.val : F) hu3).val i j) =
      (Theory.SpecificGroups.SignedThreeCubicRank.scalar (u.val : F) hu3).val i j
    fin_cases i <;> fin_cases j <;>
      simp [Theory.SpecificGroups.SignedThreeCubicRank.scalar,hfix]
  let e := IdentityGram.specialEquiv J P hP
  have heval (x : J.specialSubgroup) : (e x).val = P⁻¹ * x.val * P :=
    IdentityGram.specialEquiv_apply J P hP x
  have heval' (x : (IdentityGram.identityGram J).specialSubgroup) :
      (e.symm x).val = P * x.val * P⁻¹ := IdentityGram.specialEquiv_symm_apply J P hP x
  have fixed (v : (IdentityGram.identityGram J).specialSubgroup)
      (hv : GeneralLinearGroup.map σ.toRingHom v.val = v.val) :
      e.symm v ∈ α.fixedSubgroup := by
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    apply e.injective
    rw [e.apply_symm_apply]
    apply Subtype.ext
    rw [heval]
    rw [hframe]
    have hv' : P⁻¹ * (e.symm v).val * P = v.val := by
      rw [heval']
      group
    rw [hv',hv]
  let f : α.fixedSubgroup →* GL (Fin 3) F :=
    (MulAut.conj P⁻¹).toMonoidHom.comp (J.specialSubgroup.subtype.comp α.fixedSubgroup.subtype)
  apply Theory.SpecificGroups.SignedThreeCubicRank.special_rank (u.val : F) hu3 hu1 f
    ((MulAut.conj P⁻¹).injective.comp (Subtype.val_injective.comp Subtype.val_injective))
    ⟨e.symm ⟨D,hD⟩,fixed ⟨D,hD⟩ hDfix⟩ ⟨e.symm ⟨Z,hZ⟩,fixed ⟨Z,hZ⟩ hZfix⟩
  · simp only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,Subgroup.coe_subtype,
      inv_inv]
    rw [heval']
    change P⁻¹ * (P * D * P⁻¹) * P = D
    group
  · simp only [f,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,Subgroup.coe_subtype,
      inv_inv]
    rw [heval']
    change P⁻¹ * (P * Z * P⁻¹) * P = Z
    group


end Models

private theorem fixed_rank_lt_two {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) (x : G) (hx : orderOf x = 3) (hxK : x ∉ K)
    (hr : primeRank 3 G ≤ 2) (C : Subgroup K)
    (hC : ∀ c : C, Commute (c.val : G) x) : primeRank 3 C < 2 := by
  by_contra hn
  obtain ⟨E,hE,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := C) (p := 3)
  let := hE
  obtain ⟨B,hB⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3 (n := 2)
    (by rw [hcard]; exact pow_dvd_pow 3 (by omega))
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.of_injective B.subtype B.subtype_injective
  let f : E →* G := K.subtype.comp (C.subtype.comp E.subtype)
  have hf : Function.Injective f := K.subtype_injective.comp
    (C.subtype_injective.comp E.subtype_injective)
  let D := B.map f
  let : IsElementaryAbelian 3 D := IsElementaryAbelian.map f
  have hdK : D ≤ K := by rintro _ ⟨b,_,rfl⟩; exact b.val.val.property
  have hfix : D ≤ centralizer ({x} : Set G) := by
    rintro _ ⟨b,_,rfl⟩
    exact mem_centralizer_singleton_iff.mpr (hC b.val)
  have hc : Nat.card D = 3^2 := by rw [card_map_of_injective hf,hB]
  have hh := IsElementaryAbelian.primeRank_ge_of_fixed_join D x hx
    (fun h => hxK (hdK h)) hfix hc
  omega


/-- An actual outside cubic on a binary SU₃ cover is induced by a unitary
matrix. Descent excludes its field component using the same actor. -/
theorem unitary_binary {G : Type*} [Group G] [Finite G]
    {K : Subgroup G} [K.Normal] [IsQuasisimple K] (hr : primeRank 3 G ≤ 2)
    {n : ℕ} (hn : 0 < n) (hodd : Odd n)
    (hm : CFSG.Quasithin.Chapter1.Section02.LocalModels.IsSU K 3 (2^n))
    (a : G) (ha : orderOf a=3) (haK : a ∉ K) :
    IsUnitaryDiagonal K (2^n) (MulAut.conjNormal a) := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2) (by
    simpa only [←Nat.card_eq_fintype_card,pow_mul] using hF)
  let : IsQuasisimple J.specialSubgroup := IsQuasisimple.of_mulEquiv e
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hF hconj
  have hn2 : 2 ≤ n := by
    by_contra hh
    have hn1 : n=1 := by omega
    have hc : Nat.card F=2^2 := by simpa only [hn1,pow_one] using hF
    have hj : ∀ x, J.conj x=x^2 := by simpa only [hn1,pow_one] using hconj
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Group.IsPerfect.ofSurjective (f := J.specialToProjective) J.specialToProjective_surjective
    let : Nontrivial (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [FixedFieldTwo.card_projective J hc hj]; decide)
    exact Group.IsPerfect.not_isSolvable (ProjectiveSpecialUnitaryMatrixGroup J)
      (FixedFieldTwo.projective_isSolvable J hc hj)
  obtain ⟨C,hC⟩ := OddPrimeSylow.NormalizedOuter.FormTransport.exists_standard_basis J (2^n) hF hfixed
  let J₀ := OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  let e' : K ≃* J₀.specialSubgroup := e.trans
    (OddPrimeSylow.NormalizedOuter.FormTransport.specialEquiv J C hC)
  let α : MulAut K := MulAut.conjNormal a
  let β := MulAut.congr e' α
  have hα : α^3=1 := by
    change (MulAut.conjNormal a : MulAut K)^3=1
    rw [←map_pow,←ha,pow_orderOf_eq_one,map_one]
  have hβ : β^3=1 := by rw [←map_pow,hα,map_one]
  obtain ⟨σ,hf⟩ := EvenSemilinear.special_semilinear_coverage J₀ rfl hn2 hF hconj β
  have hs : σ^3=1 := by
    apply J₀.semilinear_identity_field_eq_one n hn2 rfl hF hfixed
    obtain ⟨v,hv⟩ := hf.pow J₀ rfl 3
    rw [hβ] at hv
    refine ⟨v,?_⟩
    intro b
    obtain ⟨y,rfl⟩ := J₀.specialToProjective_surjective b
    have hh := congrArg ProjGenLinGroup.mk (hv y)
    simpa only [MulAut.one_apply,J₀.specialToProjective_apply_val,map_mul,map_inv,
      ProjGenLinGroup.map_mk] using hh
  have hs1 : σ=1 := by
    by_contra hne
    have hge := unitary_field_fixed_rank J₀ rfl hodd hF hconj β hβ σ
      (orderOf_eq_prime hs hne) hf
    have hbound : primeRank 3 α.fixedSubgroup < 2 := by
      apply fixed_rank_lt_two K a ha haK hr
      intro c
      have he := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp c.property)
      exact ((mul_inv_eq_iff_eq_mul).mp he).symm
    have he := primeRank_congr 3 (MulAut.fixedSubgroupCongr e' α)
    change primeRank 3 α.fixedSubgroup = primeRank 3 β.fixedSubgroup at he
    omega
  obtain ⟨v,hv⟩ := hf
  refine ⟨F,inferInstance,inferInstance,J₀,hF,hconj,e',v,?_⟩
  intro l
  have hh := hv (e' l)
  change (e' (α (e'.symm (e' l)))).val = _ at hh
  rw [e'.symm_apply_apply] at hh
  simpa only [hs1,show (1 : F ≃+* F).toRingHom = RingHom.id F from rfl,
    GeneralLinearGroup.map_id,MonoidHom.id_apply] using hh

variable {G : Type*} [Group G] [Finite G]
open CFSG.Quasithin.Chapter1.Section02.LocalModels

/-- Every remaining central cover has the complete signed diagonal marking;
its Singer centralizer and outside-subgroup fusion remain to be established. -/
structure MarkedStarCover (K : Subgroup G) (a : G) : Prop extends
    CoverStructure.StarCover K a where
  marking : ∃ (unitary : Bool) (q : ℕ), CoverParameter unitary q ∧
    SignedCongruence unitary q ∧ IsSLSign (starComponent 3 K) unitary 3 q ∧
    ∃ α : MulAut (starComponent 3 K),
      (∀ l : starComponent 3 K, (α l).val = starMap 3 G a * l.val * (starMap 3 G a)⁻¹) ∧
      α ∉ MulAut.innerSubgroup (starComponent 3 K) ∧
      IsDiagonalSign (starComponent 3 K) unitary q α

/-- The exact source cover, including its original actor, now has a diagonal
marking for both signs and every permitted parameter. -/
theorem marked_star_cover {K : Subgroup G} [K.Normal]
    (hb : primeRank 3 G ≤ 2) (a : G) (hs : CoverStructure.StarCover K a) :
    MarkedStarCover K a := by
  let : (starComponent 3 K).Normal :=
    (inferInstance : K.Normal).map _ (QuotientGroup.mk'_surjective _)
  let := hs.quasisimple
  obtain ⟨_,u,q,hq,hmod,hm,α,ha,ho,hdiag⟩ := CoverBinary.marked_star_cover hb a hs
  refine ⟨hs,u,q,hq,hmod,hm,α,ha,ho,?_⟩
  rcases hdiag with ⟨rfl,n,hn,rfl⟩ | hd
  · have he : α = (MulAut.conjNormal (starMap 3 G a) : MulAut (starComponent 3 K)) := by
      apply MulEquiv.ext
      intro l
      exact Subtype.ext (ha l)
    have hodd : Odd n := by
      rw [Nat.odd_iff]
      change 2^n % 3 = 2 at hmod
      rw [Nat.BinaryTorusParity.two_pow_mod_three] at hmod
      split_ifs at hmod with h
      · omega
      · omega
    have hstar : primeRank 3 (Star 3 G) ≤ 2 :=
      (primeRank_quotient_le_of_coprime 3 (pPrimeCore 3 G) pPrimeCore_coprime_card).trans hb
    change IsUnitaryDiagonal (starComponent 3 K) (2^n) α
    rw [he]
    exact unitary_binary hstar (by omega) hodd hm (starMap 3 G a) hs.order hs.outside
  · exact hd

/-- Discharge all cover field actions on the universal normal split-prime domain. -/
theorem alternatives_or_marked_star_cover
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    {K : Subgroup G} [K.Normal] (hK : K.IsCComponent)
    [IsQuasisimple (K ⧸ pCore 2 K)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hr : 1 < primeRank p K)
    (a : G) (ha : orderOf a=p) (haK : a ∉ K) (hgen : K ⊔ zpowers a=⊤) :
    Alternatives p K ∨ (p=3 ∧ MarkedStarCover K a) := by
  rcases CoverStructure.alternatives_or_star_cover hG hK hp ho hr a ha haK hgen with halt | ⟨rfl,hs⟩
  · exact Or.inl halt
  · exact Or.inr ⟨rfl,marked_star_cover (hG.stronglyQuasithin 3 Nat.prime_three (by decide)) a hs⟩

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverUnitaryBinary
