module
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.Coordinates
public import Theory.LinearAlgebra.SplitSeparableEigenbasis
public import Theory.GroupTheory.PrimeRankZero
public import Theory.GroupTheory.PrimeRankProduct
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
public import Mathlib.FieldTheory.KummerExtension
public import Mathlib.Tactic

/-!
# Split scalar cubes in unitary three-space

A split cubic annihilator yields an eigenbasis. When three divides q+1,
its eigenvalues have norm one, so distinct eigenspaces are orthogonal.
Hermitian normalization on each repeated block gives an orthonormal
basis, and the two norm-one torus coordinates centralize the supplied
matrix. The full special unitary group has only scalar linear centralizers:
a regular diagonal cubic forces diagonality, and a permutation cubic
equates the three diagonal entries.

Source: Aschbacher–Smith A.3.18, printed pp.52–53; finite Hermitian
normalization is the proved Huppert II.10.4. The block-normalization
calculation extends the order-nine argument in NormalSplitPrime.CoverUnitary.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory Polynomial
open scoped MatrixGroups
open HermitianForm HermitianForm.EvenInner
namespace Matrix.UnitaryCubic
variable {F : Type*} [Field F]

private theorem adjoint_mul (J : HermitianForm 3 F) (A B : Matrix (Fin 3) (Fin 3) F) :
    J.conjTranspose (A*B) = J.conjTranspose B * J.conjTranspose A := by
  change ((J.conj : F →+* F).mapMatrix (A*B)).transpose = _
  rw [map_mul,transpose_mul]
  rfl

private theorem adjoint_one (J : HermitianForm 3 F) : J.conjTranspose 1=1 := by
  change ((J.conj : F →+* F).mapMatrix 1).transpose = _
  rw [map_one,transpose_one]

private theorem adjoint_diagonal (J : HermitianForm 3 F) (d : Fin 3 → F) :
    J.conjTranspose (diagonal d) = diagonal (fun i => J.conj (d i)) := by
  ext i j
  by_cases h : i=j
  · subst j; simp [HermitianForm.conjTranspose]
  · simp [HermitianForm.conjTranspose, h, Ne.symm h]

private theorem block_normalize [Finite F] (J : HermitianForm 3 F) (q : ℕ)
    (hcard : Nat.card F=q^2) (hfixed : Nat.card {x : F // J.conj x=x}=q)
    (h02 : J.form 0 2=0) (h12 : J.form 1 2=0)
    (h20 : J.form 2 0=0) (h21 : J.form 2 1=0) (d : Fin 3 → F) (hd : d 0=d 1) :
    ∃ Q : GL (Fin 3) F, J.conjTranspose Q.val * J.form * Q.val=1 ∧
      Q.val * diagonal d = diagonal d * Q.val := by
  classical
  let B : Matrix (Fin 2) (Fin 2) F := !![J.form 0 0,J.form 0 1;J.form 1 0,J.form 1 1]
  have he : J.form.det=B.det*J.form 2 2 := by
    simp [B,Matrix.det_fin_three,Matrix.det_fin_two,h02,h12,h20,h21]
    ring
  have hn := J.form_nondegenerate
  rw [he] at hn
  obtain ⟨hB,ha⟩ := mul_ne_zero_iff.mp hn
  let J₂ : HermitianForm 2 F := {
    conj := J.conj
    conj_involutive := J.conj_involutive
    form := B
    form_hermitian := by
      intro i j
      fin_cases i <;> fin_cases j <;> exact J.form_hermitian _ _
    form_nondegenerate := hB }
  obtain ⟨P,hP⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis 2 J₂ q hcard hfixed
  obtain ⟨b,hb,hnorm⟩ := BenderSuzuki.External.huppert_II_10_4_norm_surjective J q hcard hfixed
    (J.form 2 2)⁻¹ (by rw [map_inv₀,J.form_hermitian]) (inv_ne_zero ha)
  have hlast : J.conj b * J.form 2 2 * b=1 := by
    calc _ = (b*J.conj b)*J.form 2 2 := by ring
         _ = 1 := by rw [hnorm,inv_mul_cancel₀ ha]
  let M : Matrix (Fin 3) (Fin 3) F := !![P.val 0 0,P.val 0 1,0;P.val 1 0,P.val 1 1,0;0,0,b]
  have hM : M.det≠0 := by
    have hm : M.det=P.val.det*b := by
      simp [M,Matrix.det_fin_three,Matrix.det_fin_two]
      ring
    rw [hm]
    exact mul_ne_zero P.det_ne_zero hb
  refine ⟨GeneralLinearGroup.mkOfDetNeZero M hM,?_,?_⟩
  · change J.conjTranspose M * J.form * M=1
    have hh (i j : Fin 2) := congrArg (fun A : Matrix (Fin 2) (Fin 2) F => A i j) hP
    have h00 := hh 0 0
    have h01 := hh 0 1
    have h10 := hh 1 0
    have h11 := hh 1 1
    simp [HermitianForm.conjTranspose,J₂,B,Matrix.mul_apply,Fin.sum_univ_two] at h00 h01 h10 h11
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [M,HermitianForm.conjTranspose,Matrix.mul_apply,Fin.sum_univ_three,
        h02,h12,h20,h21,h00,h01,h10,h11,hlast]
  · change M * diagonal d=diagonal d * M
    ext i j
    fin_cases i <;> fin_cases j <;> simp [M,Matrix.diagonal_mul,Matrix.mul_diagonal,hd,mul_comm]

private theorem gram_normalize [Finite F] (J : HermitianForm 3 F) (q : ℕ)
    (hcard : Nat.card F=q^2) (hfixed : Nat.card {x : F // J.conj x=x}=q)
    (d : Fin 3 → F) (hd : d 0=d 1) (hnorm : ∀ i, J.conj (d i)*d i=1)
    (hpres : J.conjTranspose (diagonal d)*J.form*diagonal d=J.form) :
    ∃ Q : GL (Fin 3) F, J.conjTranspose Q.val*J.form*Q.val=1 ∧
      Q.val*diagonal d=diagonal d*Q.val := by
  by_cases hs : d 0=d 2
  · obtain ⟨Q,hQ⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis 3 J q hcard hfixed
    refine ⟨Q,hQ,?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_mul,Matrix.mul_diagonal,←hd,←hs,mul_comm]
  · have off (i j : Fin 3) (hij : d i≠d j) : J.form i j=0 := by
      have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A i j) hpres
      rw [adjoint_diagonal] at he
      simp only [Matrix.diagonal_mul,Matrix.mul_diagonal] at he
      have hn := hnorm i
      by_contra hz
      have hp : J.conj (d i)*d j=1 := by
        apply mul_right_cancel₀ hz
        calc _ = J.conj (d i)*J.form i j*d j := by ring
             _ = 1*J.form i j := by simpa using he
      have hi : J.conj (d i)≠0 := by intro h; rw [h,zero_mul] at hn; exact zero_ne_one hn
      exact hij (mul_left_cancel₀ hi (hn.trans hp.symm))
    exact block_normalize J q hcard hfixed (off 0 2 hs) (off 1 2 (hd ▸ hs))
      (off 2 0 (Ne.symm hs)) (off 2 1 (hd ▸ (Ne.symm hs))) d hd

private def gram (J : HermitianForm 3 F) (P : GL (Fin 3) F) : HermitianForm 3 F where
  conj := J.conj
  conj_involutive := J.conj_involutive
  form := J.conjTranspose P.val*J.form*P.val
  form_hermitian := by
    let : Star F := ⟨J.conj⟩
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

private theorem permute_diagonal (P : GL (Fin 3) F) (d : Fin 3 → F)
    (σ : Equiv.Perm (Fin 3)) :
    ∃ Q : GL (Fin 3) F, Q.val*diagonal (fun i => d (σ i))*Q⁻¹.val=
      P.val*diagonal d*P⁻¹.val := by
  classical
  let R : GL (Fin 3) F := (Matrix.permMatrixHom (n := Fin 3) (R := F)).toHomUnits σ
  have hR (i j : Fin 3) : R.val i j=if i=σ j then 1 else 0 := by
    change ((σ⁻¹).permMatrix F) i j=_
    simp [Equiv.Perm.permMatrix,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,
      Equiv.Perm.inv_def,Equiv.symm_apply_eq]
  have he : R.val*diagonal (fun i => d (σ i))=diagonal d*R.val := by
    ext i j
    simp only [Matrix.diagonal_mul,Matrix.mul_diagonal,hR]
    split_ifs with h
    · simp [h]
    · simp
  refine ⟨P*R,?_⟩
  change (P.val*R.val)*diagonal (fun i => d (σ i))*(R⁻¹.val*P⁻¹.val)=_
  rw [mul_assoc P.val,he]
  simp only [←mul_assoc,Units.mul_inv_cancel_right]

private theorem split_cube_eigenbasis {F : Type*} [Field F]
    (g : GL (Fin 3) F) (z w a : F) (hw : IsPrimitiveRoot w 3)
    (hcube : g.val^3=Matrix.scalar (Fin 3) z) (ha : a^3=z) (ha0 : a≠0) :
    ∃ (P : GL (Fin 3) F) (d : Fin 3 → F),
      P.val*Matrix.diagonal d*P⁻¹.val=g.val := by
  classical
  let p : F[X] := X^3-C z
  have hs : p.Splits := X_pow_sub_C_splits_of_isPrimitiveRoot hw ha
  have hp : p.Separable := by
    rw [show p = ∏ i ∈ Finset.range 3, (X-C (w^i*a)) from
      X_pow_sub_C_eq_prod hw (by decide) ha]
    apply separable_prod_X_sub_C_iff'.mpr
    intro i hi j hj he
    exact hw.pow_inj (Finset.mem_range.mp hi) (Finset.mem_range.mp hj)
      (mul_right_cancel₀ ha0 he)
  let f := Matrix.toLin' g.val
  have heval : aeval f p = 0 := by
    have he : aeval g.val p = 0 := by
      simp only [p,map_sub,map_pow,aeval_X,aeval_C]
      rw [hcube]
      simp [Matrix.algebraMap_eq_diagonal,Matrix.scalar_apply]
    change aeval (Matrix.toLinAlgEquiv' (R := F) g.val) p = 0
    rw [aeval_algHom_apply,he,map_zero]
  obtain ⟨b,μ,hb⟩ := Module.End.exists_eigenbasis_of_split_separable_annihilator f p (monic_X_pow_sub_C _ (by decide)) hs hp heval
  have hdim : Module.finrank F (Fin 3 → F)=3 := by simp
  let b' := b.reindex (finCongr hdim)
  let d : Fin 3 → F := fun i => μ ((finCongr hdim).symm i)
  have hd : LinearMap.toMatrix b' b' f = Matrix.diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [LinearMap.toMatrix_apply,b',d,Module.Basis.reindex_apply,hb]
    · simp [LinearMap.toMatrix_apply,b',d,Module.Basis.reindex_apply,hb,
        hij]
  let s := Pi.basisFun F (Fin 3)
  let P : GL (Fin 3) F := ⟨s.toMatrix b',b'.toMatrix s,
    s.toMatrix_mul_toMatrix_flip b',b'.toMatrix_mul_toMatrix_flip s⟩
  refine ⟨P,d,?_⟩
  change s.toMatrix b' * Matrix.diagonal d * b'.toMatrix s = g.val
  rw [←hd,basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
  simp [s,f,LinearMap.toMatrix_eq_toMatrix']


private theorem root_norm [Finite F] (J : HermitianForm 3 F) (q : ℕ)
    (hconj : ∀ x, J.conj x=x^q) (hq : 3 ∣ q+1)
    (z a : F) (hz : J.conj z*z=1) (ha : a^3=z) : J.conj a*a=1 := by
  let b := J.conj a*a
  have hb3 : b^3=1 := by dsimp [b]; rw [mul_pow,←map_pow,ha,hz]
  have hb0 : b≠0 := by intro h; rw [h,zero_pow (by decide)] at hb3; exact zero_ne_one hb3
  have hbq : b^q=b := by
    rw [←hconj]
    change J.conj (J.conj a*a)=J.conj a*a
    rw [map_mul,J.conj_involutive,mul_comm]
  have hmod : q%3=2 := by have := Nat.mod_eq_zero_of_dvd hq; omega
  have hqeq : q=3*(q/3)+2 := by omega
  have hb2 : b^2=b := by
    rw [hqeq,pow_add,pow_mul,hb3,one_pow,one_mul] at hbq
    exact hbq
  exact (mul_eq_left₀ hb0).mp (by simpa [pow_two] using hb2)

private theorem diagonal_normalize [Finite F] (J : HermitianForm 3 F) (q : ℕ)
    (hcard : Nat.card F=q^2) (hfixed : Nat.card {x : F // J.conj x=x}=q)
    (d : Fin 3 → F) (hd : Function.Injective d) (hnorm : ∀ i, J.conj (d i)*d i=1)
    (hpres : J.conjTranspose (diagonal d)*J.form*diagonal d=J.form) :
    ∃ Q : GL (Fin 3) F, J.conjTranspose Q.val*J.form*Q.val=1 ∧
      Q.val*diagonal d=diagonal d*Q.val := by
  classical
  have hoff (i j : Fin 3) (hij : i≠j) : J.form i j=0 := by
    have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) F => A i j) hpres
    rw [adjoint_diagonal] at he
    simp only [Matrix.diagonal_mul,Matrix.mul_diagonal] at he
    have hn := hnorm i
    by_contra hz
    have hp : J.conj (d i)*d j=1 := by
      apply mul_right_cancel₀ hz
      calc _ = J.conj (d i)*J.form i j*d j := by ring
           _ = 1*J.form i j := by simpa using he
    have hi : J.conj (d i)≠0 := by intro h; rw [h,zero_mul] at hn; exact zero_ne_one hn
    exact hij (hd (mul_left_cancel₀ hi (hn.trans hp.symm)))
  have hdiag : J.form=diagonal (fun i => J.form i i) := by
    ext i j
    by_cases h : i=j
    · subst j; simp
    · simp [hoff i j h,h]
  have hnon (i : Fin 3) : J.form i i≠0 := by
    have he := J.form_nondegenerate
    rw [hdiag,det_diagonal] at he
    exact (Finset.prod_ne_zero_iff.mp he i (Finset.mem_univ i))
  have hex (i : Fin 3) : ∃ b : F, b≠0 ∧ b*J.conj b=(J.form i i)⁻¹ :=
    BenderSuzuki.External.huppert_II_10_4_norm_surjective J q hcard hfixed
      (J.form i i)⁻¹ (by rw [map_inv₀,J.form_hermitian]) (inv_ne_zero (hnon i))
  choose b hb hn using hex
  have hdet : (diagonal b).det≠0 := by rw [det_diagonal]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hb i)
  let Q := GeneralLinearGroup.mkOfDetNeZero (diagonal b) hdet
  refine ⟨Q,?_,?_⟩
  · change J.conjTranspose (diagonal b)*J.form*diagonal b=1
    rw [adjoint_diagonal,hdiag,diagonal_mul_diagonal,diagonal_mul_diagonal]
    rw [←diagonal_one]
    congr 1
    ext i
    change J.conj (b i)*J.form i i*b i=1
    calc _ = (b i*J.conj (b i))*J.form i i := by ring
         _ = 1 := by rw [hn,inv_mul_cancel₀ (hnon i)]
  · change diagonal b*diagonal d=diagonal d*diagonal b
    simp only [diagonal_mul_diagonal,mul_comm]

/-- A split scalar cube in a unitary three-space has an orthonormal eigenbasis. -/
theorem split_eigenbasis [Finite F] (J : HermitianForm 3 F) (q : ℕ)
    (hcard : Nat.card F=q^2) (hconj : ∀ x, J.conj x=x^q)
    (hfixed : Nat.card {x : F // J.conj x=x}=q) (hq : 3 ∣ q+1)
    (g : J.unitarySubgroup) (z : Fˣ) (hz : J.conj (z:F)*z=1)
    (hc : g.val^3=GeneralLinearGroup.scalar (Fin 3) z)
    (w a : F) (hw : IsPrimitiveRoot w 3) (ha : a^3=(z:F)) :
    ∃ (P : GL (Fin 3) F) (d : Fin 3 → F),
      J.conjTranspose P.val*J.form*P.val=1 ∧
        P.val*diagonal d*P⁻¹.val=g.val.val := by
  have ha0 : a≠0 := by intro he; rw [he,zero_pow (by decide)] at ha; exact z.ne_zero ha.symm
  obtain ⟨P,d,hP⟩ := split_cube_eigenbasis g.val z w a hw (congrArg Units.val hc) ha ha0
  have chooseBasis : ∃ (P : GL (Fin 3) F) (d : Fin 3 → F),
      (d 0=d 1 ∨ Function.Injective d) ∧ P.val*diagonal d*P⁻¹.val=g.val.val := by
    by_cases h01 : d 0=d 1
    · exact ⟨P,d,Or.inl h01,hP⟩
    by_cases h02 : d 0=d 2
    · obtain ⟨Q,hQ⟩ := permute_diagonal P d (Equiv.swap 1 2)
      exact ⟨Q,fun i => d (Equiv.swap 1 2 i),Or.inl (by simpa [Equiv.swap_apply_def] using h02),hQ.trans hP⟩
    by_cases h12 : d 1=d 2
    · obtain ⟨Q,hQ⟩ := permute_diagonal P d (Equiv.swap 0 2)
      exact ⟨Q,fun i => d (Equiv.swap 0 2 i),Or.inl (by simpa [Equiv.swap_apply_def] using h12.symm),hQ.trans hP⟩
    refine ⟨P,d,Or.inr ?_,hP⟩
    intro i j he
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨P,d,hd,hP⟩ := chooseBasis
  have hd3 (i : Fin 3) : d i^3=(z:F) := by
    let D := (MulAut.conj P⁻¹) g.val
    have hD : D.val=diagonal d := by
      change P⁻¹.val*g.val.val*P.val=diagonal d
      rw [←hP]
      simp only [←mul_assoc,Units.inv_mul_cancel_right,Units.inv_mul,one_mul]
    have hDc : D^3=GeneralLinearGroup.scalar (Fin 3) z := by
      change ((MulAut.conj P⁻¹) g.val)^3=_
      rw [←map_pow,hc]
      change P⁻¹*GeneralLinearGroup.scalar (Fin 3) z*P=_
      rw [←GeneralLinearGroup.scalar_commute z P⁻¹]
      simp only [mul_assoc,inv_mul_cancel,mul_one]
    have he := congrArg (fun A : GL (Fin 3) F => A.val i i) hDc
    simpa only [Units.val_pow_eq_pow_val,hD,diagonal_pow,Pi.pow_apply,
      GeneralLinearGroup.coe_scalar,Matrix.scalar_apply,diagonal_apply_eq] using he
  have hnorm (i : Fin 3) : J.conj (d i)*d i=1 := root_norm J q hconj hq z (d i) hz (hd3 i)
  have hYP : g.val.val*P.val=P.val*diagonal d := by
    rw [←hP]
    simp only [mul_assoc,Units.inv_mul,mul_one]
  have hgram : (gram J P).conjTranspose (diagonal d)*(gram J P).form*diagonal d=(gram J P).form := by
    change J.conjTranspose (diagonal d)*(J.conjTranspose P.val*J.form*P.val)*diagonal d=_
    have hh := congrArg J.conjTranspose hYP
    rw [adjoint_mul,adjoint_mul] at hh
    calc
      _ = (J.conjTranspose (diagonal d)*J.conjTranspose P.val)*J.form*(P.val*diagonal d) := by simp only [mul_assoc]
      _ = (J.conjTranspose P.val*J.conjTranspose g.val.val)*J.form*(g.val.val*P.val) := by rw [←hh,←hYP]
      _ = J.conjTranspose P.val*(J.conjTranspose g.val.val*J.form*g.val.val)*P.val := by simp only [mul_assoc]
      _ = _ := by rw [g.property]; rfl
  have hQex : ∃ Q : GL (Fin 3) F, (gram J P).conjTranspose Q.val*(gram J P).form*Q.val=1 ∧
      Q.val*diagonal d=diagonal d*Q.val := by
    rcases hd with hd | hd
    · exact gram_normalize (gram J P) q hcard hfixed d hd hnorm hgram
    · exact diagonal_normalize (gram J P) q hcard hfixed d hd hnorm hgram
  obtain ⟨Q,hQ,hcomm⟩ := hQex
  refine ⟨P*Q,d,?_,?_⟩
  · change J.conjTranspose (P.val*Q.val)*J.form*(P.val*Q.val)=1
    rw [adjoint_mul]
    change J.conjTranspose Q.val*(J.conjTranspose P.val*J.form*P.val)*Q.val=1 at hQ
    simpa only [mul_assoc] using hQ
  · change (P.val*Q.val)*diagonal d*(Q⁻¹.val*P⁻¹.val)=g.val.val
    rw [mul_assoc P.val,hcomm]
    simpa only [←mul_assoc,Units.mul_inv_cancel_right] using hP
/-- The fixed torus is in the centralizer of the supplied matrix itself. -/
theorem split_centralizer_rank [Finite F] (J : HermitianForm 3 F) (q : ℕ)
    (hcard : Nat.card F=q^2) (hconj : ∀ x, J.conj x=x^q)
    (hfixed : Nat.card {x : F // J.conj x=x}=q) (hq : 3 ∣ q+1)
    (y : J.unitarySubgroup) (u : Fˣ) (hu : J.conj (u:F)*u=1)
    (hc : y.val^3=GeneralLinearGroup.scalar (Fin 3) u)
    (w a : F) (hw : IsPrimitiveRoot w 3) (ha : a^3=(u:F)) :
    2 ≤ primeRank 3 ((centralizer ({y.val} : Set (GL (Fin 3) F))).comap J.specialSubgroup.subtype) := by
  obtain ⟨P,d,hgram,hP⟩ := split_eigenbasis J q hcard hconj hfixed hq y u hu hc w a hw ha
  let frame : UnitaryThree.OddTorusNormalizer.OrthogonalFrame J := ⟨P,hgram⟩
  let pair := UnitaryThree.OddTorusNormalizer.specialPairHom J frame
  have hcoord : ((MulAut.conj P⁻¹) y.val).val=diagonal d := by
    change P⁻¹.val*y.val.val*P.val=diagonal d
    rw [←hP]
    simp only [←mul_assoc,Units.inv_mul_cancel_right,Units.inv_mul,one_mul]
  have hfix (x : normOne J × normOne J) : pair x ∈ (centralizer ({y.val} : Set (GL (Fin 3) F))).comap J.specialSubgroup.subtype := by
    let D := UnitaryThree.OddTorusNormalizer.diagonalHom
      (UnitaryThree.OddTorusNormalizer.pairDiagonal J x)
    have hcomm : Commute D ((MulAut.conj P⁻¹) y.val) := by
      apply Units.ext
      change D.val*((MulAut.conj P⁻¹) y.val).val=((MulAut.conj P⁻¹) y.val).val*D.val
      rw [hcoord]
      change diagonal _ * diagonal d=diagonal d * diagonal _
      rw [diagonal_mul_diagonal,diagonal_mul_diagonal]
      congr 1
      ext i
      exact mul_comm _ _
    have hh := hcomm.map (MulAut.conj P).toMonoidHom
    apply mem_centralizer_singleton_iff.mpr
    change (P*D*P⁻¹)*y.val=y.val*(P*D*P⁻¹)
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,
      mul_assoc,mul_inv_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh.eq
  let f := pair.codRestrict ((centralizer ({y.val} : Set (GL (Fin 3) F))).comap J.specialSubgroup.subtype) hfix
  have hf : Function.Injective f := fun x z h =>
    UnitaryThree.OddTorusNormalizer.specialPairHom_injective J frame (congrArg Subtype.val h)
  have hr := Theory.GroupTheory.primeRank_le_of_injective 3 f hf
  rw [primeRank_prod_eq_add] at hr
  have hnrank : primeRank 3 (normOne J) ≠ 0 := by
    intro he
    have hh := PrimeRank.eq_zero_iff_not_dvd_card.mp he
    apply hh
    rwa [normOne_card J hcard hconj]
  omega


/-- The linear centralizer of the full special unitary group is scalar. -/
theorem centralizer_scalar [Finite F] (J : HermitianForm 3 F) (q : ℕ)
    (hcard : Nat.card F=q^2) (hfixed : Nat.card {x : F // J.conj x=x}=q)
    (hconj : ∀ x, J.conj x=x^q) (hq : 3 ∣ q+1)
    (A : GL (Fin 3) F) (hA : ∀ s : J.specialSubgroup, Commute A s.val) :
    ∃ z : Fˣ, A=GeneralLinearGroup.scalar (Fin 3) z := by
  classical
  obtain ⟨P,hP⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis 3 J q hcard hfixed
  let I := IdentityGram.identityGram J
  let e := IdentityGram.specialEquiv J P hP
  let B := (MulAut.conj P⁻¹) A
  have hB (s : I.specialSubgroup) : Commute B s.val := by
    have h := (hA (e.symm s)).map (MulAut.conj P⁻¹).toMonoidHom
    have he : (MulAut.conj P⁻¹) (e.symm s).val=s.val := by
      change P⁻¹*(e.symm s).val*P=s.val
      exact (IdentityGram.specialEquiv_apply J P hP (e.symm s)).symm.trans
        (congrArg Subtype.val (e.apply_symm_apply s))
    change Commute B ((MulAut.conj P⁻¹) (e.symm s).val) at h
    rwa [he] at h
  obtain ⟨w,hw⟩ := exists_prime_orderOf_dvd_card' (G := normOne J) 3
    (by rwa [normOne_card J hcard hconj])
  let u : Fˣ := w.val
  have hu3 : u^3=1 := by
    have h := pow_orderOf_eq_one w
    rw [hw] at h
    exact congrArg Subtype.val h
  have huord : orderOf (u:F)=3 := by
    rw [orderOf_units]
    exact (orderOf_injective (normOne J).subtype (normOne J).subtype_injective w).trans hw
  have hprim : IsPrimitiveRoot (u:F) 3 := IsPrimitiveRoot.iff_orderOf.mpr huord
  let D : GL (Fin 3) F := UnitaryThree.OddTorusNormalizer.diagonalHom ![1,u,u^2]
  have hDu : D∈I.specialSubgroup := by
    apply (UnitaryThree.OddTorusNormalizer.diagonal_mem_identity_special_iff J _).mpr
    constructor
    · intro i
      fin_cases i
      · exact (normOne J).one_mem
      · exact w.property
      · exact (normOne J).pow_mem w.property 2
    · simpa [Fin.prod_univ_three,←pow_succ'] using hu3
  have hD := congrArg Units.val (hB ⟨D,hDu⟩).eq
  have hDv : D.val=diagonal (![1,(u:F),(u:F)^2]) := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  change B.val*D.val=D.val*B.val at hD
  rw [hDv] at hD
  have hd (i j : Fin 3) : B.val i j * (![1,(u:F),(u:F)^2] j) =
      (![1,(u:F),(u:F)^2] i) * B.val i j := by
    have he := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M i j) hD
    simpa only [Matrix.mul_diagonal,Matrix.diagonal_mul] using he
  have hdistinct : Function.Injective (![1,(u:F),(u:F)^2] : Fin 3 → F) := by
    have he : (![1,(u:F),(u:F)^2] : Fin 3 → F) = fun i => (u:F)^i.val := by
      ext i; fin_cases i <;> simp
    rw [he]
    intro i j hij
    exact Fin.ext (hprim.pow_inj i.isLt j.isLt hij)
  have hoff (i j : Fin 3) (hij : i≠j) : B.val i j=0 := by
    have hh := hd i j
    by_contra hn
    exact hij (hdistinct (mul_left_cancel₀ hn (hh.trans (mul_comm _ _))).symm)
  let Rm : Matrix (Fin 3) (Fin 3) F := !![0,1,0;0,0,1;1,0,0]
  have hRd : Rm.det=1 := by simp [Rm,det_fin_three]
  let R := GeneralLinearGroup.mkOfDetNeZero Rm (hRd ▸ one_ne_zero)
  have hRu : R∈I.specialSubgroup := by
    constructor
    · change I.conjTranspose Rm*1*Rm=1
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Rm,HermitianForm.conjTranspose,I,IdentityGram.identityGram,
          Matrix.mul_apply,Fin.sum_univ_three]
    · exact Units.ext hRd
  have hR := congrArg Units.val (hB ⟨R,hRu⟩).eq
  change B.val*Rm=Rm*B.val at hR
  have h01 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 0 1) hR
  have h12 := congrArg (fun M : Matrix (Fin 3) (Fin 3) F => M 1 2) hR
  simp [Rm,Matrix.mul_apply,Fin.sum_univ_three] at h01 h12
  have hs : B.val=Matrix.scalar (Fin 3) (B.val 0 0) := by
    ext i j
    by_cases h : i=j
    · subst j
      fin_cases i <;> simp [Matrix.scalar_apply,h01,h12]
    · simp [Matrix.scalar_apply,h,hoff i j h]
  have hBc : B∈center (GL (Fin 3) F) :=
    GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mpr ⟨B.val 0 0,hs.symm⟩
  rw [GeneralLinearGroup.center_eq_range_scalar] at hBc
  obtain ⟨z,hz⟩ := hBc
  refine ⟨z,?_⟩
  have he := congrArg (MulAut.conj P) hz
  change P*GeneralLinearGroup.scalar (Fin 3) z*P⁻¹=P*(P⁻¹*A*P)*P⁻¹ at he
  rw [←GeneralLinearGroup.scalar_commute z P] at he
  simpa only [mul_assoc,mul_inv_cancel,mul_one,mul_inv_cancel_left] using he.symm
theorem scalar_unitary (J : HermitianForm 3 F) (c : Fˣ) :
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

end Matrix.UnitaryCubic
