module
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverLinear
public import Theory.SpecificGroups.UnitaryThree.OddTorusNormalizer.Structure.Coordinates
public import Theory.SpecificGroups.PSU3.UniversalCover.Kernel
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import Theory.GroupTheory.PrimeRankZero
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.GroupTheory.PrimeRankProduct
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Fixed tori of order-nine implementers in the actual unitary cover

The nonidentity central cube of a determinant-one ternary matrix has a
cube root in the original coefficient field, so the matrix diagonalizes
there. Its eigenvalues have order nine. Since three divides q+1, those
ninth roots have norm one. Distinct eigenspaces are orthogonal; normalizing
the repeated eigenspace and its complement gives an orthonormal eigenbasis.
The resulting two norm-one torus coordinates centralize the original matrix.

The covering-group adapter derives the scalar cube and the congruence from
the actual special-to-projective kernel. Together with the order-nine
implementer from CoverInner, the fixed torus excludes inner outside cubics.
CoverOuter applies this to the literal two-core component and Cartan actor.
Source: Aschbacher–Smith A.3.18, printed p.52; orthonormalization uses the
proved Huppert II.10.4 finite Hermitian-form results.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups Theory.GroupTheory
open scoped MatrixGroups
open HermitianForm HermitianForm.EvenInner
namespace CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverInner
variable {F : Type*} [Field F]

private theorem repeated_roots (a b c z : F) (ha : a^3=z) (hb : b^3=z)
    (hc : c^3=z) (hd : a*b*c=1) (hz : z≠1) : a=b ∨ a=c ∨ b=c := by
  by_contra! hn
  have hab : a^2+a*b+b^2=0 := by
    apply (mul_eq_zero.mp (show (a-b)*(a^2+a*b+b^2)=0 by
      linear_combination ha-hb)).resolve_left (sub_ne_zero.mpr hn.1)
  have hac : a^2+a*c+c^2=0 := by
    apply (mul_eq_zero.mp (show (a-c)*(a^2+a*c+c^2)=0 by
      linear_combination ha-hc)).resolve_left (sub_ne_zero.mpr hn.2.1)
  have hs : a+b+c=0 := by
    apply (mul_eq_zero.mp (show (b-c)*(a+b+c)=0 by
      linear_combination hab-hac)).resolve_left (sub_ne_zero.mpr hn.2.2)
  apply hz
  linear_combination a*hab-a*b*hs+hd-ha

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

private theorem diagonal_data (y : GL (Fin 3) F) (hy : GeneralLinearGroup.det y=1)
    (u : Fˣ) (hc : y^3=GeneralLinearGroup.scalar (Fin 3) u)
    (P : GL (Fin 3) F) (d : Fin 3 → F)
    (hP : P.val*diagonal d*P⁻¹.val=y.val) :
    (∀ i, d i^3=(u : F)) ∧ d 0*d 1*d 2=1 := by
  let D := (MulAut.conj P⁻¹) y
  have hD : D.val=diagonal d := by
    change P⁻¹.val*y.val*P.val=diagonal d
    rw [←hP]
    simp only [←mul_assoc,Units.inv_mul_cancel_right,Units.inv_mul,one_mul]
  have hu : GeneralLinearGroup.scalar (Fin 3) u ∈ center (GL (Fin 3) F) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨u,rfl⟩
  have hDc : D^3=GeneralLinearGroup.scalar (Fin 3) u := by
    change ((MulAut.conj P⁻¹) y)^3=_
    rw [←map_pow,hc]
    change P⁻¹*GeneralLinearGroup.scalar (Fin 3) u*P=_
    rw [mem_center_iff.mp hu P⁻¹]
    group
  have hd : GeneralLinearGroup.det D=1 := by
    change GeneralLinearGroup.det (P⁻¹*y*P)=1
    simp [map_mul,hy,map_inv]
  constructor
  · intro i
    have hh := congrArg (fun A : GL (Fin 3) F => A.val i i) hDc
    simp only [Units.val_pow_eq_pow_val,GeneralLinearGroup.coe_scalar] at hh
    simpa only [hD,diagonal_pow,Pi.pow_apply,Matrix.scalar_apply,diagonal_apply_eq,Units.val_one] using hh
  · have hh := congrArg Units.val hd
    change D.val.det=1 at hh
    simpa only [hD,det_diagonal,Fin.prod_univ_three] using hh

private theorem scalar_eigenbasis (y : SL(3,F)) (u : Fˣ) (hu : u^3=1)
    (hn : u≠1) (hc : y.val^3=Matrix.scalar (Fin 3) (u : F)) :
    ∃ (P : GL (Fin 3) F) (d : Fin 3 → F), d 0=d 1 ∧
      P.val*diagonal d*P⁻¹.val=y.val := by
  have hz : y^3∈center SL(3,F) :=
    Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨(u : F),by simpa using congrArg Units.val hu,hc.symm⟩
  have hn' : y^3≠1 := by
    intro he
    apply hn
    apply Units.ext
    have hh := congrArg (fun M : SL(3,F) => M.val 0 0) he
    change (y.val^3) 0 0=1 at hh
    simpa only [hc,Matrix.scalar_apply,diagonal_apply_eq,Units.val_one] using hh
  obtain ⟨P,d,hP⟩ := linear_eigenbasis y hz hn'
  have hh := diagonal_data (SpecialLinearGroup.toGL y) (by simp) u (Units.ext hc) P d hP
  have hu1 : (u : F)≠1 := fun he => hn (Units.ext he)
  rcases repeated_roots (d 0) (d 1) (d 2) u (hh.1 0) (hh.1 1) (hh.1 2) hh.2 hu1 with hab | hac | hbc
  · exact ⟨P,d,hab,hP⟩
  · obtain ⟨Q,hQ⟩ := permute_diagonal P d (Equiv.swap 1 2)
    exact ⟨Q,fun i => d (Equiv.swap 1 2 i),by simpa [Equiv.swap_apply_def] using hac,hQ.trans hP⟩
  · obtain ⟨Q,hQ⟩ := permute_diagonal P d (Equiv.swap 0 2)
    exact ⟨Q,fun i => d (Equiv.swap 0 2 i),by simpa [Equiv.swap_apply_def] using hbc.symm,hQ.trans hP⟩

private theorem ninth_norm [Finite F] (J : HermitianForm 3 F) (q : ℕ)
    (hcard : Nat.card F=q^2) (hconj : ∀ x, J.conj x=x^q)
    (hq : 3 ∣ q+1) (a : F) (ha : orderOf a=9) : J.conj a*a=1 := by
  have ha0 : a≠0 := by intro he; simp [he] at ha
  let au : Fˣ := Units.mk0 a ha0
  have hao : orderOf au=9 := (orderOf_units (y := au)).symm.trans ha
  have hqpos : 1≤q := by
    have hpos := Nat.card_pos (α := F)
    rw [hcard] at hpos
    nlinarith
  have hcop3 : Nat.Coprime 3 (q-1) := by
    apply Nat.prime_three.coprime_iff_not_dvd.mpr
    intro hd
    have h1 := Nat.mod_eq_zero_of_dvd hq
    have h2 := Nat.mod_eq_zero_of_dvd hd
    omega
  have hdiv : 9 ∣ q+1 := (hcop3.pow_left 2).dvd_of_dvd_mul_left (by
    have he := orderOf_dvd_natCard au
    rw [hao,Nat.card_units,hcard] at he
    rwa [show q^2-1=(q-1)*(q+1) by simpa [mul_comm] using Nat.sq_sub_sq q 1] at he)
  rw [hconj,←pow_succ]
  exact orderOf_dvd_iff_pow_eq_one.mp (ha ▸ hdiv)

/-- The original scalar-cube unitary matrix has an orthonormal eigenbasis. -/
theorem unitary_scalar_eigenbasis [Finite F] (J : HermitianForm 3 F) (q : ℕ)
    (hcard : Nat.card F=q^2) (hconj : ∀ x, J.conj x=x^q)
    (hfixed : Nat.card {x : F // J.conj x=x}=q) (hq : 3 ∣ q+1)
    (y : J.specialSubgroup) (u : Fˣ) (hu : u^3=1) (hn : u≠1)
    (hc : y.val^3=GeneralLinearGroup.scalar (Fin 3) u) :
    ∃ (P : GL (Fin 3) F) (d : Fin 3 → F),
      J.conjTranspose P.val*J.form*P.val=1 ∧
        P.val*diagonal d*P⁻¹.val=y.val.val := by
  let ys : SL(3,F) := ⟨y.val.val,congrArg Units.val y.property.2⟩
  obtain ⟨P,d,hd,hP⟩ := scalar_eigenbasis ys u hu hn (congrArg Units.val hc)
  change P.val*diagonal d*P⁻¹.val=y.val.val at hP
  have he := diagonal_data y.val y.property.2 u hc P d hP
  have hn' : (u : F)≠1 := fun h => hn (Units.ext h)
  have hnorm (i : Fin 3) : J.conj (d i)*d i=1 := by
    apply ninth_norm J q hcard hconj hq
    apply orderOf_eq_prime_pow (p := 3) (n := 1)
    · change d i^3≠1
      simpa only [he.1 i] using hn'
    · change d i^9=1
      rw [show 9=3*3 from rfl,pow_mul,he.1 i]
      exact congrArg Units.val hu
  have hYP : y.val.val*P.val=P.val*diagonal d := by
    rw [←hP]
    simp only [mul_assoc,Units.inv_mul, mul_one]
  have hgram : (gram J P).conjTranspose (diagonal d)*(gram J P).form*diagonal d=(gram J P).form := by
    change J.conjTranspose (diagonal d)*(J.conjTranspose P.val*J.form*P.val)*diagonal d=_
    have hh := congrArg J.conjTranspose hYP
    rw [adjoint_mul,adjoint_mul] at hh
    calc
      _ = (J.conjTranspose (diagonal d)*J.conjTranspose P.val)*J.form*(P.val*diagonal d) := by simp only [mul_assoc]
      _ = (J.conjTranspose P.val*J.conjTranspose y.val.val)*J.form*(y.val.val*P.val) := by rw [←hh,←hYP]
      _ = J.conjTranspose P.val*(J.conjTranspose y.val.val*J.form*y.val.val)*P.val := by simp only [mul_assoc]
      _ = _ := by rw [y.property.1]; rfl
  obtain ⟨Q,hQ,hcomm⟩ := gram_normalize (gram J P) q hcard hfixed d hd hnorm hgram
  refine ⟨P*Q,d,?_,?_⟩
  · change J.conjTranspose (P.val*Q.val)*J.form*(P.val*Q.val)=1
    rw [adjoint_mul]
    change J.conjTranspose Q.val*(J.conjTranspose P.val*J.form*P.val)*Q.val=1 at hQ
    simpa only [mul_assoc] using hQ
  · change (P.val*Q.val)*diagonal d*(Q⁻¹.val*P⁻¹.val)=y.val.val
    rw [mul_assoc P.val,hcomm]
    simpa only [←mul_assoc,Units.mul_inv_cancel_right] using hP

/-- The fixed torus is in the centralizer of the supplied matrix itself. -/
theorem unitary_scalar_centralizer_rank [Finite F] (J : HermitianForm 3 F) (q : ℕ)
    (hcard : Nat.card F=q^2) (hconj : ∀ x, J.conj x=x^q)
    (hfixed : Nat.card {x : F // J.conj x=x}=q) (hq : 3 ∣ q+1)
    (y : J.specialSubgroup) (u : Fˣ) (hu : u^3=1) (hn : u≠1)
    (hc : y.val^3=GeneralLinearGroup.scalar (Fin 3) u) :
    2 ≤ primeRank 3 (centralizer ({y} : Set J.specialSubgroup)) := by
  obtain ⟨P,d,hgram,hP⟩ := unitary_scalar_eigenbasis J q hcard hconj hfixed hq y u hu hn hc
  let frame : UnitaryThree.OddTorusNormalizer.OrthogonalFrame J := ⟨P,hgram⟩
  let pair := UnitaryThree.OddTorusNormalizer.specialPairHom J frame
  have hcoord : ((MulAut.conj P⁻¹) y.val).val=diagonal d := by
    change P⁻¹.val*y.val.val*P.val=diagonal d
    rw [←hP]
    simp only [←mul_assoc,Units.inv_mul_cancel_right,Units.inv_mul,one_mul]
  have hfix (x : normOne J × normOne J) : pair x ∈ centralizer ({y} : Set J.specialSubgroup) := by
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
    apply Subtype.ext
    change (P*D*P⁻¹)*y.val=y.val*(P*D*P⁻¹)
    simpa only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,
      mul_assoc,mul_inv_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh.eq
  let f := pair.codRestrict (centralizer ({y} : Set J.specialSubgroup)) hfix
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


private theorem unitary_model_data [Finite F] (J : HermitianForm 3 F) (q : ℕ)
    (hq : Chapter1.Section02.LocalModels.CoverParameter true q)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q) :
    Nat.card {x : F // J.conj x = x} = q ∧
      center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
  rcases hq with ⟨n, hn, rfl, _⟩ | ⟨hp, ho⟩
  · exact ⟨FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega)
      hcard hconj, EvenProjectiveComparison.center_eq_bot J (by omega) hcard hconj⟩
  · let : Fact q.Prime := ⟨hp⟩
    have hfixed : Nat.card {x : F // J.conj x = x} = q := by
      simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
        J.conj q 1 (by decide) (by simpa using hcard) (by simpa using hconj)
    have hlarge : 2 < q := by have := hp.two_le; have := Nat.odd_iff.mp ho; omega
    let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
      BenderSuzuki.External.huppert_II_10_13 J q hlarge hcard hfixed
    let := J.projective_isPerfect_of_fixed_card hlarge hcard hfixed
    refine ⟨hfixed, ?_⟩
    rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top
        with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim

/-- A nonidentity central cube in the actual special unitary cover has a
centralizer of three-rank at least two. The field order is q². -/
theorem unitary_centralizer_rank [Finite F] (J : HermitianForm 3 F) (q : ℕ)
    (hq : Chapter1.Section02.LocalModels.CoverParameter true q)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (y : J.specialSubgroup) (hc : y ^ 3 ∈ center J.specialSubgroup) (hne : y ^ 3 ≠ 1) :
    2 ≤ primeRank 3 (centralizer ({y} : Set J.specialSubgroup)) := by
  obtain ⟨hfixed, hZ⟩ := unitary_model_data J q hq hcard hconj
  have hk : y ^ 3 ∈ J.specialToProjective.ker :=
    (J.specialToProjective_ker_eq_center hZ).symm ▸ hc
  have hGL : (y ^ 3).val ∈ center (GL (Fin 3) F) := by
    apply ProjGenLinGroup.mk_eq_one.mp
    simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
      congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
  rw [GeneralLinearGroup.center_eq_range_scalar] at hGL
  obtain ⟨u, hu⟩ := hGL
  have hu3 : u ^ 3 = 1 :=
    ((UniversalCover.scalar_mem_special_iff J u).mp (hu ▸ (y ^ 3).property)).2
  have hu1 : u ≠ 1 := by
    intro he
    apply hne
    apply Subtype.ext
    rw [← hu, he, map_one]
    rfl
  have hqu : 3 ∣ q + 1 := by
    have hm := (UniversalCover.scalar_mem_special_iff J u).mp (hu ▸ (y ^ 3).property)
    have hpow : u ^ (q + 1) = 1 := by
      apply Units.ext
      simpa only [hconj, ← pow_succ, Units.val_pow_eq_pow_val, Units.val_one] using hm.1
    have horder : orderOf u = 3 := orderOf_eq_prime hu3 hu1
    exact horder ▸ orderOf_dvd_of_pow_eq_one hpow
  exact unitary_scalar_centralizer_rank J q hcard hconj hfixed hqu y u hu3 hu1 hu.symm

/-- An outside order-three element cannot act inner on the original SU₃
cover when the ambient three-rank is at most two. -/
theorem not_inner_of_unitary_cover {G : Type*} [Group G] [Finite G]
    [Finite F] (K : Subgroup G) [K.Normal]
    (hz : Nat.card (center K) = 3) (hrK : 1 < primeRank 3 K)
    (hr : primeRank 3 G ≤ 2) (J : HermitianForm 3 F) (q : ℕ)
    (hq : Chapter1.Section02.LocalModels.CoverParameter true q)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    (e : K ≃* J.specialSubgroup)
    (x : G) (hx : orderOf x = 3) (hxK : x ∉ K) :
    (MulAut.conjNormal x : MulAut K) ∉ MulAut.innerSubgroup K := by
  intro hi
  obtain ⟨y, _, _, hyc, hy3, hbound⟩ := exists_nine_implementer K hz hrK hr x hx hxK hi
  have hc : (e y) ^ 3 ∈ center J.specialSubgroup := by
    apply mem_center_iff.mpr
    intro w
    obtain ⟨v, rfl⟩ := e.surjective w
    simpa only [map_mul, map_pow] using congrArg e (mem_center_iff.mp hyc v)
  have hn : (e y) ^ 3 ≠ 1 := by
    intro he
    apply hy3
    apply e.injective
    rwa [map_pow, map_one]
  have hh := unitary_centralizer_rank J q hq hcard hconj (e y) hc hn
  rw [← primeRank_congr 3
    (CentralizerSmallKernelTransport.centralizerEquiv e y)] at hh
  omega

end CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.NormalSplitPrime.CoverInner
