module
public import Theory.LinearAlgebra.CubicSingerCentralizer
public import Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant.Adjoint
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Cubic Singer centralizers in special unitary groups

For a nonsplit scalar-cube unitary matrix over a field of order q²,
the generated cubic field has order q⁶. Its Hermitian adjoint is the
q³-power map: this is checked on the coefficients and the original cubic
root, then extended across the generated algebra. Unitarity and determinant
one are therefore the two power equations whose intersection is precisely
the (q²−q+1)-st roots of unity. This gives both cyclicity and exact order
for the centralizer of the supplied matrix, with its original Hermitian form.

Source: the Singer calculation in Aschbacher–Smith A.3.18, printed p.53.
-/

@[expose] public noncomputable section
open Matrix Polynomial Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.SU3.BinaryPRegularClasses.CentralizerDeterminant
namespace Matrix.UnitarySinger
variable {F : Type*} [Field F]

theorem end_cube (g : GL (Fin 3) F) (z : F)
    (hc : g.val^3=Matrix.scalar (Fin 3) z) :
    (Matrix.toLin' g.val)^3=algebraMap F _ z := by
  change (Matrix.toLinAlgEquiv' g.val)^3 = _
  rw [←map_pow,hc]
  rw [show Matrix.scalar (Fin 3) z = algebraMap F _ z by rfl]
  exact (Matrix.toLinAlgEquiv' (R := F)).commutes z

def matrixAction (g : GL (Fin 3) F) (z : F)
    (hc : g.val^3=Matrix.scalar (Fin 3) z) :
    AdjoinRoot (CubicSinger.polynomial z) →ₐ[F] Matrix (Fin 3) (Fin 3) F :=
  Matrix.toLinAlgEquiv'.symm.toAlgHom.comp
    (CubicSinger.action (Matrix.toLin' g.val) z (end_cube g z hc))

theorem matrixAction_root (g : GL (Fin 3) F) (z : F)
    (hc : g.val^3=Matrix.scalar (Fin 3) z) :
    matrixAction g z hc (AdjoinRoot.root (CubicSinger.polynomial z))=g.val := by
  apply Matrix.toLinAlgEquiv'.injective
  simp only [matrixAction,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,AlgEquiv.apply_symm_apply]
  exact CubicSinger.action_root _ _ _

theorem matrixAction_det (g : GL (Fin 3) F) (z : F)
    (hc : g.val^3=Matrix.scalar (Fin 3) z) (hn : ∀ a : F, a^3≠z)
    (b : AdjoinRoot (CubicSinger.polynomial z)) :
    (matrixAction g z hc b).det=Algebra.norm F b := by
  rw [←LinearMap.det_toLin']
  change LinearMap.det (Matrix.toLinAlgEquiv' (matrixAction g z hc b))=_
  simp only [matrixAction,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,AlgEquiv.apply_symm_apply]
  exact CubicSinger.action_det _ _ _ hn (by simp) b

private theorem cubic_factor {q : ℕ} (hq : 1<q) :
    (q+1)*(q^2-q+1)=q^3+1 := by
  have h := Nat.sub_add_cancel (show q≤q^2 by nlinarith)
  nlinarith

private theorem adjoin_adjoint (J : HermitianForm 3 F) (P : F[X])
    (φ : AdjoinRoot P →ₐ[F] Matrix (Fin 3) (Fin 3) F)
    (τ : AdjoinRoot P →+* AdjoinRoot P)
    (hs : ∀ c : F, J.conjTranspose (φ (algebraMap F _ c))*J.form=
      J.form*φ (τ (algebraMap F _ c)))
    (hr : J.conjTranspose (φ (AdjoinRoot.root P))*J.form=
      J.form*φ (τ (AdjoinRoot.root P)))
    (b : AdjoinRoot P) : J.conjTranspose (φ b)*J.form=J.form*φ (τ b) := by
  have hadd (x y : AdjoinRoot P)
      (hx : J.conjTranspose (φ x)*J.form=J.form*φ (τ x))
      (hy : J.conjTranspose (φ y)*J.form=J.form*φ (τ y)) :
      J.conjTranspose (φ (x+y))*J.form=J.form*φ (τ (x+y)) := by
    have hct : J.conjTranspose (φ x+φ y)=J.conjTranspose (φ x)+J.conjTranspose (φ y) := by
      ext i j; exact map_add J.conj _ _
    rw [map_add,hct,add_mul,hx,hy,map_add,map_add,mul_add]
  have hmul (x y : AdjoinRoot P)
      (hx : J.conjTranspose (φ x)*J.form=J.form*φ (τ x))
      (hy : J.conjTranspose (φ y)*J.form=J.form*φ (τ y)) :
      J.conjTranspose (φ (x*y))*J.form=J.form*φ (τ (x*y)) := by
    have hct : J.conjTranspose (φ x*φ y)=J.conjTranspose (φ y)*J.conjTranspose (φ x) := by
      change ((J.conj : F →+* F).mapMatrix (φ x*φ y)).transpose=_
      rw [map_mul,transpose_mul]; rfl
    rw [map_mul,hct,mul_assoc,hx,←mul_assoc,hy,mul_assoc,←map_mul,←map_mul,mul_comm y x]
  have hb : b∈Algebra.adjoin F ({AdjoinRoot.root P} : Set (AdjoinRoot P)) := by
    rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
  induction hb using Algebra.adjoin_induction with
  | mem x hx => rcases Set.mem_singleton_iff.mp hx with rfl; exact hr
  | algebraMap c => exact hs c
  | add x y hx hy ihx ihy => exact hadd x y ihx ihy
  | mul x y hx hy ihx ihy => exact hmul x y ihx ihy

/-- Hermitian adjoint on the actual cubic field is its middle Frobenius. -/
theorem action_adjoint [Finite F] {p n : ℕ} [Fact p.Prime] [CharP F p]
    (J : HermitianForm 3 F) (hn : 0<n)
    (hcard : Nat.card F=(p^n)^2) (hconj : ∀ x, J.conj x=x^(p^n))
    (hdiv : 3 ∣ p^n+1) (g : J.unitarySubgroup)
    (z : Fˣ) (hz : J.conj (z:F)*z=1)
    (hc : g.val.val^3=Matrix.scalar (Fin 3) (z:F))
    (hnonsplit : ∀ a : F, a^3≠(z:F))
    (b : AdjoinRoot (CubicSinger.polynomial (z:F))) :
    J.conjTranspose (matrixAction g.val z hc b)*J.form =
      J.form*matrixAction g.val z hc (b^((p^n)^3)) := by
  classical
  let q := p^n
  have hq : 1<q := Nat.one_lt_pow hn.ne' (Fact.out : p.Prime).one_lt
  let E := AdjoinRoot (CubicSinger.polynomial (z:F))
  let : Fact (Irreducible (CubicSinger.polynomial (z:F))) :=
    ⟨CubicSinger.irreducible_polynomial (z:F) hnonsplit⟩
  let : Field E := inferInstance
  let : CharP E p := (Algebra.charP_iff F E p).mp inferInstance
  let φ := matrixAction g.val z hc
  let r : E := AdjoinRoot.root (CubicSinger.polynomial (z:F))
  let τ : E →+* E := iterateFrobenius E p (n*3)
  have hτ (x : E) : τ x=x^(q^3) := by change x^(p^(n*3))=_; rw [pow_mul]
  have hτscalar (c : F) : τ (algebraMap F E c)=algebraMap F E (J.conj c) := by
    rw [hτ,←map_pow,hconj]
    have hp : c^(q^3)=c^q := by
      let := Fintype.ofFinite F
      have hh : c^(q^2)=c := by rw [←hcard,Nat.card_eq_fintype_card]; exact FiniteField.pow_card c
      rw [pow_succ, pow_mul,hh]
    rw [hp]
  have hr3 : r^3=algebraMap F E (z:F) := by
    have he := AdjoinRoot.eval₂_root (CubicSinger.polynomial (z:F))
    change (X^3-C (z:F)).eval₂ (AdjoinRoot.of _) (AdjoinRoot.root _)=0 at he
    simpa only [eval₂_sub,eval₂_pow,eval₂_X,eval₂_C,sub_eq_zero,←AdjoinRoot.algebraMap_eq] using he
  have hm : 3 ∣ q^2-q+1 := by
    have hmod : q%3=2 := by have := Nat.mod_eq_zero_of_dvd hdiv; change (q+1)%3=0 at this; omega
    have hsub := Nat.sub_add_cancel (show q≤q^2 by nlinarith)
    have hs : (q^2)%3=1 := by rw [Nat.pow_mod,hmod]
    have he : (q^2-q+1)%3=0 := by omega
    exact Nat.dvd_of_mod_eq_zero he
  have hzq : (z:F)^(q+1)=1 := by rw [pow_succ,←hconj]; exact hz
  have hrpow : r^(q^3+1)=1 := by
    obtain ⟨k,hk⟩ := hm
    rw [←cubic_factor hq,hk,show (q+1)*(3*k)=3*((q+1)*k) by ring,pow_mul,hr3,←map_pow,
      pow_mul,hzq,one_pow,map_one]
  have hroot : J.conjTranspose (φ r)*J.form=J.form*φ (τ r) := by
    have he : φ r=g.val.val := matrixAction_root _ _ _
    have hi : φ (τ r)*g.val.val=1 := by
      rw [←he,←map_mul,hτ,←pow_succ,hrpow,map_one]
    have hi' : φ (τ r)=g.val⁻¹.val := by
      have hh := congrArg (fun M => M*g.val⁻¹.val) hi
      simpa only [mul_assoc,Units.mul_inv,mul_one,one_mul] using hh
    rw [he,hi']
    have hh := congrArg (fun M => M*g.val⁻¹.val) g.property
    simpa only [mul_assoc,Units.mul_inv,mul_one] using hh
  have hscalar (c : F) : J.conjTranspose (φ (algebraMap F E c))*J.form=
      J.form*φ (τ (algebraMap F E c)) := by
    rw [φ.commutes,hτscalar,φ.commutes]
    change J.conjTranspose (Matrix.scalar (Fin 3) c)*J.form=
      J.form*Matrix.scalar (Fin 3) (J.conj c)
    have hct : J.conjTranspose (Matrix.scalar (Fin 3) c)=Matrix.scalar (Fin 3) (J.conj c) := by
      ext i j
      by_cases h : i=j
      · subst j; simp [HermitianForm.conjTranspose,Matrix.scalar_apply]
      · simp [HermitianForm.conjTranspose,Matrix.scalar_apply,h,Ne.symm h]
    rw [hct]
    ext i j
    simp only [Matrix.scalar_apply,Matrix.diagonal_mul,Matrix.mul_diagonal,mul_comm]
  rw [←hτ]
  exact adjoin_adjoint J _ φ τ hscalar hroot b
/-- The unitary condition on cubic-field multiplication is the norm-one power equation. -/
theorem matrixAction_unitary_iff [Finite F] {p n : ℕ} [Fact p.Prime] [CharP F p]
    (J : HermitianForm 3 F) (hn : 0<n)
    (hcard : Nat.card F=(p^n)^2) (hconj : ∀ x, J.conj x=x^(p^n))
    (hdiv : 3 ∣ p^n+1) (g : J.unitarySubgroup)
    (z : Fˣ) (hz : J.conj (z:F)*z=1)
    (hc : g.val.val^3=Matrix.scalar (Fin 3) (z:F))
    (hnonsplit : ∀ a : F, a^3≠(z:F))
    (u : (AdjoinRoot (CubicSinger.polynomial (z:F)))ˣ) :
    Units.map (matrixAction g.val z hc).toMonoidHom u∈J.unitarySubgroup ↔
      u^((p^n)^3+1)=1 := by
  let q := p^n
  let E := AdjoinRoot (CubicSinger.polynomial (z:F))
  let : Fact (Irreducible (CubicSinger.polynomial (z:F))) :=
    ⟨CubicSinger.irreducible_polynomial (z:F) hnonsplit⟩
  let : Field E := inferInstance
  let φ := matrixAction g.val (z:F) hc
  let U : Eˣ →* GL (Fin 3) F := Units.map φ.toMonoidHom
  have hU (u : Eˣ) : (U u).val=φ (u:E) := rfl
  have he := action_adjoint J hn hcard hconj hdiv g z hz hc hnonsplit (u:E)
  have hf : J.conjTranspose (U u).val*J.form*(U u).val=
      J.form*φ ((u:E)^(q^3+1)) := by
    rw [hU,he,mul_assoc,←map_mul,←pow_succ]
  rw [J.mem_unitarySubgroup_iff,hf]
  constructor
  · intro hh
    let Q := GeneralLinearGroup.mkOfDetNeZero J.form J.form_nondegenerate
    have h := congrArg (fun M => Q⁻¹.val*M) hh
    change Q⁻¹.val*(Q.val*φ ((u:E)^(q^3+1)))=Q⁻¹.val*Q.val at h
    simp only [←mul_assoc,Units.inv_mul,one_mul] at h
    apply Units.ext
    exact φ.injective (h.trans φ.map_one.symm)
  · intro hh
    have h := congrArg Units.val hh
    change (u:E)^(q^3+1)=1 at h
    rw [h,map_one,mul_one]

/-- Every invertible operator commuting with the nonsplit cubic is field multiplication. -/
theorem exists_matrixAction (g A : GL (Fin 3) F) (z : F)
    (hc : g.val^3=Matrix.scalar (Fin 3) z) (hn : ∀ a : F, a^3≠z)
    (hA : Commute A g) :
    ∃ u : (AdjoinRoot (CubicSinger.polynomial z))ˣ,
      Units.map (matrixAction g z hc).toMonoidHom u=A := by
  let E := AdjoinRoot (CubicSinger.polynomial z)
  let : Fact (Irreducible (CubicSinger.polynomial z)) := ⟨CubicSinger.irreducible_polynomial z hn⟩
  let : Field E := inferInstance
  let φ := matrixAction g z hc
  let f := Matrix.toLin' g.val
  have hf := end_cube g z hc
  have hh : Commute f (Matrix.toLin' A.val) := by
    have he := congrArg (fun x : GL (Fin 3) F => Matrix.toLin' x.val) hA.eq.symm
    change Matrix.toLinAlgEquiv' (g.val*A.val)=Matrix.toLinAlgEquiv' (A.val*g.val) at he
    rw [map_mul,map_mul] at he
    exact he
  obtain ⟨b,hb⟩ := CubicSinger.action_centralizer f z hf hn (by simp) (Matrix.toLin' A.val) hh
  have hb' : φ b=A.val := by
    apply Matrix.toLinAlgEquiv'.injective
    change Matrix.toLinAlgEquiv' (matrixAction _ _ _ b)=_
    simp only [matrixAction,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,AlgEquiv.apply_symm_apply]
    exact hb
  have hb0 : b≠0 := by
    intro hz
    have he : A.val=0 := by rw [←hb',hz,map_zero]
    exact A.det_ne_zero (by rw [he,det_zero])
  exact ⟨Units.mk0 b hb0,Units.ext hb'⟩

private theorem norm_exponent {q : ℕ} (hq : 1<q) :
    (q^6-1)/(q^2-1)=q^4+q^2+1 := by
  have he : q^6=(q^2-1)*(q^4+q^2+1)+1 := by
    have hq' : q^2=q^2-1+1 := by
      have : 1≤q^2 := by nlinarith
      omega
    calc
      _ = (q^2)^3 := by ring
      _ = (q^2-1+1)^3 := congrArg (fun x : ℕ => x^3) hq'
      _ = (q^2-1)*((q^2-1+1)^2+(q^2-1+1)+1)+1 := by ring
      _ = _ := by rw [←hq']; ring
  have he' : q^6-1=(q^2-1)*(q^4+q^2+1) := by omega
  have hpos : 0<q^2-1 := by
    have : 1<q^2 := by nlinarith
    omega
  rw [he',Nat.mul_div_right _ hpos]

/-- The centralizer of the given nonsplit cubic in SU₃ has the exact Singer order. -/
theorem centralizer [Finite F] {p n : ℕ} [Fact p.Prime] [CharP F p]
    (J : HermitianForm 3 F) (hn : 0<n)
    (hcard : Nat.card F=(p^n)^2) (hconj : ∀ x, J.conj x=x^(p^n))
    (hdiv : 3 ∣ p^n+1) (g : J.unitarySubgroup)
    (z : Fˣ) (hz : J.conj (z:F)*z=1)
    (hc : g.val.val^3=Matrix.scalar (Fin 3) (z:F))
    (hnonsplit : ∀ a : F, a^3≠(z:F)) :
    IsCyclic ((Subgroup.centralizer ({g.val}:Set (GL (Fin 3) F))).comap J.specialSubgroup.subtype) ∧
    Nat.card ((Subgroup.centralizer ({g.val}:Set (GL (Fin 3) F))).comap J.specialSubgroup.subtype)=
      (p^n)^2-p^n+1 := by
  classical
  let q := p^n
  have hq : 1<q := Nat.one_lt_pow hn.ne' (Fact.out : p.Prime).one_lt
  let E := AdjoinRoot (CubicSinger.polynomial (z:F))
  let : Fact (Irreducible (CubicSinger.polynomial (z:F))) :=
    ⟨CubicSinger.irreducible_polynomial (z:F) hnonsplit⟩
  let : Field E := inferInstance
  have hdE : Module.finrank F E=3 := CubicSinger.cubic_finrank (z:F)
  let : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let : Finite E := (Module.finite_iff_finite (R := F) (M := E)).mp inferInstance
  have hE : Nat.card E=q^6 := by
    rw [Module.natCard_eq_pow_finrank (K := F),hdE,hcard]
    dsimp [q]; ring
  let φ := matrixAction g.val (z:F) hc
  let U : Eˣ →* GL (Fin 3) F := Units.map φ.toMonoidHom
  have hU (u : Eˣ) : (U u).val=φ (u:E) := rfl
  have hcomm (u : Eˣ) : Commute (U u) g.val := by
    apply Units.ext
    change φ (u:E)*g.val.val=g.val.val*φ (u:E)
    rw [←matrixAction_root g.val (z:F) hc]
    exact (Commute.all (u:E) _).map φ
  have hunit (u : Eˣ) : U u∈J.unitarySubgroup ↔ u^(q^3+1)=1 := by
    have he := action_adjoint J hn hcard hconj hdiv g z hz hc hnonsplit (u:E)
    have hf : J.conjTranspose (U u).val*J.form*(U u).val=
        J.form*φ ((u:E)^(q^3+1)) := by
      rw [hU,he,mul_assoc,←map_mul,←pow_succ]
    rw [J.mem_unitarySubgroup_iff,hf]
    constructor
    · intro hh
      let Q := GeneralLinearGroup.mkOfDetNeZero J.form J.form_nondegenerate
      have h := congrArg (fun M => Q⁻¹.val*M) hh
      change Q⁻¹.val*(Q.val*φ ((u:E)^(q^3+1)))=Q⁻¹.val*Q.val at h
      simp only [←mul_assoc,Units.inv_mul,one_mul] at h
      apply Units.ext
      exact φ.injective (h.trans φ.map_one.symm)
    · intro hh
      have h := congrArg Units.val hh
      change (u:E)^(q^3+1)=1 at h
      rw [h,map_one,mul_one]
  have hdet (u : Eˣ) : GeneralLinearGroup.det (U u)=1 ↔ u^(q^4+q^2+1)=1 := by
    have he := FiniteField.algebraMap_norm_eq_pow (K := F) (K' := E) (x := (u:E))
    rw [hE,hcard,norm_exponent hq] at he
    constructor
    · intro hh
      have hh' : Algebra.norm F (u:E)=1 := by
        rw [←matrixAction_det g.val (z:F) hc hnonsplit]
        exact congrArg Units.val hh
      rw [hh',map_one] at he
      exact Units.ext he.symm
    · intro hh
      have hh' : Algebra.norm F (u:E)=1 := (algebraMap F E).injective (by
        rw [he,map_one]
        exact congrArg Units.val hh)
      apply Units.ext
      exact (matrixAction_det g.val (z:F) hc hnonsplit (u:E)).trans hh'
  let m := q^2-q+1
  have hmadd : m+q=q^2+1 := by
    dsimp [m]
    have : q≤q^2 := by nlinarith
    omega
  have hdn : q^4+q^2+1=q*(q^3+1)+m := by nlinarith
  have hnm : q^3+1=(q+1)*m := (cubic_factor hq).symm
  have hdm : q^4+q^2+1=(q^2+q+1)*m := by nlinarith [cubic_factor hq]
  have hspecial (u : Eˣ) : U u∈J.specialSubgroup ↔ u^m=1 := by
    change U u∈J.unitarySubgroup ∧ GeneralLinearGroup.det (U u)=1 ↔ _
    rw [hunit,hdet]
    constructor
    · rintro ⟨h1,h2⟩
      rw [hdn,pow_add,pow_mul',h1,one_pow,one_mul] at h2
      exact h2
    · intro h
      rw [hnm,hdm,pow_mul',pow_mul',h,one_pow,one_pow]
      exact ⟨rfl,rfl⟩
  let N := rootsOfUnity m E
  let C := (Subgroup.centralizer ({g.val}:Set (GL (Fin 3) F))).comap J.specialSubgroup.subtype
  let j : N →* J.specialSubgroup :=
    { toFun := fun u => ⟨U u.val,(hspecial u.val).mpr ((mem_rootsOfUnity _ _).mp u.property)⟩
      map_one' := Subtype.ext (U.map_one)
      map_mul' := fun u v => Subtype.ext (U.map_mul u.val v.val) }
  have hjC (u : N) : j u∈C := mem_centralizer_singleton_iff.mpr (hcomm u.val).eq
  let jC : N →* C := j.codRestrict C hjC
  have hinj : Function.Injective jC := by
    intro u v h
    apply Subtype.ext
    apply Units.ext
    apply φ.injective
    exact congrArg (fun x : C => x.val.val.val) h
  have hsurj : Function.Surjective jC := by
    intro c
    let f := Matrix.toLin' g.val.val
    have hf := end_cube g.val (z:F) hc
    have hh : Commute f (Matrix.toLin' c.val.val.val) := by
      have he := (mem_centralizer_singleton_iff.mp c.property).symm
      have he' := congrArg (fun x : GL (Fin 3) F => Matrix.toLin' x.val) he
      change Matrix.toLinAlgEquiv' (g.val.val*c.val.val.val)=Matrix.toLinAlgEquiv' (c.val.val.val*g.val.val) at he'
      rw [map_mul,map_mul] at he'
      exact he'
    obtain ⟨b,hb⟩ := CubicSinger.action_centralizer f (z:F) hf hnonsplit (by simp)
      (Matrix.toLin' c.val.val.val) hh
    have hb' : φ b=c.val.val.val := by
      apply Matrix.toLinAlgEquiv'.injective
      change Matrix.toLinAlgEquiv' (matrixAction _ _ _ b)=_
      simp only [matrixAction,AlgHom.comp_apply,AlgEquiv.coe_toAlgHom,AlgEquiv.apply_symm_apply]
      exact hb
    have hb0 : b≠0 := by
      intro hz
      have he : c.val.val.val=0 := by rw [←hb',hz,map_zero]
      exact c.val.val.det_ne_zero (by rw [he,det_zero])
    let u := Units.mk0 b hb0
    have hu : U u=c.val.val := Units.ext hb'
    have hum : u∈N := (mem_rootsOfUnity _ _).mpr ((hspecial u).mp (hu ▸ c.val.property))
    refine ⟨⟨u,hum⟩,?_⟩
    apply Subtype.ext
    exact Subtype.ext hu
  let e : N ≃* C := MulEquiv.ofBijective jC ⟨hinj,hsurj⟩
  refine ⟨isCyclic_of_surjective e e.surjective,?_⟩
  rw [←Nat.card_congr e.toEquiv]
  change Nat.card (rootsOfUnity m E)=m
  rw [rootsOfUnity_eq_ker,IsCyclic.card_powMonoidHom_ker,Nat.card_units,hE]
  apply Nat.gcd_eq_right
  have hn : q^3+1 ∣ q^6-1 := by
    have he : q^6-1=(q^3-1)*(q^3+1) := by
      calc
        _ = (q^3)^2-1 := by congr 1; ring
        _ = _ := by simpa only [one_pow,mul_comm] using Nat.sq_sub_sq (q^3) 1
    rw [he]; exact dvd_mul_left _ _
  exact (show m ∣ q^3+1 by rw [hnm]; exact dvd_mul_left _ _).trans hn
end Matrix.UnitarySinger
