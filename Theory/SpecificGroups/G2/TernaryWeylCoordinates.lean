module
public import Theory.SpecificGroups.G2.TernaryCubicFormNormalization

/-!
# Simultaneous Weyl and cubic coordinates for the ternary G₂ module

A linear Weyl involution preserving the commutator radical is constrained by
(UW)⁴ = -I. On the two-dimensional quotient, six possible matrices reduce to
the coordinate swap, up to sign and conjugation by a cubic power. Its action
on the radical then has the required sign, and an explicit three-parameter
change removes the remaining entries. These changes commute with U and
preserve the original alternating form and opposite derived line.

All finite checks concern two-by-two matrices or at most four ternary
parameters. The rest uses structural matrix identities. The only final sign
is realized by the determinant automorphism of GL₂(3), which fixes both
the cubic and scalar involution. TernaryEndpointCoordinates uses this to
identify the whole action; G2Recognition.MaximalWeylCoordinates discharges
the hypotheses on the original cores in Aschbacher–Smith I.4.5, p.417.
The literal root conventions retain LICENSES/ATLAS-CITATION.cff and
LICENSES/ATLAS.txt from the imported Atlas model.
-/

open Matrix
namespace Atlas.G2.TernaryCore
private abbrev M4 := Matrix (Fin 4) (Fin 4) (ZMod 3)
private abbrev M2 := Matrix (Fin 2) (Fin 2) (ZMod 3)
private def u : M4 := !![1,0,0,-1;0,1,1,1;0,0,1,-1;0,0,0,1]
private def w : M4 := !![0,0,0,1;0,0,1,0;0,1,0,0;1,0,0,0]
private def plane (A : M4) : Prop := A 0 1=0 ∧ A 0 2=0 ∧ A 3 1=0 ∧ A 3 2=0
private def q (A : M4) : M2 := !![A 0 0,A 0 3;A 3 0,A 3 3]
private def r (A : M4) : M2 := !![A 1 1,A 1 2;A 2 1,A 2 2]
private theorem plane_mul {A B : M4} (hA : plane A) (hB : plane B) : plane (A*B) := by
  rcases hA with ⟨h01,h02,h31,h32⟩
  rcases hB with ⟨g01,g02,g31,g32⟩
  simp [plane,Matrix.mul_apply,Fin.sum_univ_four,h01,h02,h31,h32,g01,g02,g31,g32]
private theorem q_mul {A B : M4} (hA : plane A) : q (A*B)=q A*q B := by
  rcases hA with ⟨h01,h02,h31,h32⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [q,Matrix.mul_apply,Fin.sum_univ_four,Fin.sum_univ_two,h01,h02,h31,h32]
private theorem r_mul {A B : M4} (hB : plane B) : r (A*B)=r A*r B := by
  rcases hB with ⟨h01,h02,h31,h32⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [r,Matrix.mul_apply,Fin.sum_univ_four,Fin.sum_univ_two,h01,h02,h31,h32]
private instance (A : M4) : Decidable (plane A) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))
private theorem plane_pow {A : M4} (hA : plane A) (n : ℕ) : plane (A^n) := by
  induction n with
  | zero => simp only [pow_zero]; decide
  | succ n ih => exact plane_mul ih hA
private theorem q_pow {A : M4} (hA : plane A) (n : ℕ) : q (A^n)=(q A)^n := by
  induction n with
  | zero => simp only [pow_zero]; decide
  | succ n ih => rw [pow_succ,q_mul (plane_pow hA n),ih,pow_succ]
private theorem r_pow {A : M4} (hA : plane A) (n : ℕ) : r (A^n)=(r A)^n := by
  induction n with
  | zero => simp only [pow_zero]; decide
  | succ n ih => rw [pow_succ,r_mul hA,ih,pow_succ]

private def shift (k : ZMod 3) : M4 :=
  !![1,0,0,-k;0,1,k,k*k;0,0,1,-k;0,0,0,1]
private def swap2 : M2 := !![0,1;1,0]
private theorem quotient_normalize : ∀ A : M2,
    A^2=1 → (!![1,-1;0,1]*A)^4=-1 →
    ∃ k c : ZMod 3,c*c=1 ∧
      c • (!![1,-k;0,1]*A*!![1,k;0,1])=swap2 := by decide +kernel

private def canonical (a c p z : ZMod 3) : M4 :=
  !![0,0,0,1;
     p,a,(1-a*a)*c,-a*p-(1-a*a)*c*z;
     z,c,-a,-c*p+a*z;
     1,0,0,0]
private theorem radical_shape : ∀ A : M2,
    A^2=1 → (!![1,1;0,1]*A)^4=-1 →
    ∃ a c : ZMod 3,c*c=1 ∧ A=!![a,(1-a*a)*c;c,-a] := by decide +kernel

private theorem canonical_sign : ∀ a c p z : ZMod 3,
    c*c=1 → (u*canonical a c p z)^4=-1 → c=1 := by decide +kernel

private theorem canonical_of_quotient_swap (A : M4) (hplane : plane A)
    (hq : q A=swap2) (h2 : A^2=1) (h4 : (u*A)^4=-1) :
    ∃ a p z : ZMod 3,A=canonical a 1 p z := by
  have hu : plane u := ⟨rfl,rfl,rfl,rfl⟩
  have hR2 : (r A)^2=1 := by rw [←r_pow hplane,h2]; decide
  have hR4 : (!![1,1;0,1]*r A)^4=-1 := by
    have hh := congrArg r h4
    rw [r_pow (plane_mul hu hplane),r_mul hplane] at hh
    rw [show r u=!![1,1;0,1] from rfl,show r (-1)=-1 from by decide] at hh
    exact hh
  obtain ⟨a,c,hc,hr⟩ := radical_shape (r A) hR2 hR4
  have h00 := congrArg (fun B : M2=>B 0 0) hq
  have h03 := congrArg (fun B : M2=>B 0 1) hq
  have h30 := congrArg (fun B : M2=>B 1 0) hq
  have h33 := congrArg (fun B : M2=>B 1 1) hq
  have h11 := congrArg (fun B : M2=>B 0 0) hr
  have h12 := congrArg (fun B : M2=>B 0 1) hr
  have h21 := congrArg (fun B : M2=>B 1 0) hr
  have h22 := congrArg (fun B : M2=>B 1 1) hr
  change A 0 0=0 at h00
  change A 0 3=1 at h03
  change A 3 0=1 at h30
  change A 3 3=0 at h33
  change A 1 1=a at h11
  change A 1 2=(1-a*a)*c at h12
  change A 2 1=c at h21
  change A 2 2= -a at h22
  rcases hplane with ⟨h01,h02,h31,h32⟩
  have h13 := congrArg (fun B : M4=>B 1 0) h2
  have h23 := congrArg (fun B : M4=>B 2 0) h2
  simp only [pow_two,Matrix.mul_apply,Fin.sum_univ_four,h00,h30,h11,h12,h21,h22,
    mul_zero,zero_add,mul_one,Matrix.one_apply,show (1:Fin 4)≠0 from by decide,
    show (2:Fin 4)≠0 from by decide,ite_false] at h13 h23
  have he : A=canonical a c (A 1 0) (A 2 0) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [canonical,h00,h01,h02,h03,h30,h31,h32,h33,h11,h12,h21,h22]
    · linear_combination h13
    · linear_combination h23
  have hc1 : c=1 := canonical_sign a c (A 1 0) (A 2 0) hc (he ▸ h4)
  exact ⟨a,A 1 0,A 2 0,hc1 ▸ he⟩

private def adjustment (a p z : ZMod 3) : M4 :=
  !![1,0,0,0;-z-a,1,-a,a*z-p;0,0,1,z-a;0,0,0,1]

private theorem adjustment_root : ∀ a p z : ZMod 3,
    adjustment a p z*u=u*adjustment a p z := by decide +kernel
private theorem adjustment_weyl : ∀ a p z : ZMod 3,
    adjustment a p z*canonical a 1 p z=w*adjustment a p z := by decide +kernel
private theorem shift_inverse : ∀ k : ZMod 3,shift k*shift (-k)=1 := by decide +kernel
private theorem shift_root : ∀ k : ZMod 3,shift k*u=u*shift k := by decide +kernel

private theorem conjugate_pow (S T A : M4) (hST : S*T=1) (hTS : T*S=1) (n : ℕ) :
    (S*A*T)^n=S*A^n*T := by
  induction n with
  | zero => simp [hST]
  | succ n ih =>
    rw [pow_succ,ih,pow_succ]
    calc
      _=S*A^n*(T*S)*A*T := by simp only [mul_assoc]
      _=S*(A^n*A)*T := by rw [hTS]; simp only [mul_assoc,one_mul]

private theorem matrix_normalization (A : M4) (hplane : plane A)
    (h2 : A^2=1) (h4 : (u*A)^4=-1) :
    ∃ k c a p z : ZMod 3,c*c=1 ∧
      (adjustment a p z*shift k)*A=c • (w*(adjustment a p z*shift k)) := by
  have hu : plane u := ⟨rfl,rfl,rfl,rfl⟩
  have hQ2 : (q A)^2=1 := by rw [←q_pow hplane,h2]; decide
  have hQ4 : (!![1,-1;0,1]*q A)^4=-1 := by
    have hh := congrArg q h4
    rw [q_pow (plane_mul hu hplane),q_mul hu] at hh
    rw [show q u=!![1,-1;0,1] from rfl,show q (-1)=-1 from by decide] at hh
    exact hh
  obtain ⟨k,c,hc,hq⟩ := quotient_normalize (q A) hQ2 hQ4
  let S := shift k
  let T := shift (-k)
  have hST : S*T=1 := shift_inverse k
  have hTS : T*S=1 := by simpa only [neg_neg] using shift_inverse (-k)
  have hS : plane S := ⟨rfl,rfl,rfl,rfl⟩
  have hT : plane T := ⟨rfl,rfl,rfl,rfl⟩
  have hconj : u*(S*A*T)=S*(u*A)*T := by
    change u*(shift k*A*T)=shift k*(u*A)*T
    rw [←mul_assoc,←mul_assoc,←shift_root]
    simp only [mul_assoc]
  let B := c • (S*A*T)
  have hBplane : plane B := by
    have hh := plane_mul (plane_mul hS hplane) hT
    rcases hh with ⟨h01,h02,h31,h32⟩
    simp [plane,B,h01,h02,h31,h32]
  have hBq : q B=swap2 := by
    have hsmul : q B=c • q (S*A*T) := by ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hsmul,q_mul (plane_mul hS hplane),q_mul hS]
    have hs : q S=!![1,-k;0,1] := rfl
    have ht : q T=!![1,k;0,1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [q,T,shift]
    rw [hs,ht]
    exact hq
  have hB2 : B^2=1 := by
    change (c • (S*A*T))^2=1
    rw [smul_pow,conjugate_pow S T A hST hTS,h2,mul_one,hST,pow_two,hc,one_smul]
  have hc4 : c^4=1 := by rw [show 4=2*2 from rfl,pow_mul,pow_two c,hc,one_pow]
  have hB4 : (u*B)^4=-1 := by
    change (u*(c • (S*A*T)))^4=-1
    rw [mul_smul_comm,hconj,smul_pow,hc4,one_smul,
      conjugate_pow S T (u*A) hST hTS,h4,mul_neg_one,neg_mul,hST]
  obtain ⟨a,p,z,hB⟩ := canonical_of_quotient_swap B hBplane hBq hB2 hB4
  have hn := adjustment_weyl a p z
  rw [←hB] at hn
  have hh := congrArg (fun X : M4=>c • (X*S)) hn
  change c • ((adjustment a p z*(c • (S*A*T)))*S)=_ at hh
  rw [mul_smul_comm,smul_mul_assoc,smul_smul,hc,one_smul] at hh
  have he : (adjustment a p z*(S*A*T))*S=(adjustment a p z*S)*A := by
    calc
      _=(adjustment a p z*S)*A*(T*S) := by simp only [mul_assoc]
      _=_ := by rw [hTS,mul_one]
  rw [he] at hh
  exact ⟨k,c,a,p,z,hc,by simpa only [mul_assoc] using hh⟩

private abbrev W := Fin 4 → ZMod 3
private def linear (f : V →* V) : W →ₗ[ZMod 3] W :=
  ({ toFun := fun x => (f (Multiplicative.ofAdd x)).toAdd
     map_zero' := congrArg Multiplicative.toAdd f.map_one
     map_add' := fun x y => congrArg Multiplicative.toAdd (f.map_mul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)) } : W →+ W).toZModLinearMap 3
private def mat (f : V →* V) : M4 := LinearMap.toMatrix' (linear f)
private theorem mat_apply (f : V →* V) (v : V) :
    mat f *ᵥ v.toAdd=(f v).toAdd := by
  exact LinearMap.toMatrix'_mulVec (linear f) v.toAdd
private theorem mat_mul (f g : V →* V) : mat (f.comp g)=mat f*mat g := by
  rw [mat,show linear (f.comp g)=(linear f).comp (linear g) from by ext; rfl]
  exact LinearMap.toMatrix'_comp (linear f) (linear g)
private theorem mat_ext (f g : V →* V) (h : mat f=mat g) : f=g := by
  apply MonoidHom.ext
  intro v
  apply Multiplicative.toAdd.injective
  rw [←mat_apply,←mat_apply,h]

private def shiftEquiv (k : ZMod 3) : V ≃* V where
  toFun v := Multiplicative.ofAdd ![v.toAdd 0-k*v.toAdd 3,
    v.toAdd 1+k*v.toAdd 2+k*k*v.toAdd 3,v.toAdd 2-k*v.toAdd 3,v.toAdd 3]
  invFun v := Multiplicative.ofAdd ![v.toAdd 0+k*v.toAdd 3,
    v.toAdd 1-k*v.toAdd 2+k*k*v.toAdd 3,v.toAdd 2+k*v.toAdd 3,v.toAdd 3]
  left_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
    all_goals ring_nf
    all_goals reduce_mod_char
  right_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
    all_goals ring_nf
    all_goals reduce_mod_char
  map_mul' v z := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp <;> ring

private def adjustmentEquiv (a p z : ZMod 3) : V ≃* V where
  toFun v := Multiplicative.ofAdd ![v.toAdd 0,
    (-z-a)*v.toAdd 0+v.toAdd 1-a*v.toAdd 2+(a*z-p)*v.toAdd 3,
    v.toAdd 2+(z-a)*v.toAdd 3,v.toAdd 3]
  invFun v := Multiplicative.ofAdd ![v.toAdd 0,
    (z+a)*v.toAdd 0+v.toAdd 1+a*v.toAdd 2+(a*a+a*z+p)*v.toAdd 3,
    v.toAdd 2-(z-a)*v.toAdd 3,v.toAdd 3]
  left_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
    all_goals ring_nf
    all_goals reduce_mod_char
  right_inv v := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp
    all_goals ring_nf
    all_goals reduce_mod_char
  map_mul' v z := by
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i <;> simp <;> ring

private theorem mat_shift (k : ZMod 3) : mat (shiftEquiv k).toMonoidHom=shift k := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mat,linear,LinearMap.toMatrix'_apply,shiftEquiv,shift]
private theorem mat_adjustment (a p z : ZMod 3) :
    mat (adjustmentEquiv a p z).toMonoidHom=adjustment a p z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mat,linear,LinearMap.toMatrix'_apply,adjustmentEquiv,adjustment]



private def matAction : MulAut V →* M4 where
  toFun f := mat f.toMonoidHom
  map_one' := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    exact (mat_apply (1 : MulAut V).toMonoidHom (Multiplicative.ofAdd v)).trans (Matrix.one_mulVec v).symm
  map_mul' f g := mat_mul f.toMonoidHom g.toMonoidHom

private theorem u_apply (v : V) : u*ᵥv.toAdd=(shortRoot v).toAdd := by
  ext i
  fin_cases i <;> simp [u,shortRoot,Matrix.mulVec, dotProduct,Fin.sum_univ_four,sub_eq_add_neg]
private theorem w_apply (v : V) : w*ᵥv.toAdd=(shortWeyl v).toAdd := by
  ext i
  fin_cases i <;> simp [w,shortWeyl,Matrix.mulVec, dotProduct,Fin.sum_univ_four]

private theorem generators_square : TernaryLevi.generator true^2=1 := by decide +kernel
private theorem generators_product_four :
    (TernaryLevi.generator false*TernaryLevi.generator true)^4=-1 := by decide +kernel

/-- A Weyl action extending the fixed cubic has simultaneous form-preserving
coordinates. The only possible remaining sign is a determinant twist of GL₂(3). -/
public theorem exists_shortWeyl_normalization
    (ρ : TernaryLevi.GL23 →* MulAut V)
    (hroot : ∀ v,ρ (TernaryLevi.generator false) v=shortRoot v)
    (hcentral : ∀ v,ρ (-1) v=v⁻¹)
    (hplane : ∀ v,v.toAdd 0=0 → v.toAdd 3=0 →
      (ρ (TernaryLevi.generator true) v).toAdd 0=0 ∧
      (ρ (TernaryLevi.generator true) v).toAdd 3=0) :
    ∃ (e : V ≃* V) (c : ZMod 3),c*c=1 ∧
      (∀ v,e (shortRoot v)=shortRoot (e v)) ∧
      (∀ v,(e (ρ (TernaryLevi.generator true) v)).toAdd=c • (shortWeyl (e v)).toAdd) ∧
      (∀ v z,shortForm (e v) (e z)=shortForm v z) ∧
      (∀ v,(e v).toAdd 0=0 ∧ (e v).toAdd 2=0 ∧ (e v).toAdd 3=0 ↔
        v.toAdd 0=0 ∧ v.toAdd 2=0 ∧ v.toAdd 3=0) := by
  let R := matAction.comp ρ
  have hU : R (TernaryLevi.generator false)=u := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    change mat (ρ (TernaryLevi.generator false)).toMonoidHom*ᵥv=_
    exact (mat_apply (ρ (TernaryLevi.generator false)).toMonoidHom (Multiplicative.ofAdd v)).trans
      ((congrArg Multiplicative.toAdd (hroot (Multiplicative.ofAdd v))).trans
        (u_apply (Multiplicative.ofAdd v)).symm)
  have hC : R (-1)=-1 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    change mat (ρ (-1)).toMonoidHom*ᵥv=_
    exact (mat_apply (ρ (-1)).toMonoidHom (Multiplicative.ofAdd v)).trans
      ((congrArg Multiplicative.toAdd (hcentral (Multiplicative.ofAdd v))).trans
        (by simp only [Matrix.neg_mulVec,Matrix.one_mulVec,toAdd_inv,toAdd_ofAdd]))
  let A := R (TernaryLevi.generator true)
  have hA2 : A^2=1 := by rw [←map_pow,generators_square,map_one]
  have hA4 : (u*A)^4=-1 := by rw [←hU,←map_mul,←map_pow,generators_product_four,hC]
  have hAplane : plane A := by
    have h1 := hplane (Multiplicative.ofAdd (Pi.single 1 1)) (by simp) (by simp)
    have h2 := hplane (Multiplicative.ofAdd (Pi.single 2 1)) (by simp) (by simp)
    have hm (i j : Fin 4) : A i j=(ρ (TernaryLevi.generator true)
        (Multiplicative.ofAdd (Pi.single j 1))).toAdd i := by
      have hh := congrArg (fun v : W=>v i) (mat_apply (ρ (TernaryLevi.generator true)).toMonoidHom
        (Multiplicative.ofAdd (Pi.single j 1)))
      change (A*ᵥ(Pi.single j 1)) i=_ at hh
      rw [Matrix.mulVec_single_one] at hh
      exact hh
    exact ⟨hm 0 1 ▸ h1.1,hm 0 2 ▸ h2.1,hm 3 1 ▸ h1.2,hm 3 2 ▸ h2.2⟩
  obtain ⟨k,c,a,p,z,hc,hm⟩ := matrix_normalization A hAplane hA2 hA4
  let e := (shiftEquiv k).trans (adjustmentEquiv a p z)
  have he : mat e.toMonoidHom=adjustment a p z*shift k := by
    change mat ((adjustmentEquiv a p z).toMonoidHom.comp (shiftEquiv k).toMonoidHom)=_
    rw [mat_mul,mat_adjustment,mat_shift]
  have heU : (mat e.toMonoidHom)*u=u*mat e.toMonoidHom := by
    rw [he,mul_assoc,shift_root,←mul_assoc,adjustment_root,mul_assoc]
  refine ⟨e,c,hc,?_,?_,?_,?_⟩
  · intro v
    apply Multiplicative.toAdd.injective
    calc
      _ = mat e.toMonoidHom*ᵥ(shortRoot v).toAdd := (mat_apply e.toMonoidHom (shortRoot v)).symm
      _ = mat e.toMonoidHom*ᵥ(u*ᵥv.toAdd) := congrArg (mat e.toMonoidHom*ᵥ·) (u_apply v).symm
      _ = (mat e.toMonoidHom*u)*ᵥv.toAdd := Matrix.mulVec_mulVec _ _ _
      _ = (u*mat e.toMonoidHom)*ᵥv.toAdd := congrArg (·*ᵥv.toAdd) heU
      _ = u*ᵥ(mat e.toMonoidHom*ᵥv.toAdd) := (Matrix.mulVec_mulVec _ _ _).symm
      _ = u*ᵥ(e v).toAdd := congrArg (u*ᵥ·) (mat_apply e.toMonoidHom v)
      _ = _ := u_apply (e v)
  · intro v
    have hh := congrArg (fun B : M4=>B*ᵥv.toAdd) hm
    rw [←he,←Matrix.mulVec_mulVec,Matrix.smul_mulVec,←Matrix.mulVec_mulVec,
      mat_apply,w_apply] at hh
    change mat e.toMonoidHom*ᵥ(mat (ρ (TernaryLevi.generator true)).toMonoidHom*ᵥv.toAdd)=_ at hh
    rw [mat_apply,mat_apply] at hh
    exact hh
  · intro v v'
    change shortForm (adjustmentEquiv a p z (shiftEquiv k v))
      (adjustmentEquiv a p z (shiftEquiv k v'))=shortForm v v'
    simp [shortForm,adjustmentEquiv,shiftEquiv]
    ring
  · intro v
    change (shiftEquiv k v).toAdd 0=0 ∧
      (shiftEquiv k v).toAdd 2+(z-a)*(shiftEquiv k v).toAdd 3=0 ∧
      (shiftEquiv k v).toAdd 3=0 ↔ _
    change v.toAdd 0-k*v.toAdd 3=0 ∧
      v.toAdd 2-k*v.toAdd 3+(z-a)*v.toAdd 3=0 ∧ v.toAdd 3=0 ↔ _
    constructor
    · rintro ⟨h0,h2,h3⟩
      exact ⟨by simpa only [h3,mul_zero,sub_zero] using h0,
        by simpa only [h3,mul_zero,sub_zero,add_zero] using h2,h3⟩
    · rintro ⟨h0,h2,h3⟩
      simp [h0,h2,h3]
end Atlas.G2.TernaryCore

namespace Atlas.G2.TernaryLevi
private theorem central_matrix : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 3),
    A*A=1 → A≠1 → A*(generator false).val=(generator false).val*A →
    A*(generator true).val=(generator true).val*A → A= -1 := by decide +kernel
/-- The scalar involution is characterized within the actual two-generator actor. -/
public theorem eq_central_of_commuting_generators (a : GL23)
    (h2 : a*a=1) (hne : a≠1) (hU : a*generator false=generator false*a)
    (hW : a*generator true=generator true*a) : a=-1 := by
  apply Units.ext
  exact central_matrix a.val (congrArg Units.val h2) (fun h=>hne (Units.ext h))
    (congrArg Units.val hU) (congrArg Units.val hW)

/-- Every actor re-marking retains the scalar involution. -/
public theorem mulEquiv_central (κ : GL23 ≃* GL23) : κ (-1)=-1 := by
  apply eq_central_of_commuting_generators
  · rw [←map_mul,neg_mul_neg,one_mul,map_one]
  · intro h
    have hh := κ.injective (h.trans κ.map_one.symm)
    exact (by decide : (-1:GL23)≠1) hh
  · obtain ⟨a,ha⟩ := κ.surjective (generator false)
    rw [←ha,←map_mul,←map_mul]
    congr 1
    simp
  · obtain ⟨a,ha⟩ := κ.surjective (generator true)
    rw [←ha,←map_mul,←map_mul]
    congr 1
    simp
end Atlas.G2.TernaryLevi


namespace Atlas.G2.TernaryLevi
private def twist (a : GL23) : GL23 :=
  Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det a)*a
private theorem twist_val (a : GL23) : (twist a).val=a.val.det • a.val := by
  change (Matrix.scalar (Fin 2) a.val.det)*a.val=_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
private theorem twist_involutive (a : GL23) : twist (twist a)=a := by
  apply Units.ext
  have hh : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 3),A.det≠0 →
      (A.det • A).det • (A.det • A)=A := by decide +kernel
  rw [twist_val,twist_val]
  exact hh a.val (Units.ne_zero (Matrix.GeneralLinearGroup.det a))
private theorem twist_mul (a b : GL23) : twist (a*b)=twist a*twist b := by
  have hs : Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det b)∈
      Subgroup.center GL23 := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨_,rfl⟩
  have hc := Subgroup.mem_center_iff.mp hs a
  dsimp only [twist]
  rw [map_mul,map_mul]
  calc
    _=Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det a)*
        (Matrix.GeneralLinearGroup.scalar (Fin 2) (Matrix.GeneralLinearGroup.det b)*a)*b := by
      simp only [mul_assoc]
    _=_ := by rw [←hc]; simp only [mul_assoc]
public def determinantTwist : GL23 ≃* GL23 where
  toFun := twist
  invFun := twist
  left_inv := twist_involutive
  right_inv := twist_involutive
  map_mul' := twist_mul
public theorem determinantTwist_root : determinantTwist (generator false)=generator false := by decide +kernel
public theorem determinantTwist_weyl : determinantTwist (generator true)=(-1)*generator true := by decide +kernel
public theorem determinantTwist_central : determinantTwist (-1)=-1 := by decide +kernel
end Atlas.G2.TernaryLevi

