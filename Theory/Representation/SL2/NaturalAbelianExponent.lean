module
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Exponent two in abelian extensions of natural SL₂ modules

Two commuting root involutions with distinct nonzero parameters force the
second coordinate of every double to vanish. Their displacements on the
preimage of the common fixed space descend to additive maps H,S satisfying
H(a y)+a H(y)=(a+a²)S(y) and S(a y)=a S(y). Iteration through the odd
multiplicative order of a forces S=0. The Weyl element exchanges the two
coordinates, so every double is zero.

The multiplicative application retains a surjective covering actor, its
kernel action, and the literal natural coordinates. This supplies the
exponent step used in DGS, Groups and Graphs (1985), (5.17), p.117, and
(10.9), p.163, once the natural layers and abelianness have been proved.
No additive splitting or elementary-abelian core is assumed.
-/

noncomputable section
namespace Representation.SL2.NaturalAbelian
variable {F V A : Type*} [Field F] [CharP F 2]
  [AddCommGroup V] [Module F V] [AddCommGroup A]

private theorem scalar_obstruction (a : F) (ha1 : a ≠ 1)
    (m : ℕ) (hm : (m : F) = 1) (ha : a ^ m = 1)
    (H S : V →+ F) (hS : ∀ y, S (a • y) = a * S y)
    (hH : ∀ y, H (a • y) + a * H y = (a+a^2) * S y) : S = 0 := by
  have hSp (n : ℕ) (y : V) : S (a^n • y) = a^n * S y := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ',mul_smul,hS,ih,mul_assoc]
  have hHp (n : ℕ) (y : V) :
      H (a^n • y) = a^n * (H y + (n : F)*(1+a)*S y) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hh := hH (a^n • y)
      rw [←mul_smul,←pow_succ',hSp,ih] at hh
      have he := eq_sub_of_add_eq hh
      rw [he,Nat.cast_succ,pow_succ']
      have hneg : ∀ z : F, -z = z := CharTwo.neg_eq
      simp only [sub_eq_add_neg,hneg]
      ring_nf
  ext y
  have he := hHp m y
  rw [ha,one_smul,one_mul,hm,one_mul] at he
  have hz : (1+a)*S y = 0 := by
    exact add_left_cancel (show H y + (1+a)*S y = H y+0 by simpa using he.symm)
  have hne : 1+a ≠ 0 := by
    intro hh
    have hh' : a = -1 := eq_neg_of_add_eq_zero_right hh
    exact ha1 (hh'.trans (CharTwo.neg_eq _))
  exact (mul_eq_zero.mp hz).resolve_left hne

/-- Coordinates for an abelian extension with two marked root operators. -/
private structure RootData (a : F) where
  incl : F × F →+ A
  proj : A →+ V × V
  inj : Function.Injective incl
  onto : Function.Surjective proj
  exact : ∀ x, proj x = 0 ↔ ∃ v, incl v = x
  u : A →+ A
  v : A →+ A
  u_sq : ∀ x, u (u x) = x
  v_sq : ∀ x, v (v x) = x
  commute : ∀ x, v (u x) = u (v x)
  u_incl : ∀ x y, u (incl (x,y)) = incl (x+y,y)
  v_incl : ∀ x y, v (incl (x,y)) = incl (x+a*y,y)
  u_proj : ∀ x, proj (u x) = ((proj x).1+(proj x).2,(proj x).2)
  v_proj : ∀ x, proj (v x) = ((proj x).1+a • (proj x).2,(proj x).2)

variable {a : F} (d : RootData (V := V) (A := A) a)
omit [CharP F 2] in
private theorem proj_incl (z : F × F) : d.proj (d.incl z) = 0 :=
  (d.exact _).mpr ⟨z,rfl⟩

private def p₂ : A →+ V := (AddMonoidHom.snd V V).comp d.proj
private abbrev L := (p₂ d).ker
private def p₁ : L d →+ V := (AddMonoidHom.fst V V).comp (d.proj.comp (L d).subtype)

omit [CharP F 2] in
private theorem p₁_onto : Function.Surjective (p₁ d) := by
  intro y
  obtain ⟨x,hx⟩ := d.onto (y,0)
  refine ⟨⟨x,show (d.proj x).2=0 from congrArg Prod.snd hx⟩,?_⟩
  exact congrArg Prod.fst hx

private theorem displacement (t : F) (ht : t ≠ 0) (u : A →+ A)
    (hsq : ∀ x, u (u x) = x)
    (hi : ∀ x y, u (d.incl (x,y)) = d.incl (x+t*y,y))
    (hp : ∀ x, d.proj (u x) = ((d.proj x).1+t • (d.proj x).2,(d.proj x).2)) :
    ∃ b : L d →+ F, ∀ x : L d, u x - x = d.incl (b x,0) := by
  have hex (x : L d) : ∃ z : F × F, d.incl z = u x-x := by
    apply (d.exact _).mp
    rw [map_sub,hp]
    have hx : (d.proj (x : A)).2 = 0 := x.property
    ext <;> simp [hx]
  choose b hb using hex
  have hz (x : L d) : (b x).2 = 0 := by
    have hh : u (d.incl (b x)) + d.incl (b x) = 0 := by
      rw [hb,map_sub,hsq]
      abel
    rw [hi,←map_add] at hh
    have he := d.inj (hh.trans d.incl.map_zero.symm)
    have ht0 : t * (b x).2 = 0 := by
      have hh := congrArg Prod.fst he
      change (b x).1+t*(b x).2+(b x).1=0 at hh
      have he : (b x).1+t*(b x).2+(b x).1 = t*(b x).2 := by
        rw [add_right_comm,CharTwo.add_self_eq_zero,zero_add]
      rwa [he] at hh
    exact (mul_eq_zero.mp ht0).resolve_left ht
  have hb' (x : L d) : u x-x = d.incl ((b x).1,0) := by
    rw [←hb]; congr 1; exact Prod.ext rfl (hz x)
  let B : L d →+ F := {
    toFun x := (b x).1
    map_zero' := by
      have hh : d.incl ((b 0).1,0) = d.incl 0 := by rw [←hb']; simp
      exact congrArg Prod.fst (d.inj hh)
    map_add' x y := by
      have hh : d.incl ((b (x+y)).1,0) = d.incl (((b x).1,0)+((b y).1,0)) := by
        rw [←hb',map_add,←hb',←hb']
        change u ((x:A)+(y:A))-((x:A)+(y:A)) = (u x-x)+(u y-y)
        rw [map_add]; abel
      exact congrArg Prod.fst (d.inj hh) }
  exact ⟨B,hb'⟩

/-- Two distinct nonzero root parameters force all doubles into the first kernel line. -/
private theorem double_second_zero (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (m : ℕ) (hm : (m : F) = 1) (ham : a^m = 1) :
    ∀ x : A, ∃ t : F, x+x = d.incl (t,0) := by
  have hex (x : A) : ∃ z : F × F, d.incl z = x+x := by
    apply (d.exact _).mp
    rw [map_add]
    rw [←two_smul F _,CharTwo.two_eq_zero,zero_smul]
  choose D hD using hex
  let D' : A →+ F × F := {
    toFun := D
    map_zero' := d.inj (by rw [hD,map_zero]; simp)
    map_add' x y := d.inj (by rw [hD,map_add,hD,hD]; abel) }
  have hd (x : A) : d.incl (D' x) = x+x := hD x
  have hdi (z : F × F) : D' (d.incl z) = 0 := by
    apply d.inj
    rw [hd,←map_add,CharTwo.add_self_eq_zero,map_zero]
  have hdu (x : A) : D' (d.u x) = ((D' x).1+(D' x).2,(D' x).2) := by
    apply d.inj
    rw [hd,←map_add,←hd,d.u_incl]
  have hdv (x : A) : D' (d.v x) = ((D' x).1+a*(D' x).2,(D' x).2) := by
    apply d.inj
    rw [hd,←map_add,←hd,d.v_incl]
  obtain ⟨bu,hbu⟩ := displacement d 1 one_ne_zero d.u d.u_sq
    (by simpa using d.u_incl) (by simpa using d.u_proj)
  obtain ⟨bv,hbv⟩ := displacement d a ha0 d.v d.v_sq d.v_incl d.v_proj
  let du : A →+ L d := {
    toFun x := ⟨d.u x-x, by change (d.proj (d.u x-x)).2=0; rw [map_sub,d.u_proj]; simp⟩
    map_zero' := by apply Subtype.ext; simp
    map_add' x y := by apply Subtype.ext; simp only [map_add]; change _ = (d.u x-x)+(d.u y-y); abel }
  let dv : A →+ L d := {
    toFun x := ⟨d.v x-x, by change (d.proj (d.v x-x)).2=0; rw [map_sub,d.v_proj]; simp⟩
    map_zero' := by apply Subtype.ext; simp
    map_add' x y := by apply Subtype.ext; simp only [map_add]; change _ = (d.v x-x)+(d.v y-y); abel }
  have hpu (x : A) : p₁ d (du x) = p₂ d x := by
    change (d.proj (d.u x-x)).1 = (d.proj x).2
    rw [map_sub,d.u_proj]; simp
  have hpv (x : A) : p₁ d (dv x) = a • p₂ d x := by
    change (d.proj (d.v x-x)).1 = a • (d.proj x).2
    rw [map_sub,d.v_proj]; simp
  have hDu (x : A) : D' (du x) = ((D' x).2,0) := by
    change D' (d.u x-x) = _
    rw [map_sub,hdu]; ext <;> simp
  have hDv (x : A) : D' (dv x) = (a*(D' x).2,0) := by
    change D' (d.v x-x) = _
    rw [map_sub,hdv]; ext <;> simp
  have hbu_du (x : A) : bu (du x) = (D' x).2 := by
    have hh : d.incl (bu (du x),0) = -d.incl (D' (du x)) := by
      rw [←hbu,hd]
      change d.u (d.u x-x)-(d.u x-x) = -((d.u x-x)+(d.u x-x))
      rw [map_sub,d.u_sq]; abel
    rw [hDu,←map_neg] at hh
    have he := congrArg Prod.fst (d.inj hh)
    simpa only [Prod.fst_neg,CharTwo.neg_eq] using he
  have hbv_dv (x : A) : bv (dv x) = a*(D' x).2 := by
    have hh : d.incl (bv (dv x),0) = -d.incl (D' (dv x)) := by
      rw [←hbv,hd]
      change d.v (d.v x-x)-(d.v x-x) = -((d.v x-x)+(d.v x-x))
      rw [map_sub,d.v_sq]; abel
    rw [hDv,←map_neg] at hh
    have he := congrArg Prod.fst (d.inj hh)
    simpa only [Prod.fst_neg,CharTwo.neg_eq] using he
  have hcross (x : A) : bv (du x) = bu (dv x) := by
    apply_fun (fun t : F => d.incl (t,0)) using
      (fun x y hh => congrArg Prod.fst (d.inj hh))
    change d.incl (bv (du x),0) = d.incl (bu (dv x),0)
    rw [←hbv,←hbu]
    change d.v (d.u x-x)-(d.u x-x) = d.u (d.v x-x)-(d.v x-x)
    rw [map_sub,map_sub,d.commute]; abel
  let C : L d →+ F := bv - a • bu
  have hCker : (p₁ d).ker ≤ C.ker := by
    intro x hx
    have hp : d.proj (x : A) = 0 := Prod.ext hx x.property
    obtain ⟨⟨s,t⟩,he⟩ := (d.exact _).mp hp
    have hbu' : bu x = t := by
      have hh := hbu x
      rw [←he,d.u_incl,←map_sub] at hh
      exact (congrArg Prod.fst (d.inj hh)).symm.trans (by simp)
    have hbv' : bv x = a*t := by
      have hh := hbv x
      rw [←he,d.v_incl,←map_sub] at hh
      exact (congrArg Prod.fst (d.inj hh)).symm.trans (by simp)
    change bv x-a*bu x=0
    rw [hbu',hbv',sub_self]
  let H : V →+ F := (p₁ d).liftOfSurjective (p₁_onto d) ⟨C,hCker⟩
  have hH (x : L d) : H (p₁ d x) = bv x-a*bu x :=
    (p₁ d).liftOfRightInverse_comp_apply _ _ _ x
  let D₂ : A →+ F := (AddMonoidHom.snd F F).comp D'
  have hDker : (p₂ d).ker ≤ D₂.ker := by
    intro x hx
    have hd0 : D' (d.u x-x) = 0 := by
      rw [hbu ⟨x,hx⟩,hdi]
    rw [show d.u x-x = (du x : A) from rfl,hDu] at hd0
    exact congrArg Prod.fst hd0
  have hp₂ : Function.Surjective (p₂ d) := by
    intro y
    obtain ⟨x,hx⟩ := d.onto (0,y)
    exact ⟨x,congrArg Prod.snd hx⟩
  let S : V →+ F := (p₂ d).liftOfSurjective hp₂ ⟨D₂,hDker⟩
  have hS (x : A) : S (p₂ d x) = (D' x).2 :=
    (p₂ d).liftOfRightInverse_comp_apply _ _ _ x
  have hfirst (z : L d) : (D' z).1 = S (p₁ d z) := by
    obtain ⟨x,hx⟩ := hp₂ (p₁ d z)
    have hpr : d.proj ((z : A)-(du x : A)) = 0 := by
      rw [map_sub]
      apply sub_eq_zero.mpr
      apply Prod.ext
      · exact hx.symm.trans (hpu x).symm
      · exact z.property.trans (du x).property.symm
    obtain ⟨y,hy⟩ := (d.exact _).mp hpr
    have hh : D' z = D' (du x) := by
      apply sub_eq_zero.mp
      rw [←map_sub,←hy,hdi]
    rw [hh,hDu,←hS,hx]
  have hSa (y : V) : S (a • y) = a*S y := by
    obtain ⟨x,rfl⟩ := hp₂ y
    rw [←hpv,←hfirst,hDv,hS]
  have hHa (y : V) : H (a • y)+a*H y = (a+a^2)*S y := by
    obtain ⟨x,rfl⟩ := hp₂ y
    rw [←hpv,←hpu,hH,hH,hbv_dv,hbu_du,hcross,hpu,hS]
    rw [sub_eq_add_neg,sub_eq_add_neg,CharTwo.neg_eq,CharTwo.neg_eq]
    ring_nf
    simp [CharTwo.two_eq_zero]
  have hSz := scalar_obstruction a ha1 m hm ham H S hSa hHa
  intro x
  refine ⟨(D' x).1,?_⟩
  rw [←hd]
  congr 1
  apply Prod.ext
  · rfl
  change (D' x).2 = 0
  rw [←hS,hSz,AddMonoidHom.zero_apply]


open Matrix
open scoped MatrixGroups
private def upper (t : F) : SL(2,F) := ⟨!![1,t;0,1],by simp [det_fin_two]⟩
private def swap : SL(2,F) := ⟨!![0,1;1,0],by simp [det_fin_two,CharTwo.neg_eq]⟩
omit [CharP F 2] in
private theorem upper_vec (t x y : F) : (upper t).val *ᵥ ![x,y] = ![x+t*y,y] := by
  ext i; fin_cases i <;> simp [upper,mulVec,dotProduct,Fin.sum_univ_two]
private theorem swap_vec (x y : F) : (swap (F := F)).val *ᵥ ![x,y] = ![y,x] := by
  ext i; fin_cases i <;> simp [swap,mulVec,dotProduct,Fin.sum_univ_two]
omit [CharP F 2] in
private theorem upper_mul (s t : F) : upper s * upper t = upper (s+t) := by
  apply Subtype.ext
  change !![1,s;0,1] * !![1,t;0,1] = !![1,s+t;0,1]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,add_comm]
private theorem upper_sq (t : F) : upper t * upper t = 1 := by
  rw [upper_mul,CharTwo.add_self_eq_zero]
  ext i j; fin_cases i <;> fin_cases j <;> simp [upper]

/-- An abelian extension of natural SL₂ modules with a natural kernel has exponent two
when the finite field is nonbinary. -/
public theorem double_eq_zero [Finite F] {ι : Type*}
    (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (j : (Fin 2 → F) →+ A) (hj : Function.Injective j)
    (p : A →+ (ι → Fin 2 → F)) (hp : Function.Surjective p)
    (hex : ∀ x, p x=0 ↔ ∃ z, j z=x)
    (ρ : Representation ℤ SL(2,F) A)
    (heJ : ∀ g z, ρ g (j z) = j (g.val *ᵥ z))
    (heP : ∀ g x, p (ρ g x) = fun i => g.val *ᵥ (p x i)) :
    ∀ x : A, x+x=0 := by
  let J : F × F →+ A := {
    toFun z := j ![z.1,z.2]
    map_zero' := by
      change j ![0,0]=0
      rw [←j.map_zero]
      congr 1
      ext i; fin_cases i <;> rfl
    map_add' z w := by
      change j ![z.1+w.1,z.2+w.2] = _
      rw [←map_add]
      congr 1
      ext i; fin_cases i <;> rfl }
  let P : A →+ (ι → F) × (ι → F) := {
    toFun x := (fun i => p x i 0,fun i => p x i 1)
    map_zero' := by ext i <;> simp
    map_add' x y := by ext i <;> simp }
  have hJi : Function.Injective J := by
    intro z w hh
    have he := hj hh
    exact Prod.ext (congrFun he 0) (congrFun he 1)
  have hPo : Function.Surjective P := by
    intro z
    obtain ⟨x,hx⟩ := hp (fun i => ![z.1 i,z.2 i])
    refine ⟨x,?_⟩
    apply Prod.ext <;> funext i
    · exact congrFun (congrFun hx i) 0
    · exact congrFun (congrFun hx i) 1
  have hPe (x : A) : P x=0 ↔ ∃ z, J z=x := by
    constructor
    · intro hx
      have hh : p x=0 := by
        funext i b
        fin_cases b
        · exact congrFun (congrArg Prod.fst hx) i
        · exact congrFun (congrArg Prod.snd hx) i
      obtain ⟨z,hz⟩ := (hex x).mp hh
      refine ⟨(z 0,z 1),?_⟩
      change j ![z 0,z 1]=x
      have he : ![z 0,z 1] = z := by ext i; fin_cases i <;> rfl
      rwa [he]
    · rintro ⟨z,hz⟩
      have hh := (hex x).mpr ⟨![z.1,z.2],hz⟩
      change (fun i => p x i 0,fun i => p x i 1)=0
      simp only [hh,Pi.zero_apply]
      rfl
  have hroot (t : F) (x : A) :
      P (ρ (upper t) x) = ((P x).1+t • (P x).2,(P x).2) := by
    apply Prod.ext <;> funext i
    · change p (ρ (upper t) x) i 0 = p x i 0+t*p x i 1
      simp only [heP]
      simp [upper,mulVec,dotProduct,Fin.sum_univ_two]
    · change p (ρ (upper t) x) i 1 = p x i 1
      simp only [heP]
      simp [upper,mulVec,dotProduct,Fin.sum_univ_two]
  let d : RootData (V := ι → F) (A := A) a := {
    incl := J
    proj := P
    inj := hJi
    onto := hPo
    exact := hPe
    u := (ρ (upper 1)).toAddMonoidHom
    v := (ρ (upper a)).toAddMonoidHom
    u_sq := fun x => by
      change (ρ (upper 1) * ρ (upper 1)) x=x
      rw [←map_mul,upper_sq,map_one]; rfl
    v_sq := fun x => by
      change (ρ (upper a) * ρ (upper a)) x=x
      rw [←map_mul,upper_sq,map_one]; rfl
    commute := fun x => by
      change (ρ (upper a)*ρ (upper 1)) x = (ρ (upper 1)*ρ (upper a)) x
      rw [←map_mul,←map_mul,upper_mul,upper_mul,add_comm a 1]
    u_incl := fun x y => by change ρ (upper 1) (j ![x,y]) = j ![x+y,y]; rw [heJ,upper_vec,one_mul]
    v_incl := fun x y => by change ρ (upper a) (j ![x,y]) = j ![x+a*y,y]; rw [heJ,upper_vec]
    u_proj := fun x => by
      change P (ρ (upper 1) x) = _
      simpa only [one_smul] using hroot 1 x
    v_proj := hroot a }
  let := Fintype.ofFinite F
  have hm : ((Fintype.card F-1 : ℕ) : F)=1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Fintype.card F))),FiniteField.cast_card_eq_zero,Nat.cast_one,
      zero_sub,CharTwo.neg_eq]
  have hdouble := double_second_zero d ha0 ha1 (Fintype.card F-1) hm
    (FiniteField.pow_card_sub_one_eq_one a ha0)
  intro x
  obtain ⟨t,ht⟩ := hdouble x
  obtain ⟨s,hs⟩ := hdouble (ρ swap x)
  have hst : j ![s,0] = j ![0,t] := by
    change ρ swap x+ρ swap x = j ![s,0] at hs
    rw [←hs,←map_add,ht]
    exact (heJ swap ![t,0]).trans (congrArg j (swap_vec t 0))
  have ht0 : t=0 := by
    have hh := congrFun (hj hst) 1
    simpa using hh.symm
  rw [ht,ht0]
  exact J.map_zero
end Representation.SL2.NaturalAbelian

open Matrix Subgroup
open scoped IsMulCommutative MatrixGroups
namespace Representation.SL2
variable {F Q X : Type*} [Field F] [Finite F] [CharP F 2]
  [Group Q] [IsMulCommutative Q] [Group X]

/-- The exponent obstruction with the original covering actor and multiplicative coordinates. -/
public theorem square_eq_one_of_natural_abelian_extension {n : ℕ}
    (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (f : Q →* Multiplicative (Fin n → Fin 2 → F)) (hf : Function.Surjective f)
    (z : f.ker →* Multiplicative (Fin 2 → F)) (hz : Function.Bijective z)
    (π : X →* SL(2,F)) (hπ : Function.Surjective π)
    (φ : X →* MulAut Q) (hkill : π.ker ≤ φ.ker)
    (he : ∀ a x, (f (φ a x)).toAdd = fun i => (π a).val *ᵥ (f x).toAdd i)
    (heZ : ∀ a (x y : f.ker), φ a x = y → (z y).toAdd = (π a).val *ᵥ (z x).toAdd) :
    ∀ x : Q, x^2=1 := by
  let e := MulEquiv.ofBijective z hz
  let jM : Multiplicative (Fin 2 → F) →* Q := f.ker.subtype.comp e.symm.toMonoidHom
  let j : (Fin 2 → F) →+ Additive Q := {
    toFun v := Additive.ofMul (jM (Multiplicative.ofAdd v))
    map_zero' := jM.map_one
    map_add' x y := jM.map_mul (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) }
  have hj : Function.Injective j := by
    intro x y hxy
    apply Multiplicative.ofAdd.injective
    apply e.symm.injective
    apply Subtype.ext
    exact congrArg Additive.toMul hxy
  let p : Additive Q →+ (Fin n → Fin 2 → F) := {
    toFun x := (f x.toMul).toAdd
    map_zero' := f.map_one
    map_add' x y := f.map_mul x.toMul y.toMul }
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨y,hy⟩ := hf (Multiplicative.ofAdd x)
    exact ⟨Additive.ofMul y,congrArg Multiplicative.toAdd hy⟩
  have hex (x : Additive Q) : p x=0 ↔ ∃ v, j v=x := by
    constructor
    · intro hx
      have hxk : x.toMul ∈ f.ker := hx
      refine ⟨(e ⟨x.toMul,hxk⟩).toAdd,?_⟩
      apply Additive.toMul.injective
      change ((e.symm (e ⟨x.toMul,hxk⟩) : f.ker) : Q) = x.toMul
      rw [e.symm_apply_apply]
    · rintro ⟨v,rfl⟩
      exact (e.symm (Multiplicative.ofAdd v)).property
  let β : SL(2,F) →* MulAut Q := π.liftOfSurjective hπ ⟨φ,hkill⟩
  have hβ (x : X) : β (π x)=φ x := π.liftOfRightInverse_comp_apply _ _ _ x
  let ρ : Representation ℤ SL(2,F) (Additive Q) := {
    toFun g := (β g).toMonoidHom.toAdditive.toIntLinearMap
    map_one' := by
      apply LinearMap.ext; intro x
      change β 1 x.toMul=x.toMul
      rw [map_one]; rfl
    map_mul' g h := by
      apply LinearMap.ext; intro x
      change β (g*h) x.toMul=β g (β h x.toMul)
      rw [map_mul]; rfl }
  have heP (g : SL(2,F)) (x : Additive Q) :
      p (ρ g x) = fun i => g.val *ᵥ p x i := by
    obtain ⟨b,rfl⟩ := hπ g
    change (f (β (π b) x.toMul)).toAdd = _
    rw [hβ]
    exact he b x.toMul
  have heJ (g : SL(2,F)) (v : Fin 2 → F) : ρ g (j v) = j (g.val *ᵥ v) := by
    obtain ⟨b,rfl⟩ := hπ g
    let x : f.ker := e.symm (Multiplicative.ofAdd v)
    have hx : (z x).toAdd = v := congrArg Multiplicative.toAdd (e.apply_symm_apply _)
    have hym : φ b (x : Q) ∈ f.ker := by
      apply Multiplicative.toAdd.injective
      change (f (φ b (x : Q))).toAdd = 0
      rw [he,show f (x : Q)=1 from x.property]
      funext i
      exact Matrix.mulVec_zero _
    let y : f.ker := ⟨φ b (x : Q),hym⟩
    have hy : y = e.symm (Multiplicative.ofAdd ((π b).val *ᵥ v)) := by
      apply e.injective
      rw [e.apply_symm_apply]
      apply Multiplicative.toAdd.injective
      change (z y).toAdd = _
      rw [heZ b x y rfl,hx]
      rfl
    apply Additive.toMul.injective
    change β (π b) (x : Q) = (e.symm (Multiplicative.ofAdd ((π b).val *ᵥ v)) : Q)
    rw [hβ]
    exact congrArg Subtype.val hy
  intro x
  have hh := NaturalAbelian.double_eq_zero a ha0 ha1 j hj p hp hex ρ heJ heP
    (Additive.ofMul x)
  have hh' := congrArg Additive.toMul hh
  change x*x=1 at hh'
  simpa only [pow_two] using hh'
end Representation.SL2
