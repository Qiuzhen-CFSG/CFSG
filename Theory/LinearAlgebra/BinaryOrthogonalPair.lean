module
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Projection
public import Theory.LinearAlgebra.BinaryAlternatingFourPencil

/-!
# Products of complementary binary orthogonal involutions

For two isometries whose fixed and displacement spaces are complementary
singular four-spaces, displacement identifies these two spaces. In the
resulting coordinates the original isometries are (x,y) ↦ (x+y,y) and
(x,y) ↦ (x,y+t x). The polar form induces a nondegenerate alternating
form C with C composed with t alternating. The four-dimensional pencil
relation gives product powers six or five; complementary fixed spaces
exclude product orders one and two.

Every coordinate map intertwines the same given isometries. No replacement
action or module classification is assumed. Source: Aschbacher--Smith
F.9.5(6.ii), pp.319--320, applied in 12.6.26, p.831.
-/

public section
namespace BinaryOrthogonalPair
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem displacement_equiv
    (a : V ≃ₗ[ZMod 2] V) (A B : Submodule (ZMod 2) V)
    (hc : IsCompl A B) (hd : Module.finrank (ZMod 2) A = Module.finrank (ZMod 2) B)
    (hk : LinearMap.ker (a.toLinearMap-LinearMap.id)=A)
    (hr : LinearMap.range (a.toLinearMap-LinearMap.id)=A) :
    ∃ e : B ≃ₗ[ZMod 2] A, ∀ x : B, (e x : V)=a x-x := by
  let N := a.toLinearMap-LinearMap.id
  let f : B →ₗ[ZMod 2] A := (N.comp B.subtype).codRestrict A
    (fun x => hr ▸ LinearMap.mem_range_self N x)
  have hf : Function.Injective f := by
    apply (LinearMap.ker_eq_bot).mp
    apply bot_unique
    intro x hx
    have hz : N x=0 := congrArg Subtype.val hx
    have ha : (x:V) ∈ A := hk ▸ hz
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hc.disjoint x ha x.property
  let e := LinearEquiv.ofInjectiveOfFinrankEq f hf hd.symm
  exact ⟨e,fun _ => rfl⟩

omit [FiniteDimensional (ZMod 2) V] in
private theorem polar_singular
    (q : QuadraticForm (ZMod 2) V) (A : Submodule (ZMod 2) V)
    (hA : ∀ x ∈ A, q x=0) (x y : A) : q.polarBilin x y=0 := by
  rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
    hA _ (A.add_mem x.property y.property),hA _ x.property,hA _ y.property]
  simp

omit [FiniteDimensional (ZMod 2) V] in
private theorem polar_displacement
    (q : QuadraticForm (ZMod 2) V) (a : V ≃ₗ[ZMod 2] V)
    (ha : ∀ x, q (a x)=q x) (hs : ∀ x, q (a x-x)=0) (x : V) :
    q.polarBilin (a x-x) x=0 := by
  rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,sub_add_cancel,ha,hs]
  simp

/-- Coordinates retain the same two generators. Their product is governed
by an invertible operator on one original fixed space, alternating for a
nondegenerate alternating form on that space. -/
theorem coordinates
    (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin.Nondegenerate)
    (a b : V ≃ₗ[ZMod 2] V) (ha : ∀ x, q (a x)=q x) (hb : ∀ x, q (b x)=q x)
    (A B : Submodule (ZMod 2) V) (hc : IsCompl A B)
    (hd : Module.finrank (ZMod 2) A = Module.finrank (ZMod 2) B)
    (hA : ∀ x ∈ A, q x=0) (hB : ∀ x ∈ B, q x=0)
    (hka : LinearMap.ker (a.toLinearMap-LinearMap.id)=A)
    (hra : LinearMap.range (a.toLinearMap-LinearMap.id)=A)
    (hkb : LinearMap.ker (b.toLinearMap-LinearMap.id)=B)
    (hrb : LinearMap.range (b.toLinearMap-LinearMap.id)=B) :
    ∃ (t : B ≃ₗ[ZMod 2] B) (c : (B×B) ≃ₗ[ZMod 2] V)
      (C : LinearMap.BilinForm (ZMod 2) B),
      C.IsAlt ∧ C.Nondegenerate ∧ (C.compRight t.toLinearMap).IsAlt ∧
      (∀ x y, a (c (x,y))=c (x+y,y)) ∧
      (∀ x y, b (c (x,y))=c (x,y+t x)) := by
  obtain ⟨e,he⟩ := displacement_equiv a A B hc hd hka hra
  obtain ⟨f,hf⟩ := displacement_equiv b B A hc.symm hd.symm hkb hrb
  let t := e.trans f
  let c := (e.prodCongr (LinearEquiv.refl (ZMod 2) B)).trans (A.prodEquivOfIsCompl B hc)
  let C := LinearMap.BilinForm.comp q.polarBilin (A.subtype.comp e.toLinearMap) B.subtype
  have hC (x y : B) : C x y=q.polarBilin (e x) y := rfl
  have hAlt : C.IsAlt := by
    intro x
    rw [hC,he]
    exact polar_displacement q a ha (fun x => hA _ (hra ▸ LinearMap.mem_range_self _ x)) x
  have hsep : C.SeparatingLeft := by
    intro x hx
    have hz : (e x : V)=0 := by
      apply hq.1
      intro y
      obtain ⟨u,hu,v,hv,rfl⟩ := Submodule.mem_sup.mp (hc.codisjoint.eq_top ▸ Submodule.mem_top (x:=y))
      rw [map_add]
      have h₁ : q.polarBilin (e x) u=0 := polar_singular q A hA (e x) ⟨u,hu⟩
      have h₂ : q.polarBilin (e x) v=0 := hx ⟨v,hv⟩
      rw [h₁,h₂,add_zero]
    exact e.injective ((Subtype.ext hz).trans e.map_zero.symm)
  have hND : C.Nondegenerate := by
    refine ⟨hsep,?_⟩
    intro x hx
    apply hsep x
    intro y
    rw [← hAlt.neg_eq, hx,neg_zero]
  have ht : (C.compRight t.toLinearMap).IsAlt := by
    intro x
    change q.polarBilin (e x) (f (e x))=0
    rw [hf,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar_comm]
    exact polar_displacement q b hb (fun x => hB _ (hrb ▸ LinearMap.mem_range_self _ x)) (e x)
  have hcval (x y : B) : c (x,y)=(e x:V)+y := rfl
  have haA (x : A) : a x=x := sub_eq_zero.mp (show a x-x=0 from hka.symm ▸ x.property)
  have hbB (x : B) : b x=x := sub_eq_zero.mp (show b x-x=0 from hkb.symm ▸ x.property)
  refine ⟨t,c,C,hAlt,hND,ht,?_,?_⟩
  · intro x y
    rw [hcval,map_add,haA,hcval,map_add,Submodule.coe_add,he y]
    abel
  · intro x y
    rw [hcval,map_add,hbB,hcval]
    change b (e x:V)+(y:V)=(e x:V)+((y:V)+(f (e x):V))
    rw [hf]
    abel
end BinaryOrthogonalPair

namespace BinaryOrthogonalPair
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

/-- An invertible operator alternating for a binary alternating four-form
satisfies one of the two quadratic relations. -/
theorem pencil_relation (hd : Module.finrank (ZMod 2) W=4)
    (C : LinearMap.BilinForm (ZMod 2) W) (hC : C.IsAlt) (hn : C.Nondegenerate)
    (t : W ≃ₗ[ZMod 2] W) (ht : (C.compRight t.toLinearMap).IsAlt) :
    t.toLinearMap^2=1 ∨ t.toLinearMap^2+t.toLinearMap+1=0 := by
  classical
  let e := (Module.finBasisOfFinrankEq (ZMod 2) W hd).equivFun
  let F := C.comp e.symm.toLinearMap e.symm.toLinearMap
  let φ : Module.End (ZMod 2) W ≃+* BinaryAlternatingFour.Mat :=
    e.conjRingEquiv.trans LinearMap.toMatrixAlgEquiv'.toRingEquiv
  have hF : F.IsAlt := fun x => hC (e.symm x)
  have hFn : F.Nondegenerate := hn.congr e
  have hi : φ t.toLinearMap * φ t.symm.toLinearMap=1 := by
    rw [←map_mul,←map_one φ]
    congr 1
    ext x
    exact t.apply_symm_apply x
  have hdet : (φ t.toLinearMap).det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hi
    rw [Matrix.det_mul,hz,zero_mul,Matrix.det_one] at hh
    exact zero_ne_one hh
  have halt : (F.toMatrix'*φ t.toLinearMap).toBilin'.IsAlt := by
    change (F.toMatrix' * (e.conjRingEquiv t.toLinearMap).toMatrix').toBilin'.IsAlt
    rw [←LinearMap.BilinForm.toMatrix'_compRight,Matrix.toBilin'_toMatrix']
    intro x
    simpa [F,LinearEquiv.conjRingEquiv] using ht (e.symm x)
  have hm := BinaryAlternatingFour.alternating_pencil_relation F.toMatrix' (φ t.toLinearMap)
    (by simpa only [Matrix.toBilin'_toMatrix'] using hF)
    (by simpa only [Matrix.toBilin'_toMatrix'] using hFn) hdet halt
  rcases hm with h | h
  · left
    apply φ.injective
    simpa only [map_pow,map_one] using h
  · right
    apply φ.injective
    simpa only [map_pow,map_add,map_one,map_zero] using h

omit [FiniteDimensional (ZMod 2) W] in
private theorem product_powers {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (a b : V ≃ₗ[ZMod 2] V) (t : W ≃ₗ[ZMod 2] W) (c : (W×W) ≃ₗ[ZMod 2] V)
    (ha : ∀ x y, a (c (x,y))=c (x+y,y))
    (hb : ∀ x y, b (c (x,y))=c (x,y+t x))
    (ht : t.toLinearMap^2=1 ∨ t.toLinearMap^2+t.toLinearMap+1=0) :
    (a*b)^6=1 ∨ (a*b)^5=1 := by
  rcases ht with ht | ht
  · left
    have htt (x) : t (t x)=x := LinearMap.congr_fun ht x
    ext v
    obtain ⟨⟨x,y⟩,rfl⟩ := c.surjective v
    simp only [pow_succ,pow_zero,LinearEquiv.mul_apply,LinearEquiv.coe_one,id_eq,hb,ha,
      map_add,htt]
    apply congrArg c
    apply Prod.ext <;> dsimp <;> abel_nf <;> simp only [← Int.cast_smul_eq_zsmul (ZMod 2)] <;> match_scalars <;> decide
  · right
    have htt (x) : t (t x)=t x+x := by
      have hh : (t (t x)+t x)+x=0 := LinearMap.congr_fun ht x
      have hself (v : W) : v+v=0 := by
        have h := @two_smul (ZMod 2) W _ _ _ v
        rw [show (2:ZMod 2)=0 by decide,zero_smul] at h
        exact h.symm
      have hneg (v : W) : -v=v := neg_eq_of_add_eq_zero_left (hself v)
      rw [add_assoc] at hh
      exact (eq_neg_of_add_eq_zero_left hh).trans (hneg _)
    ext v
    obtain ⟨⟨x,y⟩,rfl⟩ := c.surjective v
    simp only [pow_succ,pow_zero,LinearEquiv.mul_apply,LinearEquiv.coe_one,id_eq,hb,ha,
      map_add,htt]
    apply congrArg c
    apply Prod.ext <;> dsimp <;> abel_nf <;> simp only [← Int.cast_smul_eq_zsmul (ZMod 2)] <;> match_scalars <;> decide
end BinaryOrthogonalPair

namespace BinaryOrthogonalPair
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Two orthogonal involutions with complementary singular fixed/moved
four-spaces have product order three, five or six. -/
theorem product_order
    (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin.Nondegenerate)
    (a b : V ≃ₗ[ZMod 2] V) (ha : ∀ x, q (a x)=q x) (hb : ∀ x, q (b x)=q x)
    (A B : Submodule (ZMod 2) V) (hc : IsCompl A B)
    (hAd : Module.finrank (ZMod 2) A=4) (hBd : Module.finrank (ZMod 2) B=4)
    (hA : ∀ x ∈ A, q x=0) (hB : ∀ x ∈ B, q x=0)
    (hka : LinearMap.ker (a.toLinearMap-LinearMap.id)=A)
    (hra : LinearMap.range (a.toLinearMap-LinearMap.id)=A)
    (hkb : LinearMap.ker (b.toLinearMap-LinearMap.id)=B)
    (hrb : LinearMap.range (b.toLinearMap-LinearMap.id)=B) :
    orderOf (a*b)=3 ∨ orderOf (a*b)=5 ∨ orderOf (a*b)=6 := by
  obtain ⟨t,c,C,hC,hCn,hCt,ha',hb'⟩ := coordinates q hq a b ha hb A B hc
    (hAd.trans hBd.symm) hA hB hka hra hkb hrb
  have hp := product_powers a b t c ha' hb' (pencil_relation hBd C hC hCn t hCt)
  have hn2 : (a*b)^2 ≠ 1 := by
    intro hh
    have hz (x : B) : x=0 := by
      have hv := congrArg (fun f : V ≃ₗ[ZMod 2] V => f (c (0,x))) hh
      simp only [pow_succ,pow_zero,LinearEquiv.mul_apply,LinearEquiv.coe_one,id_eq,
        ha',hb',map_zero,zero_add,add_zero] at hv
      have he := congrArg Prod.fst (c.injective hv)
      change x+(x+t x)=0 at he
      have hself (v : B) : v+v=0 := by
        have h := @two_smul (ZMod 2) B _ _ _ v
        rw [show (2:ZMod 2)=0 by decide,zero_smul] at h
        exact h.symm
      rw [←add_assoc,hself,zero_add] at he
      exact t.injective (he.trans t.map_zero.symm)
    have he : B=⊥ := by
      apply bot_unique
      intro x hx
      exact congrArg Subtype.val (hz ⟨x,hx⟩)
    rw [he,finrank_bot] at hBd
    omega
  have hno (h : orderOf (a*b) ∣ 2) : False := hn2 (orderOf_dvd_iff_pow_eq_one.mp h)
  rcases hp with hp | hp
  · have hd := orderOf_dvd_of_pow_eq_one hp
    have hc : orderOf (a*b)=1 ∨ orderOf (a*b)=2 ∨ orderOf (a*b)=3 ∨ orderOf (a*b)=6 := by
      have hle := Nat.le_of_dvd (by decide : 0<6) hd
      have ht : ∀ n ∈ Finset.range 7, n ∣ 6 → n=1 ∨ n=2 ∨ n=3 ∨ n=6 := by decide
      exact ht _ (Finset.mem_range.mpr (by omega)) hd
    rcases hc with h | h | h | h
    · exact (hno (by simpa only [h] using (show (1:ℕ) ∣ 2 from by decide))).elim
    · exact (hno (by rw [h])).elim
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · have hd := orderOf_dvd_of_pow_eq_one hp
    rcases (Nat.dvd_prime (by decide : Nat.Prime 5)).mp hd with h | h
    · exact (hno (by simpa only [h] using (show (1:ℕ) ∣ 2 from by decide))).elim
    · exact Or.inr (Or.inl h)
end BinaryOrthogonalPair
