module
public import Theory.LinearAlgebra.BinaryOrthogonalPair
public import Theory.LinearAlgebra.BinaryFourFixedSpace
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import Theory.ElementaryAbelian.Basic

/-!
# Residual-nine control of binary orthogonal pairs

A faithful elementary group of order nine on a binary four-space is a
Sylow three-subgroup of its full linear group. Consequently every commuting
cubic operator belongs to that group. If the operator is alternating for
an invariant nondegenerate alternating form, it is self-adjoint; preservation
of the form then forces its square to be one.

For complementary singular fixed/moved four-spaces, displacement gives the
usual alternating pencil. Restricting the same residual action to the second
space preserves that pencil and commutes with its operator. Its cubic branch
is therefore excluded, and the original two isometries have product of sixth
power one. This avoids enumerating the eight-dimensional orthogonal group.

Source: Aschbacher--Smith, F.9.5(6.ii), pp.319--320, and the residual-centralizer
step of 12.6.26, pp.831--832.
-/

public section
open Subgroup
namespace BinaryOrthogonalPair
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

private theorem cubic_mem_nine (hd : Module.finrank (ZMod 2) W = 4)
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 3 E]
    (hc : Nat.card E = 9) (ρ : E →* (W ≃ₗ[ZMod 2] W))
    (hf : Function.Injective ρ) (t : W ≃ₗ[ZMod 2] W) (ht : t^3=1)
    (hcomm : ∀ e, Commute (ρ e) t) : t ∈ ρ.range := by
  let : Finite W := Module.finite_of_finite (ZMod 2)
  let : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun a : W ≃ₗ[ZMod 2] W => (a : W → W)) DFunLike.coe_injective
  have hcard : Nat.card ρ.range = 9 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hc
  have hidx : ¬ 3 ∣ ρ.range.index := by
    have h := ρ.range.card_mul_index
    rw [hcard, BinaryFourFixedSpace.card_GL_four hd] at h
    have hi : ρ.range.index = 2240 := by omega
    rw [hi]
    decide
  have hp : IsPGroup 3 ρ.range := IsPGroup.of_card (n:=2) hcard
  let P := hp.toSylow hidx
  have htP : IsPGroup 3 (zpowers t) := IsPGroup.of_card_dvd_pow (n:=1) (by
    simpa only [Nat.card_zpowers,pow_one] using orderOf_dvd_of_pow_eq_one ht)
  apply htP.le_sylow_of_normalized P ?_ (mem_zpowers t)
  intro a ha
  obtain ⟨e,rfl⟩ := ha
  apply Subgroup.centralizer_le_normalizer
  intro x hx
  obtain ⟨n,rfl⟩ := hx
  exact ((hcomm e).zpow_right n).eq.symm

/-- A commuting faithful residual nine excludes the cubic branch of the
four-dimensional alternating pencil. -/
theorem pencil_square_of_nine (hd : Module.finrank (ZMod 2) W=4)
    (C : LinearMap.BilinForm (ZMod 2) W) (hC : C.IsAlt) (hn : C.Nondegenerate)
    (t : W ≃ₗ[ZMod 2] W) (ht : (C.compRight t.toLinearMap).IsAlt)
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 3 E]
    (hc : Nat.card E=9) (ρ : E →* (W ≃ₗ[ZMod 2] W)) (hf : Function.Injective ρ)
    (hpres : ∀ e x y, C (ρ e x) (ρ e y)=C x y)
    (hcomm : ∀ e, Commute (ρ e) t) : t.toLinearMap^2=1 := by
  rcases pencil_relation hd C hC hn t ht with hs | hs
  · exact hs
  have htt (x : W) : t (t x)=t x+x := by
    have hh : (t (t x)+t x)+x=0 := LinearMap.congr_fun hs x
    have hneg (v : W) : -v=v := by
      apply neg_eq_of_add_eq_zero_left
      have h := @two_smul (ZMod 2) W _ _ _ v
      rw [show (2:ZMod 2)=0 by decide,zero_smul] at h
      exact h.symm
    rw [add_assoc] at hh
    exact (eq_neg_of_add_eq_zero_left hh).trans (hneg _)
  have ht3 : t^3=1 := by
    ext x
    change t (t (t x))=x
    rw [htt,htt]
    abel_nf
    simp only [← Int.cast_smul_eq_zsmul (ZMod 2)]
    match_scalars <;> decide
  obtain ⟨e,he⟩ := cubic_mem_nine hd hc ρ hf t ht3 hcomm
  have hp (x y : W) : C (t x) (t y)=C x y := he ▸ hpres e x y
  have hadj (x y : W) : C (t x) y=C x (t y) := by
    calc
      C (t x) y = -C y (t x) := (hC.neg_eq y (t x)).symm
      _ = C x (t y) := ht.neg_eq y x
  ext x
  apply sub_eq_zero.mp
  apply hn.1
  intro y
  change C (t (t x)-x) y=0
  rw [map_sub,LinearMap.sub_apply,hadj,hp,sub_self]
end BinaryOrthogonalPair

namespace BinaryOrthogonalPair
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
/-- The same orthogonal generators have product of sixth power one when
a commuting residual nine acts faithfully on an original singular four-space. -/
theorem product_six_of_nine
    (q : QuadraticForm (ZMod 2) V) (hq : q.polarBilin.Nondegenerate)
    (a b : V ≃ₗ[ZMod 2] V) (ha : ∀ x, q (a x)=q x) (hb : ∀ x, q (b x)=q x)
    (A B : Submodule (ZMod 2) V) (hc : IsCompl A B)
    (hd : Module.finrank (ZMod 2) A = Module.finrank (ZMod 2) B)
    (hA : ∀ x ∈ A, q x=0) (hB : ∀ x ∈ B, q x=0)
    (hka : LinearMap.ker (a.toLinearMap-LinearMap.id)=A)
    (hra : LinearMap.range (a.toLinearMap-LinearMap.id)=A)
    (hkb : LinearMap.ker (b.toLinearMap-LinearMap.id)=B)
    (hrb : LinearMap.range (b.toLinearMap-LinearMap.id)=B)
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 3 E]
    (hE : Nat.card E=9) (ρ : E →* (V ≃ₗ[ZMod 2] V))
    (hρq : ∀ r x, q (ρ r x)=q x)
    (hρB : ∀ r x, x ∈ B → ρ r x ∈ B)
    (hfaith : ∀ r, (∀ x ∈ B, ρ r x=x) → r=1)
    (hρa : ∀ r, Commute (ρ r) a) (hρb : ∀ r, Commute (ρ r) b)
    (hBd : Module.finrank (ZMod 2) B=4) : (a*b)^6=1 := by
  obtain ⟨t,c,_,_,_,_,ha',hb'⟩ := coordinates q hq a b ha hb A B hc hd hA hB hka hra hkb hrb
  let u : B →ₗ[ZMod 2] V := c.toLinearMap.comp (LinearMap.inl (ZMod 2) B B)
  let w : B →ₗ[ZMod 2] V := c.toLinearMap.comp (LinearMap.inr (ZMod 2) B B)
  have hcval (x y : B) : c (x,y)=u x+w y := by
    simpa only [u,w,LinearMap.comp_apply,LinearMap.inl_apply,LinearMap.inr_apply,
      LinearEquiv.coe_coe,Prod.mk_add_mk,add_zero,zero_add] using c.map_add (x,0) (0,y)
  have huA (x : B) : u x ∈ A := by
    apply hka.le
    change a (c (x,0))-c (x,0)=0
    rw [ha',add_zero,sub_self]
  have hwB (x : B) : w x ∈ B := by
    apply hkb.le
    change b (c (0,x))-c (0,x)=0
    rw [hb',map_zero,add_zero,sub_self]
  have hwinj : Function.Injective w := by
    intro x y h
    exact congrArg Prod.snd (c.injective h)
  have hudi (x : B) : a (w x)=u x+w x := by
    change a (c (0,x))=_
    rw [ha',zero_add,hcval]
  have hwdi (x : B) : b (u x)=u x+w (t x) := by
    change b (c (x,0))=_
    rw [hb',zero_add,hcval]
  let C := LinearMap.BilinForm.comp q.polarBilin u w
  have hC (x y : B) : C x y=q.polarBilin (u x) (w y) := rfl
  have hAlt : C.IsAlt := by
    intro x
    rw [hC,QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,←hudi,ha,
      hA _ (huA x),hB _ (hwB x)]
    simp
  have hsep : C.SeparatingLeft := by
    intro x hx
    have hz : u x=0 := by
      apply hq.1
      intro v
      obtain ⟨⟨y,z⟩,rfl⟩ := c.surjective v
      rw [hcval,map_add]
      have h₁ : q.polarBilin (u x) (u y)=0 := by
        rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,
          hA _ (A.add_mem (huA x) (huA y)),hA _ (huA x),hA _ (huA y)]
        simp
      rw [h₁,zero_add]
      exact hx z
    have he : c (x,0)=c (0,0) := hz.trans c.map_zero.symm
    exact congrArg Prod.fst (c.injective he)
  have hND : C.Nondegenerate := by
    refine ⟨hsep,?_⟩
    intro x hx
    apply hsep x
    intro y
    rw [←hAlt.neg_eq,hx,neg_zero]
  have ht : (C.compRight t.toLinearMap).IsAlt := by
    intro x
    change q.polarBilin (u x) (w (t x))=0
    rw [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,←hwdi,hb,
      hA _ (huA x),hB _ (hwB (t x))]
    simp
  let d : B ≃ₗ[ZMod 2] B := LinearEquiv.ofInjectiveOfFinrankEq
    (w.codRestrict B hwB) (fun x y h => hwinj (congrArg Subtype.val h)) rfl
  have hmap (r : E) : B.map (ρ r).toLinearMap=B := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact hρB r x hx
    · intro x hx
      refine ⟨ρ r⁻¹ x,hρB r⁻¹ x hx,?_⟩
      change (ρ r * ρ r⁻¹) x=x
      rw [←map_mul,mul_inv_cancel,map_one]
      rfl
  let τ : E →* (B ≃ₗ[ZMod 2] B) := {
    toFun := fun r => (ρ r).ofSubmodules B B (hmap r)
    map_one' := by ext x; exact LinearEquiv.congr_fun ρ.map_one x
    map_mul' := fun r s => by ext x; exact LinearEquiv.congr_fun (ρ.map_mul r s) x }
  have hτinj : Function.Injective τ := by
    apply (MonoidHom.ker_eq_bot_iff τ).mp
    apply bot_unique
    intro r hr
    apply hfaith r
    intro x hx
    exact congrArg Subtype.val (LinearEquiv.congr_fun (show τ r=1 from hr) ⟨x,hx⟩)
  let σ := (MulAut.conj d.symm).toMonoidHom.comp τ
  have hσinj : Function.Injective σ := (MulAut.conj d.symm).injective.comp hτinj
  have hwρ (r : E) (x : B) : w (σ r x)=ρ r (w x) := by
    change (d (d.symm (τ r (d x))):V)=ρ r (d x)
    rw [d.apply_symm_apply]
    rfl
  have huval (x : B) : u x=a (w x)-w x := by rw [hudi]; abel
  have hwval (x : B) : w (t x)=b (u x)-u x := by rw [hwdi]; abel
  have huρ (r : E) (x : B) : u (σ r x)=ρ r (u x) := by
    rw [huval,hwρ,huval,map_sub]
    congr 1
    exact LinearEquiv.congr_fun (hρa r).eq.symm (w x)
  have htρ (r : E) (x : B) : t (σ r x)=σ r (t x) := by
    apply hwinj
    rw [hwval,hwρ,hwval,huρ,map_sub]
    congr 1
    exact LinearEquiv.congr_fun (hρb r).eq.symm (u x)
  have hCρ (r : E) (x y : B) : C (σ r x) (σ r y)=C x y := by
    rw [hC,hC,huρ,hwρ]
    simp only [QuadraticMap.polarBilin_apply_apply,QuadraticMap.polar,←map_add,hρq]
  have ht2 := pencil_square_of_nine hBd C hAlt hND t ht hE σ hσinj hCρ
    (fun r => by apply LinearEquiv.ext; intro x; exact (htρ r x).symm)
  have htt (x : B) : t (t x)=x := LinearMap.congr_fun ht2 x
  ext v
  obtain ⟨⟨x,y⟩,rfl⟩ := c.surjective v
  simp only [pow_succ,pow_zero,LinearEquiv.mul_apply,LinearEquiv.coe_one,id_eq,hb',ha',map_add,htt]
  apply congrArg c
  apply Prod.ext <;> dsimp <;> abel_nf <;> simp only [← Int.cast_smul_eq_zsmul (ZMod 2)] <;> match_scalars <;> decide
end BinaryOrthogonalPair
