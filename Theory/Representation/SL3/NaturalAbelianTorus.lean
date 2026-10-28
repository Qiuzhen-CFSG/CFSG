module
public import Theory.Representation.SL3.NaturalAbelianExtension
public import Theory.GroupTheory.OddElementLift
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Excluding natural exponent-four lifts over every nonbinary field

For an exact abelian extension of two natural SL₃ modules, the central
covering kernel makes every lifted root transvection an involution. An
odd-order lift of diag(a,a,a⁻²) commutes with the lifts of the root elements
with parameters 1 and a. Writing T for this torus action and U,V for those
root displacements, D=V-TU kills the lower layer and has image in it.

If doubling identifies the two natural layers, D²=2D=0. The commuting
root involutions give T²(2U)=T(2U). On the natural root line this forces
a²=a, contrary to a being a unit different from one. Such a unit exists
over every field with more than two elements. This includes odd field
degree, where the full SL₃ quotient has no nontrivial central scalar.

The application excludes the canonical homocyclic center lift in
Aschbacher–Smith C.1.34, printed pp.136–137, without assuming that the
covering kernel is trivial. The proof uses only finite-group and
endomorphism algebra and is independent of the MS hypotheses.
-/

public noncomputable section
open Representation
open scoped MatrixGroups commutatorElement
namespace Representation.NaturalAbelianTorus

private theorem commute_of_odd_of_central_commutator {H : Type*} [Group H]
    (x y : H) (m : ℕ) (hm : Odd m) (hx : x^m=1) (hy : y^2=1)
    (hcx : Commute ⁅x,y⁆ x) (hcy : Commute ⁅x,y⁆ y) : Commute x y := by
  have hpow (n : ℕ) : ⁅x^n,y⁆ = ⁅x,y⁆^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ,commutatorElement_mul_left_eq_conj_mul,
        hcx.symm.pow_left n |>.eq,mul_inv_cancel_right,ih,←pow_succ']
  have hpow' (n : ℕ) : ⁅x,y^n⁆ = ⁅x,y⁆^n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',commutatorElement_mul_right_eq_mul_conj,
        ih,mul_assoc ⁅x,y⁆ y,hcy.symm.pow_right n |>.eq,←mul_assoc,
        mul_inv_cancel_right,←pow_succ']
  have hm' : ⁅x,y⁆^m=1 := by rw [←hpow,hx]; simp
  have htwo : ⁅x,y⁆^2=1 := by rw [←hpow',hy]; simp
  apply commutatorElement_eq_one_iff_commute.mp
  apply orderOf_eq_one_iff.mp
  exact Nat.eq_one_of_dvd_coprimes hm.coprime_two_right
    (orderOf_dvd_of_pow_eq_one hm') (orderOf_dvd_of_pow_eq_one htwo)

variable {X A F : Type*} [Group X] [AddCommGroup A] [Field F] [CharP F 2]
variable {π : X →* SL(3,F)} {ρ : Representation ℤ X A}
variable (d : NaturalAbelianExtension.Data π ρ)

include d in
private theorem odd_root_commute (hπ : Function.Surjective π)
    (hcentral : ∀ z, π z=1 → ∀ g, Commute (ρ z) (ρ g))
    (s : X) (hs : Odd (orderOf s)) {i j : Fin 3} (hij : i ≠ j)
    (a : F) (g : X) (hg : π g=Matrix.SpecialLinearGroup.transvection hij a)
    (hc : Commute (π s) (π g)) : Commute (ρ s) (ρ g) := by
  let f := ρ.asGroupHom
  have hker : π ⁅s,g⁆=1 := by rw [map_commutatorElement]; exact hc.commutator_eq
  have hcent (k : X) : Commute ⁅f s,f g⁆ (f k) := by
    rw [←map_commutatorElement]
    apply Units.ext
    exact (hcentral ⁅s,g⁆ hker k).eq
  have hsq : f g^2=1 := by
    apply Units.ext
    exact NaturalAbelianExtension.root_lift_square d hπ hcentral hij a g hg
  have hh := commute_of_odd_of_central_commutator (f s) (f g) (orderOf s) hs
    (by rw [←map_pow,pow_orderOf_eq_one,map_one]) hsq (hcent s) (hcent g)
  exact congrArg (fun u : (Module.End ℤ A)ˣ => (u : Module.End ℤ A)) hh.eq

private def torus : Fˣ →* SL(3,F) where
  toFun a := ⟨Matrix.diagonal ![(a:F),(a:F),((a:F)*(a:F))⁻¹], by
    rw [Matrix.det_diagonal,Fin.prod_univ_three]
    simp [←mul_assoc,a.ne_zero]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  map_mul' a b := by
    apply Subtype.ext
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i <;> simp
    ring

omit [CharP F 2] in
private theorem torus_apply (a : Fˣ) (v : Fin 3 → F) :
    specialLinearNatural 3 (torus a) v =
      ![(a:F)*v 0,(a:F)*v 1,((a:F)*(a:F))⁻¹*v 2] := by
  change (Matrix.diagonal _).mulVec v = _
  ext i
  fin_cases i <;> simp [Matrix.mulVec,dotProduct,Matrix.diagonal]

omit [CharP F 2] in
private theorem torus_root_commute (a : Fˣ) (b : F) :
    Commute (torus a) (Matrix.SpecialLinearGroup.transvection (show (0:Fin 3) ≠ 1 by decide) b) := by
  apply Subtype.ext
  change Matrix.diagonal ![(a:F),(a:F),((a:F)*(a:F))⁻¹] *
      (1 + Matrix.single 0 1 b) =
    (1 + Matrix.single 0 1 b) * Matrix.diagonal ![(a:F),(a:F),((a:F)*(a:F))⁻¹]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,
      Matrix.diagonal,Matrix.single,Matrix.one_apply,mul_comm]

omit [CharP F 2] in
private theorem root_apply (a : F) (v : Fin 3 → F) :
    specialLinearNatural 3
      (Matrix.SpecialLinearGroup.transvection (show (0:Fin 3) ≠ 1 by decide) a) v =
      v + Pi.single 0 (a*v 1) := by
  change ((1 : Matrix (Fin 3) (Fin 3) F) + Matrix.single 0 1 a).mulVec v = _
  simp only [Matrix.add_mulVec,Matrix.one_mulVec,Matrix.single_mulVec_eq]
  congr 1
  funext k
  by_cases hk : k = 0 <;> simp [hk]

private theorem ring_relation {B : Type*} [Ring B] (T U V : B)
    (hU : U^2 = -2*U) (hV : V^2 = -2*V)
    (hTU : Commute T U) (hTV : Commute T V) (hUV : Commute U V)
    (hD : (V-T*U)^2=0) (h2D : 2*(V-T*U)=0) :
    T*(T*(2*U))=T*(2*U) := by
  let D := V-T*U
  have hBD : Commute (T*U) D := (hTV.mul_left hUV).sub_right (Commute.refl _)
  have he : V=T*U+D := by dsimp [D]; abel
  have hcross : 2*(T*U)*D=0 := by
    calc
      _ = (T*U)*(2*D) := by noncomm_ring
      _ = 0 := by rw [h2D,mul_zero]
  have hv : V^2 = -2*T^2*U := by
    rw [he,hBD.add_sq,hD,add_zero,hcross,add_zero,hTU.mul_pow,hU]
    noncomm_ring
  have hh : 2*T^2*U=2*T*U := by
    have hvv := hv.symm.trans hV
    have hvd : 2*V=2*T*U :=
      sub_eq_zero.mp (by simpa only [mul_sub,mul_assoc] using h2D)
    have hh' : -(2*T^2*U)=-(2*V) := by simpa only [neg_mul] using hvv
    exact (neg_injective hh').trans hvd
  calc
    _ = 2*T^2*U := by noncomm_ring
    _ = 2*T*U := hh
    _ = T*(2*U) := by noncomm_ring

variable [Finite X] [Finite F]

include d in
/-- A nonbinary coefficient field rules out a natural exponent-four lift
of a central SL₃ cover. No nontrivial central scalar is required. -/
theorem no_square_extension (hπ : Function.Surjective π)
    (hcentral : ∀ z, π z=1 → ∀ g, Commute (ρ z) (ρ g))
    (hdouble : ∀ x : A, x+x=d.incl (d.proj x))
    (hF : 2 < Nat.card F) : False := by
  have hu : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hu
  obtain ⟨a,ha⟩ := exists_ne (1:Fˣ)
  have ha1 : (a:F) ≠ 1 := fun hh => ha (Units.ext hh)
  have hoddu : Odd (Nat.card Fˣ) := by
    let := Fintype.ofFinite F
    have heven := FiniteField.even_card_of_char_two (F := F) (ringChar.eq F 2)
    have hgt : 2 < Fintype.card F := by simpa only [Nat.card_eq_fintype_card] using hF
    rw [Nat.card_units,Nat.card_eq_fintype_card,Nat.odd_iff]
    omega
  have hoddt : Odd (orderOf (torus a)) :=
    hoddu.of_dvd_nat ((orderOf_map_dvd torus a).trans (orderOf_dvd_natCard a))
  obtain ⟨s₀,hs₀⟩ := hπ (torus a)
  obtain ⟨s,_,hs,hst⟩ := π.exists_odd_power_with_image s₀ (hs₀.symm ▸ hoddt)
  have hst : π s=torus a := hst.trans hs₀
  obtain ⟨g,hg⟩ := hπ (Matrix.SpecialLinearGroup.transvection (show (0:Fin 3) ≠ 1 by decide) (1:F))
  obtain ⟨h,hh⟩ := hπ (Matrix.SpecialLinearGroup.transvection (show (0:Fin 3) ≠ 1 by decide) (a:F))
  let T := ρ s
  let U := ρ g-1
  let V := ρ h-1
  let D := V-T*U
  have hTU : Commute T U := by
    apply Commute.sub_right _ (Commute.one_right _)
    exact odd_root_commute d hπ hcentral s hs (by decide) 1 g hg
      (by rw [hst,hg]; exact torus_root_commute a 1)
  have hTV : Commute T V := by
    apply Commute.sub_right _ (Commute.one_right _)
    exact odd_root_commute d hπ hcentral s hs (by decide) (a:F) h hh
      (by rw [hst,hh]; exact torus_root_commute a (a:F))
  have hUV : Commute U V := by
    apply Commute.sub_right _ (Commute.one_right _)
    apply Commute.sub_left _ (Commute.one_left _)
    exact NaturalAbelianExtension.root_lifts_commute d hπ hcentral (by decide) 1 (a:F) g h hg hh
  have hU : U^2 = -2*U := by
    have he := NaturalAbelianExtension.root_lift_square d hπ hcentral (by decide) 1 g hg
    calc
      U^2 = (ρ g)^2-1-2*U := by dsimp [U]; noncomm_ring
      _ = -2*U := by rw [he,sub_self,zero_sub]; noncomm_ring
  have hV : V^2 = -2*V := by
    have he := NaturalAbelianExtension.root_lift_square d hπ hcentral (by decide) (a:F) h hh
    calc
      V^2 = (ρ h)^2-1-2*V := by dsimp [V]; noncomm_ring
      _ = -2*V := by rw [he,sub_self,zero_sub]; noncomm_ring
  have hDq (x : A) : d.proj (D x)=0 := by
    change d.proj ((ρ h x-x)-ρ s (ρ g x-x))=0
    rw [map_sub,map_sub,d.proj_equivariant,d.proj_equivariant,
      map_sub,d.proj_equivariant,hst,hg,hh,root_apply,root_apply,torus_apply]
    ext k
    fin_cases k <;> simp
  have hDi (v : Fin 3 → F) : D (d.incl v)=0 := by
    change (ρ h (d.incl v)-d.incl v)-ρ s (ρ g (d.incl v)-d.incl v)=0
    rw [d.incl_equivariant,d.incl_equivariant,←map_sub,←map_sub,d.incl_equivariant,
      ←map_sub]
    apply (map_eq_zero_iff d.incl d.incl_injective).mpr
    rw [hst,hg,hh,root_apply,root_apply,torus_apply]
    ext k
    fin_cases k <;> simp
  have hD2 : D^2=0 := by
    apply LinearMap.ext
    intro x
    obtain ⟨v,hv⟩ := (d.exact _).mp (hDq x)
    change D (D x)=0
    rw [←hv,hDi]
  have h2D : 2*D=0 := by
    apply LinearMap.ext
    intro x
    rw [two_mul]
    change D x+D x=0
    rw [hdouble,hDq,map_zero]
  have hrel := ring_relation T U V hU hV hTU hTV hUV hD2 h2D
  obtain ⟨x,hx⟩ := d.proj_surjective (Pi.single 1 1)
  have hUx : U x+U x=d.incl (Pi.single 0 1) := by
    rw [hdouble]
    congr 1
    change d.proj (ρ g x-x)=_
    rw [map_sub,d.proj_equivariant,hg,root_apply,hx]
    ext k
    fin_cases k <;> simp
  have he := LinearMap.congr_fun hrel x
  rw [two_mul] at he
  change ρ s (ρ s (U x+U x))=ρ s (U x+U x) at he
  rw [hUx,d.incl_equivariant,d.incl_equivariant,hst] at he
  have he0 := congrFun (d.incl_injective he) 0
  simp only [torus_apply,Matrix.cons_val_zero,Pi.single_eq_same,mul_one] at he0
  exact ha1 ((mul_left_cancel₀ a.ne_zero) (he0.trans (mul_one (a:F)).symm))

end Representation.NaturalAbelianTorus
