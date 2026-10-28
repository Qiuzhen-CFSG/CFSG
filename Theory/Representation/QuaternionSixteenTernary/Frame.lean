module
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Tactic

/-!
# A canonical ternary four-dimensional quaternion frame

Let a and r satisfy a⁴=r²=-1 and r a r⁻¹=a⁻¹ on a ternary space of order81.
The operator a-a⁻¹ is an involution, with its eigenspaces exchanged by r.
A nonzero positive vector v gives the basis (v,av,rv,rav-rv). Independence
uses the anisotropic binary polynomial x²+xy-y² over F₃; cardinality then
proves that the frame covers the whole space. Thus a and r have fixed
coordinate matrices without enumerating any general linear group.

Source: the complement-action classification at the start of Aschbacher,
*Sporadic Groups* (1994), 45.11, p.248.
-/

public section
namespace Theory.Representation.QuaternionSixteenTernary
variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

structure Relations (a r : V ≃ₗ[ZMod 3] V) : Prop where
  a_four : ∀ v, a (a (a (a v))) = -v
  r_square : ∀ v, r (r v) = -v
  reverse : ∀ v, r (a v) = a.symm (r v)

namespace Relations
variable {a r : V ≃ₗ[ZMod 3] V} (h : Relations a r)
include h in
theorem reverse' (v : V) : a (r v) = r (a.symm v) := by
  have hh := h.reverse (a.symm v)
  simpa only [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] using congrArg a hh

include h in
theorem a_inverse (v : V) : a.symm v = -a (a (a v)) := by
  apply a.injective
  rw [LinearEquiv.apply_symm_apply,map_neg,h.a_four,neg_neg]

include h in
theorem inverse_square (v : V) : a.symm (a.symm v) = -a (a v) := by
  rw [h.a_inverse,LinearEquiv.apply_symm_apply]

noncomputable def difference : V →ₗ[ZMod 3] V := a.toLinearMap-a.symm.toLinearMap

@[simp] theorem difference_apply (v : V) : difference (a:=a) v = a v-a.symm v := by rfl

include h in
theorem difference_square (v : V) : difference (a:=a) (difference (a:=a) v) = v := by
  simp only [difference_apply,map_sub,LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply,
    h.inverse_square]
  calc
    a (a v)-v-(v- -a (a v)) = (-2 : ZMod 3) • v := by module
    _ = v := by rw [show (-2 : ZMod 3)=1 from rfl,one_smul]

include h in
theorem difference_reverse (v : V) : difference (a:=a) (r v) = -r (difference (a:=a) v) := by
  simp only [difference_apply,map_sub,h.reverse',←h.reverse]
  abel

include h in
theorem exists_positive [Nontrivial V] : ∃ v : V, v≠0 ∧ difference (a:=a) v=v := by
  obtain ⟨x,hx⟩ := exists_ne (0:V)
  let y := difference (a:=a) x+x
  by_cases hy : y=0
  · refine ⟨r x,?_,?_⟩
    · exact fun he=>hx (r.injective (he.trans (map_zero r).symm))
    · have ht : difference (a:=a) x = -x := eq_neg_of_add_eq_zero_left hy
      rw [h.difference_reverse,ht,map_neg,neg_neg]
  · exact ⟨y,hy,by dsimp [y]; rw [map_add,h.difference_square,add_comm]⟩

theorem quadratic_of_positive (v : V) (hv : difference (a:=a) v=v) : a (a v)=a v+v := by
  have hh := congrArg a hv
  simp only [difference_apply,map_sub,LinearEquiv.apply_symm_apply] at hh
  exact (sub_eq_iff_eq_add).mp hh

theorem difference_a (v : V) : difference (a:=a) (a v)=a (difference (a:=a) v) := by
  simp only [difference_apply,map_sub,LinearEquiv.apply_symm_apply,LinearEquiv.symm_apply_apply]

theorem positive_plane_independent (v : V) (hne : v≠0) (hv : difference (a:=a) v=v)
    (x y : ZMod 3) (he : x • v+y • a v=0) : x=0 ∧ y=0 := by
  have hquad := quadratic_of_positive v hv
  have ha := congrArg a he
  simp only [map_add,map_smul,map_zero,hquad,smul_add] at ha
  have hz : (x*(x+y)-y*y) • v=0 := by
    linear_combination (norm := module) (x+y) • he-y • ha
  have hd : x*(x+y)-y*y=0 := (smul_eq_zero.mp hz).resolve_right hne
  have roots : ∀ x y : ZMod 3, x*(x+y)-y*y=0 → x=0 ∧ y=0 := by decide
  exact roots x y hd

noncomputable def frame (v : V) : (Fin 4 → ZMod 3) →ₗ[ZMod 3] V :=
  (LinearMap.proj 0).smulRight v + (LinearMap.proj 1).smulRight (a v) +
    (LinearMap.proj 2).smulRight (r v) + (LinearMap.proj 3).smulRight (r (a v)-r v)

@[simp] theorem frame_apply (v : V) (x : Fin 4 → ZMod 3) :
    frame (a:=a) (r:=r) v x = x 0 • v+x 1 • a v+x 2 • r v+x 3 • (r (a v)-r v) := by rfl

include h in
theorem frame_injective (v : V) (hne : v≠0) (hv : difference (a:=a) v=v) :
    Function.Injective (frame (a:=a) (r:=r) v) := by
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro x hx
  change frame (a:=a) (r:=r) v x=0 at hx
  have ht := congrArg (difference (a:=a)) hx
  simp only [frame_apply,map_add,map_smul,map_sub,map_zero,hv,difference_a,h.difference_reverse] at ht
  have hp : x 0 • v+x 1 • a v=0 := by
    simp only [frame_apply] at hx
    have ht' := congrArg (fun w : V => (2 : ZMod 3) • w) (congrArg₂ (·+·) hx ht)
    calc
      x 0 • v+x 1 • a v = (2 : ZMod 3) •
        ((x 0 • v+x 1 • a v+x 2 • r v+x 3 • (r (a v)-r v)) +
        (x 0 • v+x 1 • a v+x 2 • (-r v)+x 3 • (-r (a v)- -r v))) := by
          match_scalars <;> ring_nf <;> simp only [show (4 : ZMod 3)=1 from rfl,mul_one]
      _ = 0 := by simpa only [zero_add,smul_zero] using ht'
  obtain ⟨hx0,hx1⟩ := positive_plane_independent v hne hv (x 0) (x 1) hp
  have hm : (x 2-x 3) • v+x 3 • a v=0 := by
    have hr := congrArg r hx
    simp only [frame_apply,map_add,map_smul,map_sub,h.r_square,map_zero,hx0,hx1,zero_smul,zero_add] at hr
    linear_combination (norm := module) -hr
  obtain ⟨hx23,hx3⟩ := positive_plane_independent v hne hv (x 2-x 3) (x 3) hm
  have hx2 : x 2=0 := by simpa [hx3] using hx23
  funext i
  fin_cases i <;> simp [hx0,hx1,hx2,hx3]

include h in
theorem frame_surjective [Finite V] (hc : Nat.card V=81)
    (v : V) (hne : v≠0) (hv : difference (a:=a) v=v) :
    Function.Surjective (frame (a:=a) (r:=r) v) := by
  apply ((h.frame_injective v hne hv).bijective_of_nat_card_le ?_).2
  simp only [hc,Nat.card_fun,Nat.card_zmod,Nat.card_fin]
  decide

noncomputable def coordinates [Finite V] (hc : Nat.card V=81)
    (v : V) (hne : v≠0) (hv : difference (a:=a) v=v) :
    (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] V :=
  LinearEquiv.ofBijective (frame v) ⟨h.frame_injective v hne hv,h.frame_surjective hc v hne hv⟩

@[simp] theorem coordinates_apply [Finite V] (hc : Nat.card V=81)
    (v : V) (hne : v≠0) (hv : difference (a:=a) v=v) (x : Fin 4 → ZMod 3) :
    h.coordinates hc v hne hv x = x 0 • v+x 1 • a v+x 2 • r v+x 3 • (r (a v)-r v) := by rfl

include h in
theorem frame_a (v : V) (hv : difference (a:=a) v=v) (x : Fin 4 → ZMod 3) :
    a (frame (a:=a) (r:=r) v x) = frame (a:=a) (r:=r) v
      ![x 1,x 0+x 1,x 3,x 2-x 3] := by
  have hinv : a.symm v=a v-v := by
    change a v-a.symm v=v at hv
    linear_combination (norm := module) -hv
  simp only [frame_apply,map_add,map_smul,map_sub,quadratic_of_positive v hv,
    h.reverse',LinearEquiv.symm_apply_apply,hinv]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  module

include h in
theorem frame_r (v : V) (x : Fin 4 → ZMod 3) :
    r (frame (a:=a) (r:=r) v x) = frame (a:=a) (r:=r) v
      ![-x 2+x 3,-x 3,x 0+x 1,x 1] := by
  simp only [frame_apply,map_add,map_smul,map_sub,h.r_square,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  module

include h in
theorem exists_coordinates [Finite V] (hc : Nat.card V=81) :
    ∃ e : (Fin 4 → ZMod 3) ≃ₗ[ZMod 3] V,
      (∀ x, a (e x)=e ![x 1,x 0+x 1,x 3,x 2-x 3]) ∧
      (∀ x, r (e x)=e ![-x 2+x 3,-x 3,x 0+x 1,x 1]) := by
  let : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by rw [hc];decide)
  obtain ⟨v,hne,hv⟩ := h.exists_positive
  exact ⟨h.coordinates hc v hne hv,h.frame_a v hv,h.frame_r v⟩
end Relations
end Theory.Representation.QuaternionSixteenTernary
