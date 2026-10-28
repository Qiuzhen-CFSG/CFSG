module
public import Theory.GroupAction.TernaryCubicFixedCard
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Push

/-!
# Explicit coordinates for a nonquadratic ternary cubic

A cubic automorphism of an elementary group of order81 with nonzero second
displacement has Jordan blocks of lengths three and one. Choose a vector at
the top of the length-three chain. The cubic fixed-point bound supplies a
fixed vector independent of its bottom vector. These four vectors give an
injective linear frame, and cardinality makes the frame an equivalence.

The construction provides an actual equivariant coordinate map, using no
enumeration of GL₄(3). Its consumer is the original opposite-core action in
G2Recognition.MaximalCubicCoordinates, in the proof of Aschbacher–Smith I.4.5,
printed p.417. Full endpoint action compatibility is a separate obligation.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupAction.TernaryCubicCoordinates
variable {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 3 V]

private def linearActor (a : MulAut V) : Additive V ≃ₗ[ZMod 3] Additive V :=
  { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }

private def difference (a : MulAut V) : Additive V →ₗ[ZMod 3] Additive V :=
  (linearActor a).toLinearMap - LinearMap.id

omit [Finite V] in
private theorem difference_cube (a : MulAut V) (ha : a^3=1) (v : Additive V) :
    difference a (difference a (difference a v))=0 := by
  have hthree : linearActor a (linearActor a (linearActor a v))=v :=
    congrArg Additive.ofMul (DFunLike.congr_fun ha v.toMul)
  simp only [difference,LinearMap.sub_apply,LinearEquiv.coe_coe,LinearMap.id_apply,
    map_sub,hthree]
  calc
    _ = (3 : ZMod 3) • (linearActor a v-linearActor a (linearActor a v)) := by module
    _ = 0 := by rw [show (3 : ZMod 3)=0 from rfl,zero_smul]

private theorem exists_extra_fixed (a : MulAut V) (ha : a^3=1)
    (hc : Nat.card V=81) (v : Additive V) (hv : difference a v=0) :
    ∃ w : Additive V, difference a w=0 ∧ ∀ k : ZMod 3,w≠k • v := by
  by_contra hn
  push Not at hn
  have hfix : ∀ k : ZMod 3, a (k • v).toMul=(k • v).toMul := by
    intro k
    have h : difference a (k • v)=0 := by rw [map_smul,hv,smul_zero]
    exact congrArg Additive.toMul (sub_eq_zero.mp h)
  let f : ZMod 3 → a.fixedSubgroup := fun k=>⟨(k • v).toMul,(MulAut.mem_fixedSubgroup _ _).mpr (hfix k)⟩
  have hf : Function.Surjective f := by
    intro w
    have hw : difference a (Additive.ofMul (w:V))=0 := by
      exact sub_eq_zero.mpr (congrArg (fun z : V => Additive.ofMul z) ((MulAut.mem_fixedSubgroup a (w:V)).mp w.property))
    obtain ⟨k,hk⟩ := hn (Additive.ofMul (w:V)) hw
    exact ⟨k,Subtype.ext (congrArg Additive.toMul hk.symm)⟩
  have hcard := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_zmod] at hcard
  have hh := a.ternary_cubic_fixed_card_bound ha
  rw [hc] at hh
  have : Nat.card a.fixedSubgroup^3≤27 := (Nat.pow_le_pow_left hcard 3)
  omega

private def frame (a : MulAut V) (v w : Additive V) :
    (Fin 4 → ZMod 3) →ₗ[ZMod 3] Additive V :=
  (LinearMap.proj 0).smulRight (difference a (difference a v)) +
    (LinearMap.proj 1).smulRight (difference a v) +
    (LinearMap.proj 2).smulRight v + (LinearMap.proj 3).smulRight w

omit [Finite V] in
private theorem frame_apply (a : MulAut V) (v w : Additive V) (x : Fin 4 → ZMod 3) :
    frame a v w x=x 0 • difference a (difference a v)+x 1 • difference a v+
      x 2 • v+x 3 • w := rfl

omit [Finite V] in
private theorem frame_injective (a : MulAut V) (ha : a^3=1)
    (v w : Additive V) (hv : difference a (difference a v)≠0)
    (hw : difference a w=0) (hwv : ∀ k : ZMod 3,w≠k • difference a (difference a v)) :
    Function.Injective (frame a v w) := by
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro x hx
  change frame a v w x=0 at hx
  have hN := congrArg (difference a) hx
  simp only [frame_apply,map_add,map_smul,difference_cube a ha,hw,map_zero,
    smul_zero,zero_add,add_zero] at hN
  have hNN := congrArg (difference a) hN
  simp only [map_add,map_smul,difference_cube a ha,map_zero,smul_zero,zero_add] at hNN
  have hx2 : x 2=0 := (smul_eq_zero.mp hNN).resolve_right hv
  rw [hx2,zero_smul,add_zero] at hN
  have hx1 : x 1=0 := (smul_eq_zero.mp hN).resolve_right hv
  simp only [frame_apply,hx1,hx2,zero_smul,add_zero] at hx
  have hx3 : x 3=0 := by
    by_contra h
    apply hwv (-(x 3)⁻¹*x 0)
    have hh := congrArg (fun z : Additive V => (x 3)⁻¹ • z) hx
    simp only [smul_add,smul_smul,inv_mul_cancel₀ h,one_smul,smul_zero] at hh
    rw [neg_mul,neg_smul]
    exact eq_neg_of_add_eq_zero_right hh
  rw [hx3,zero_smul,add_zero] at hx
  have hx0 : x 0=0 := (smul_eq_zero.mp hx).resolve_right hv
  funext i
  fin_cases i <;> simp [hx0,hx1,hx2,hx3]

omit [Finite V] in
private theorem frame_actor (a : MulAut V) (ha : a^3=1)
    (v w : Additive V) (hw : difference a w=0) (x : Fin 4 → ZMod 3) :
    linearActor a (frame a v w x)=frame a v w ![x 0+x 1,x 1+x 2,x 2,x 3] := by
  have step (z : Additive V) : linearActor a z=z+difference a z := by
    simp only [difference,LinearMap.sub_apply,LinearEquiv.coe_coe,LinearMap.id_apply]
    abel
  rw [step]
  simp only [frame_apply,map_add,map_smul,difference_cube a ha,hw,smul_zero,
    zero_add,add_zero,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons]
  module

/-- A nonquadratic cubic on elementary eighty-one has a length-three Jordan chain
and one fixed coordinate. -/
theorem exists_coordinates (a : MulAut V) (ha : a^3=1) (hc : Nat.card V=81)
    (hne : ∃ v : V,a (a v*v⁻¹)*(a v*v⁻¹)⁻¹≠1) :
    ∃ e : V ≃* Multiplicative (Fin 4 → ZMod 3), ∀ v,
      e (a v)=Multiplicative.ofAdd ![(e v).toAdd 0+(e v).toAdd 1,
        (e v).toAdd 1+(e v).toAdd 2,(e v).toAdd 2,(e v).toAdd 3] := by
  obtain ⟨v,hv⟩ := hne
  have hNv : difference a (difference a (Additive.ofMul v))≠0 := by
    intro h
    apply hv
    change a (a v / v) / (a v / v)=1 at h
    simpa only [div_eq_mul_inv] using h
  obtain ⟨w,hw,hwn⟩ := exists_extra_fixed a ha hc _ (difference_cube a ha (Additive.ofMul v))
  let F := frame a (Additive.ofMul v) w
  have hi : Function.Injective F := frame_injective a ha _ _ hNv hw hwn
  have hs : Function.Surjective F := (hi.bijective_of_nat_card_le (by
    simp only [Nat.card_fun,Nat.card_zmod,Nat.card_fin]
    exact hc.le)).2
  let E := LinearEquiv.ofBijective F ⟨hi,hs⟩
  let e : V ≃* Multiplicative (Fin 4 → ZMod 3) :=
    AddEquiv.toMultiplicativeRight E.symm.toAddEquiv
  refine ⟨e,?_⟩
  intro z
  have hh := frame_actor a ha (Additive.ofMul v) w hw (E.symm (Additive.ofMul z))
  change linearActor a (E (E.symm (Additive.ofMul z)))=E _ at hh
  rw [LinearEquiv.apply_symm_apply] at hh
  exact congrArg Multiplicative.ofAdd ((E.symm_apply_eq).mpr hh)

end Theory.GroupAction.TernaryCubicCoordinates
