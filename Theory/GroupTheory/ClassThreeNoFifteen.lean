module
public import Theory.GroupTheory.Commutator.ThirdTrilinear
public import Theory.LinearAlgebra.OrderFifteenTrilinear
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.Frattini.PGroup
public import Mathlib.GroupTheory.Abelianization.Finite

/-!
# No order15 automorphism on the class-three residual's Frattini quotient

A binary group of order512 and class three, with center of order two and
derived subgroup equal to its order32 Frattini subgroup, admits no
automorphism inducing order15 on the literal Frattini quotient.

That quotient is binary four-space. The central third commutator is
nontrivial because the group has class three. It descends to a nonzero
trilinear form on the abelianization and is invariant under every actual
group automorphism. The proved order15 linear-algebra obstruction excludes
such an induced abelianization action. Equality of derived and Frattini
subgroups identifies the two quotient actions by the canonical quotient
isomorphism and its automorphism-group conjugation.

This removes the order15 centralizer allowed by a merely linear analysis
of the Tits residual. The statement uses only intrinsic finite-group data
and the actual characteristic-quotient action, with no recognition premise.
Sources: class-three commutator calculus and the primitive binary degree4
recurrences proved in the imported order15 linear-algebra development.
-/

open scoped commutatorElement IsMulCommutative

namespace ThirdCommutator
open Subgroup

private theorem no_fifteen_on_abelianization
    {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    [IsElementaryAbelian 2 (Abelianization G)]
    (hclass : Group.nilpotencyClass G = 3)
    (hZ : Nat.card (center G) = 2) (hV : Nat.card (Abelianization G) = 16)
    (a : MulAut G) : orderOf a.abelianizationCongr ≠ 15 := by
  have hL3 : (⊤ : Subgroup G).lowerCentralSeries 3 = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hclass.le
  have hc : ⁅_root_.commutator G, (⊤ : Subgroup G)⁆ ≤ center G :=
    commutator_top_right_eq_bot_iff_le_center.mp hL3
  have hn : ∃ x y z : G, ⁅⁅x,y⁆,z⁆ ≠ 1 := by
    by_contra h
    push Not at h
    have hDc : _root_.commutator G ≤ center G := by
      rw [commutator_eq_closure, closure_le]
      rintro d ⟨x, y, rfl⟩
      change ⁅x,y⁆ ∈ center G
      rw [mem_center_iff]
      intro z
      exact (commutatorElement_eq_one_iff_mul_comm.mp (h x y z)).symm
    have hL2 : (⊤ : Subgroup G).lowerCentralSeries 2 = ⊥ :=
      commutator_top_right_eq_bot_iff_le_center.mpr hDc
    have hh := Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp hL2
    omega
  obtain ⟨F, hFne, hF⟩ := exists_invariant_third_commutator_trilinear hc hZ hn
  let L : MulAut (Abelianization G) →*
      (Additive (Abelianization G) ≃ₗ[ZMod 2] Additive (Abelianization G)) := {
    toFun := fun b => { b.toAdditive with map_smul' := ZMod.map_smul b.toAdditive }
    map_one' := by ext x; rfl
    map_mul' := by intro b c; ext x; rfl }
  have hLi : Function.Injective L := by
    intro b c hbc
    ext x
    exact Additive.ofMul.injective
      (congrArg (fun l : Additive (Abelianization G) ≃ₗ[ZMod 2] Additive (Abelianization G) =>
        l (Additive.ofMul x)) hbc)
  intro horder
  have hcard : Nat.card (Additive (Abelianization G)) = 16 := hV
  apply hFne
  exact LinearEquiv.invariant_trilinear_eq_zero_of_order_fifteen hcard
    (L a.abelianizationCongr) ((orderOf_injective L hLi a.abelianizationCongr).trans horder)
    F (hF a)


/-- The actual Frattini quotient action of a residual automorphism cannot have order15. -/
public theorem frattini_action_order_ne_fifteen
    {G : Type*} [Group G] [Finite G]
    (hG : IsPGroup 2 G) (hcard : Nat.card G = 512)
    (hclass : Group.nilpotencyClass G = 3) (hZ : Nat.card (center G) = 2)
    (hPhi : _root_.commutator G = frattini G) (hD : Nat.card (_root_.commutator G) = 32)
    (a : MulAut G) : orderOf (quotientAut (frattini G) a) ≠ 15 := by
  let : Fact (IsPGroup 2 G) := ⟨hG⟩
  let : Group.IsNilpotent G := hG.isNilpotent
  let e : Abelianization G ≃* G ⧸ frattini G := QuotientGroup.quotientMulEquivOfEq hPhi
  let : IsElementaryAbelian 2 (G ⧸ frattini G) := isElementaryAbelian_quotient_frattini
  let : IsElementaryAbelian 2 (Abelianization G) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply e.injective
      simpa using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (G ⧸ frattini G)) (e x)) }
  have hV : Nat.card (Abelianization G) = 16 := by
    have h := card_eq_card_quotient_mul_card_subgroup (_root_.commutator G)
    rw [hcard, hD] at h
    change 512 = Nat.card (Abelianization G) * 32 at h
    omega
  have heq : MulAut.congr e a.abelianizationCongr = quotientAut (frattini G) a := by
    ext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini G) q
    have hm : e (Abelianization.of x) = QuotientGroup.mk' (frattini G) x := rfl
    rw [MulAut.congr_apply, quotientAut_apply_mk]
    simp only [MulEquiv.trans_apply]
    rw [← hm, e.symm_apply_apply, abelianizationCongr_of]
    rfl
  have ho := (MulAut.congr e).orderOf_eq a.abelianizationCongr
  rw [heq] at ho
  intro h15
  exact no_fifteen_on_abelianization hclass hZ hV a (ho.symm.trans h15)

end ThirdCommutator
