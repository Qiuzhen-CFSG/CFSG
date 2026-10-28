module

public import Theory.Frattini.PGroup
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel
public import Theory.Representation.ElementaryAbelianAction
public import Theory.GroupAction.NoncentralTwoChiefLength.BinaryRepresentation
public import Theory.Representation.BinaryOffender.Basic
public import Theory.GroupAction.QuotientFixedIndex

/-!
# Binary actions on Frattini quotients

Automorphism actions on elementary abelian groups are binary linear actions.
For a finite two-group, a nontrivial cubic automorphism remains nontrivial
on the Frattini quotient, while every inner automorphism acts trivially there.
The fixed-index formula converts an index bound into a fixed-codimension bound.
These give the descended module in Aschbacher--Smith 13.3.12, printed p.890.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative

namespace Representation.FrattiniAction
variable {A B X Y : Type*} [Group A] [Group B] [Group X] [Finite X]

theorem quotientAut_cubic_ne_one (hX : IsPGroup 2 X) (a : A →* MulAut X) (c : A)
    (ho : orderOf c = 3) (hc : a c ≠ 1) :
    Subgroup.quotientAut (frattini X) (a c) ≠ 1 := by
  intro he
  let k : (Subgroup.quotientAut (frattini X)).ker := ⟨a c, he⟩
  have hp := (Subgroup.isPGroup_quotientAut_frattini_kernel hX).orderOf_coprime
    (by decide : Nat.Coprime 2 3) k
  have hd : orderOf k ∣ 3 := by
    rw [← Subgroup.orderOf_coe k]
    have hd : orderOf (a c) ∣ orderOf c := orderOf_map_dvd a c
    exact ho ▸ hd
  have h1 : orderOf k = 1 := Nat.eq_one_of_dvd_coprimes hp (dvd_refl _) hd
  exact hc (congrArg Subtype.val (orderOf_eq_one_iff.mp h1))

variable [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]

theorem fixedIndex_eq_two_pow_fixedCodim (ρ : Representation (ZMod 2) B Y) (D : Subgroup B) :
    BinaryFixedPoints.fixedIndex (ρ.comp D.subtype) =
      2 ^ BinaryOffender.fixedCodim ρ D := by
  have hi := BinaryFixedPoints.fixedIndex_mul_card (ρ.comp D.subtype)
  have hd := BinaryOffender.fixedCodim_add_finrank ρ D
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := (Representation.invariants (ρ.comp D.subtype))),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Y)] at hi
  simp only [Nat.card_zmod] at hi
  change _ * 2 ^ Module.finrank (ZMod 2) (BinaryOffender.fixedSpace ρ D) = _ at hi
  rw [← hd, pow_add] at hi
  exact Nat.eq_of_mul_eq_mul_right (by positivity) hi

noncomputable def ofAutomorphismHom [IsElementaryAbelian 2 X] (a : B →* MulAut X) :
    Representation (ZMod 2) B (Additive X) where
  toFun b := (a b).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    ext x
    change Additive.ofMul (a 1 x.toMul) = x
    rw [map_one]
    rfl
  map_mul' b c := by
    ext x
    change Additive.ofMul (a (b*c) x.toMul) = _
    rw [map_mul]
    rfl

omit [Finite X] in
@[simp] theorem ofAutomorphismHom_apply [IsElementaryAbelian 2 X]
    (a : B →* MulAut X) (b : B) (x : Additive X) :
    ofAutomorphismHom a b x = Additive.ofMul (a b x.toMul) := rfl

omit [Finite X] in
theorem ofAutomorphismHom_ne_one [IsElementaryAbelian 2 X]
    (a : B →* MulAut X) (b : B) (hb : a b ≠ 1) :
    ofAutomorphismHom a ≠ 1 := by
  intro he
  apply hb
  ext x
  exact Additive.ofMul.injective
    (congrArg (fun r : Representation (ZMod 2) B (Additive X) =>
      r b (Additive.ofMul x)) he)

theorem quotientAut_conj_eq_one (hX : IsPGroup 2 X) (x : X) :
    (frattini X).quotientAut (MulAut.conj x) = 1 := by
  let : Fact (IsPGroup 2 X) := ⟨hX⟩
  let : IsElementaryAbelian 2 (X ⧸ frattini X) :=
    isElementaryAbelian_quotient_frattini
  ext y
  induction y using QuotientGroup.induction_on with
  | H y =>
    change (frattini X).quotientAut (MulAut.conj x) (QuotientGroup.mk' (frattini X) y) = _
    rw [Subgroup.quotientAut_apply_mk]
    change QuotientGroup.mk' (frattini X) (x * y * x⁻¹) = QuotientGroup.mk' (frattini X) y
    simp [map_mul, map_inv, mul_comm]
section Descent
open BinaryFixedPoints
variable {H : Type*} [Group H] [MulDistribMulAction H X]

/-- Descend an automorphism action through a surjective actor map. If its
marked cubic moves the two-group and the original cyclic action has fixed
index at most four, the Frattini quotient is a nontrivial binary module with
marked fixed codimension at most two. -/
theorem exists_nontrivial_quotient_representation (hX : IsPGroup 2 X) (a : A →* MulAut X)
    (q : A →* B) (hq : Function.Surjective q)
    (hker : q.ker ≤ ((frattini X).quotientAut.comp a).ker)
    (c : A) (ho : orderOf c = 3) (hc : a c ≠ 1)
    (k : H →* A) (z : H) (hz : zpowers z = ⊤) (hk : k z = c)
    (hacts : ∀ r, MulDistribMulAction.toMulAut H X r = a (k r))
    (hi : (FixedPoints.subgroup H X).index ≤ 4) :
    letI : Fact (IsPGroup 2 X) := ⟨hX⟩
    letI : IsElementaryAbelian 2 (X ⧸ frattini X) := isElementaryAbelian_quotient_frattini
    ∃ ρ : Representation (ZMod 2) B (Additive (X ⧸ frattini X)),
      ρ ≠ 1 ∧ Representation.BinaryOffender.fixedCodim ρ (zpowers (q c)) ≤ 2 := by
  let Y := X ⧸ frattini X
  let : Fact (IsPGroup 2 X) := ⟨hX⟩
  let : IsElementaryAbelian 2 Y := isElementaryAbelian_quotient_frattini
  let b : A →* MulAut Y := (frattini X).quotientAut.comp a
  let β : B →* MulAut Y := q.liftOfSurjective hq ⟨b,hker⟩
  have hb (l : A) : β (q l) = b l := by
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  let ρ := ofAutomorphismHom β
  have hρ : ρ ≠ 1 := by
    apply ofAutomorphismHom_ne_one β (q c)
    rw [hb]
    exact quotientAut_cubic_ne_one hX a c ho hc
  let D := zpowers (q c)
  let g : H →* B := q.comp k
  have hgz : g z = q c := congrArg q hk
  have hg : g.range = D := by
    calc
      g.range = (⊤ : Subgroup H).map g := MonoidHom.range_eq_map g
      _ = D := by rw [← hz,g.map_zpowers,hgz]
  let g' := g.codRestrict D (fun r => hg ▸ (show g r ∈ g.range from ⟨r,rfl⟩))
  have hg' : Function.Surjective g' := by
    rintro ⟨r,hr⟩
    obtain ⟨t,ht⟩ := (show r ∈ g.range from hg.symm ▸ hr)
    exact ⟨t,Subtype.ext ht⟩
  let τ := ρ.comp D.subtype
  let := action (τ.comp g')
  let F : X →* Multiplicative (Additive Y) := {
    toFun x := Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk' (frattini X) x))
    map_one' := by change QuotientGroup.mk' (frattini X) 1 = 1; exact map_one _
    map_mul' x y := by exact (QuotientGroup.mk' (frattini X)).map_mul x y }
  have hF : Function.Surjective F := QuotientGroup.mk'_surjective (frattini X)
  have heq (r : H) (x : X) : F (r • x) = r • F x := by
    change QuotientGroup.mk' (frattini X) (MulDistribMulAction.toMulAut H X r x) =
      β (q (k r)) (QuotientGroup.mk' (frattini X) x)
    rw [hb]
    change _ = (frattini X).quotientAut (a (k r)) (QuotientGroup.mk' (frattini X) x)
    rw [Subgroup.quotientAut_apply_mk,hacts]
  have hi' : fixedIndex (τ.comp g') ≤ 4 :=
    (fixedPoints_index_le_of_surjective_equivariant F hF heq).trans hi
  have ht : fixedIndex (τ.comp g') = fixedIndex τ :=
    fixedIndex_eq_of_equivariant τ g' hg' (MulEquiv.refl _) (by intros; rfl)
  refine ⟨ρ,hρ,?_⟩
  rw [ht,fixedIndex_eq_two_pow_fixedCodim ρ D] at hi'
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hi'
end Descent
end Representation.FrattiniAction
