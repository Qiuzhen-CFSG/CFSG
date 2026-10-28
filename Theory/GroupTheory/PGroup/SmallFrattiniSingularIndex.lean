module
public import Theory.GroupTheory.PGroup.SmallFrattiniLinearForms
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.Tactic

/-!
# Elementary subgroups in the small Frattini quadratic space

For a finite two-group with Frattini subgroup of order two, the image of an
elementary subgroup in the Frattini quotient is totally singular. Its binary
codimension is at most the logarithm of the subgroup index; containment of
the Frattini subgroup in the elementary subgroup is unnecessary.

This supplies the literal quotient-space input to the G.2.3 elementary-index
bounds used in Aschbacher–Smith 14.2.16 and 14.2.20, pp.985–987.
-/

public section
open Subgroup Module
open scoped IsMulCommutative commutatorElement
namespace SmallFrattini
variable {Q : Type*} [Group Q] [Finite Q]

/-- An elementary subgroup gives a totally singular subspace of the literal Frattini
quotient. Its codimension is bounded by its original group index, even when
the subgroup does not contain the Frattini subgroup. -/
theorem exists_totallySingular_of_index
    (htwo : IsPGroup 2 Q) (hphi : Nat.card (frattini Q) = 2)
    (A : Subgroup Q) [IsElementaryAbelian 2 A]
    (m : ℕ) (hindex : A.index ≤ 2^m) :
    letI : IsElementaryAbelian 2 (Q ⧸ frattini Q) := quotientElementary htwo
    ∃ E : Submodule (ZMod 2) (Additive (Q ⧸ frattini Q)),
      (∀ x ∈ E, quotientQuadraticForm htwo hphi x = 0) ∧
      (∀ x ∈ E, ∀ y ∈ E, quotientBilinearForm htwo hphi x y = 0) ∧
      finrank (ZMod 2) ((Additive (Q ⧸ frattini Q)) ⧸ E) ≤ m := by
  let : IsElementaryAbelian 2 (Q ⧸ frattini Q) := quotientElementary htwo
  let q := QuotientGroup.mk' (frattini Q)
  let D := A.map q
  let E : Submodule (ZMod 2) (Additive (Q ⧸ frattini Q)) :=
    AddSubgroup.toZModSubmodule 2 D.toAddSubgroup
  refine ⟨E,?_,?_,?_⟩
  · intro x hx
    change x.toMul ∈ D at hx
    obtain ⟨a,ha,he⟩ := hx
    have he' : x = Additive.ofMul (q a) := congrArg Additive.ofMul he.symm
    rw [he',quotientQuadraticForm_apply]
    have hz : quotientSquare htwo hphi (q a) = 1 := by
      apply Subtype.ext
      rw [quotientSquare_apply_mk]
      exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A) (⟨a,ha⟩ : A))
    rw [hz,map_one]
    rfl
  · intro x hx y hy
    change x.toMul ∈ D at hx
    change y.toMul ∈ D at hy
    obtain ⟨a,ha,he⟩ := hx
    obtain ⟨b,hb,hf⟩ := hy
    have he' : x = Additive.ofMul (q a) := congrArg Additive.ofMul he.symm
    have hf' : y = Additive.ofMul (q b) := congrArg Additive.ofMul hf.symm
    rw [he',hf',quotientBilinearForm_apply]
    have hz : quotientPolar htwo hphi (q a) (q b) = 1 := by
      apply Subtype.ext
      rw [quotientPolar_apply_mk]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (congrArg Subtype.val (mul_comm (⟨a,ha⟩ : A) ⟨b,hb⟩))
    rw [hz,map_one]
    rfl
  · have hDc : Nat.card D = 2 ^ finrank (ZMod 2) E := by
      exact (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := E)).trans
        (by rw [Nat.card_zmod])
    have hQc : Nat.card (Q ⧸ frattini Q) =
        2 ^ finrank (ZMod 2) (Additive (Q ⧸ frattini Q)) := by
      exact (Module.natCard_eq_pow_finrank (K := ZMod 2)
        (V := Additive (Q ⧸ frattini Q))).trans (by rw [Nat.card_zmod])
    have hcard := D.card_mul_index
    rw [hDc,hQc,←E.finrank_quotient_add_finrank,add_comm,pow_add] at hcard
    have hDi : D.index = 2 ^ finrank (ZMod 2) ((Additive (Q ⧸ frattini Q)) ⧸ E) :=
      Nat.eq_of_mul_eq_mul_left (by positivity) hcard
    apply (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp
    rw [←hDi]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero A.index_ne_zero_of_finite) (A.index_map_dvd (QuotientGroup.mk'_surjective _))).trans hindex
end SmallFrattini
