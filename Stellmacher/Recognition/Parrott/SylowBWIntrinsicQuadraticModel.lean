module

public import Stellmacher.Recognition.Parrott.SylowBWQuadraticModel
public import Stellmacher.Recognition.Parrott.SylowBWCorePairing
public import Stellmacher.Recognition.Parrott.SylowBWSquareQuadratic

/-!
# The intrinsic quadratic model on Parrott's actual core quotients

The faithful conjugation actions on `J/[J,J]` and `[J,J]/Z(J)`, the actual
square map, and the central commutator pairing assemble into the
`BinaryQuadraticPairing` required by the five-four argument.  The supplied
second elementary involution gives the nontrivial zero, while an element
commutes with its square for the self-orthogonality axiom.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673--674 and printed p.678, equations (1)--(2).
-/

open Subgroup
namespace Stellmacher.Recognition

variable {G : Type*} [Group G] [Finite G] {z : G}

set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
set_option quotPrecheck false in
local notation "J" => pCore 2 H
set_option quotPrecheck false in
local notation "D" => commutator J
set_option quotPrecheck false in
local notation "Z" => (center J).subgroupOf D
set_option quotPrecheck false in
local notation "V" => J ⧸ D
set_option quotPrecheck false in
local notation "W" => D ⧸ Z

/-- The actual core quotients carry the intrinsic equivariant quadratic model. -/
public theorem parrott_core_intrinsic_quadratic_model
    (h : ParrottCentralizerHypotheses z)
    (e : ParrottSecondElementaryData z) :
    ∃ d : Theory.GroupAction.BinaryQuadraticPairing (H ⧸ J) V W,
      (∀ (j : J) (hj : j ^ 2 ∈ D),
        d.square (QuotientGroup.mk' D j) = QuotientGroup.mk' Z ⟨j ^ 2, hj⟩) ∧
      (∀ (a : H) (w w' : D), ((w' : J) : H) = a * ((w : J) : H) * a⁻¹ →
        d.rightAction (QuotientGroup.mk' J a) (QuotientGroup.mk' Z w) =
          QuotientGroup.mk' Z w') ∧
      (∀ (b : J) (w : D),
        d.pairing (QuotientGroup.mk' D b) (QuotientGroup.mk' Z w) = 1 ↔
          Commute b (w : J)) := by
  obtain ⟨L, hLi, hLEval⟩ := parrott_core_quotient_action z h
  obtain ⟨R, hRi, hREval⟩ := parrott_derived_quotient_action z h
  obtain ⟨square, hsquare, hsquare_one, ⟨vzero, hvzero, hzero⟩⟩ :=
    parrott_core_square_map h e
  obtain ⟨eZ, p, hp_inj, hp_test, hp_eval, hp_inv⟩ :=
    parrott_core_invariant_pairing h L R hLEval hREval
  let d : Theory.GroupAction.BinaryQuadraticPairing (H ⧸ J) V W := {
    pairing := p
    pairing_injective := hp_inj
    square := square
    square_one := hsquare_one
    square_quadratic := by
      intro a b c
      exact parrott_core_square_seven_term h square hsquare a b c
    square_self := by
      intro v
      obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective D v
      have hb : b ^ 2 ∈ D := by
        apply (QuotientGroup.eq_one_iff _).mp
        change QuotientGroup.mk' D (b ^ 2) = 1
        rw [map_pow]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (parrott_core_abelianization_structure z h).1.exponent_dvd_p
          (QuotientGroup.mk' D b)
      rw [hsquare b hb]
      exact (hp_test b ⟨b ^ 2, hb⟩).mpr (Commute.self_pow b 2)
    square_has_nontrivial_zero := ⟨vzero, hvzero, hzero⟩
    leftAction := L
    rightAction := R
    leftAction_injective := hLi
    rightAction_injective := hRi
    pairing_equivariant := hp_inv
    square_equivariant := by
      intro a v
      exact parrott_core_square_equivariant h square hsquare L R hLEval hREval a v }
  exact ⟨d, hsquare, hREval, hp_test⟩

/-- Assemble the intrinsic core model with every supplied Sylow mark. -/
public theorem ParrottSylowActionData.exists_bw_quadratic_model
    {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
    (f : ParrottSylowActionData n) (h : ParrottCentralizerHypotheses z) :
    ∃ (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5))),
      Function.Injective φ ∧
      ∃ (model : Theory.GroupAction.BinaryQuadraticPairing
          (SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ) V W)
        (g : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ)
        (β : V) (ω : W),
        orderOf g = 4 ∧ model.square β = model.rightAction (g ^ 2) ω * ω ∧
        model.square β ≠ 1 ∧
        (model.pairing β ω = 1 ↔ Tits.parrottCommutator n.b f.w = 1) := by
  obtain ⟨d, hsquare, hR, hpair⟩ := parrott_core_intrinsic_quadratic_model h e
  exact f.exists_bw_quadratic_model_of_intrinsic_model h d hsquare hR hpair

end Stellmacher.Recognition
