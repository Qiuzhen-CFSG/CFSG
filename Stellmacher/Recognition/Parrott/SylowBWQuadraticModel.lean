module

public import Stellmacher.Recognition.Parrott.SylowBWSquareInputs
public import Stellmacher.Recognition.Parrott.SylowBWQuadraticInputs
public import Theory.GroupAction.BinaryQuadraticPairing

/-!
# Assembly of the marked five-four quadratic model

An intrinsic binary quadratic pairing for the actual core quotients can be
transported along the given faithful C₅ ⋊ C₄ model of H/J. Its actions retain
their faithfulness, and the literal images of the supplied x, b and w satisfy
the required square-displacement equation. The pairing detects exactly the
original ambient commutator of b and w.

The theorem in this module is a conditional assembly step: construction of
the intrinsic quadratic pairing remains a separate prerequisite. No abstract
orthogonality or classification assertion is used here.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.673–674 and printed p.678, equations (1)–(2).
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] [Finite G] {z : G}
set_option quotPrecheck false in
local notation "H" => centralizer ({z} : Set G)
local notation "J" => pCore 2 H
local notation "D" => commutator J
set_option quotPrecheck false in
local notation "Z" => (center J).subgroupOf D
local notation "V" => J ⧸ D
local notation "W" => D ⧸ Z

set_option synthInstance.maxHeartbeats 40000 in
/-- Transport an actual core quadratic pairing to the common faithful
five-four actor, retaining the supplied square-displacement marks. -/
public theorem ParrottSylowActionData.exists_bw_quadratic_model_of_intrinsic_model
    {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}
    (f : ParrottSylowActionData n) (h : ParrottCentralizerHypotheses z)
    (d : Theory.GroupAction.BinaryQuadraticPairing (H ⧸ J) V W)
    (hsquare : ∀ (j : J) (hj : j ^ 2 ∈ D),
      d.square (QuotientGroup.mk' D j) = QuotientGroup.mk' Z ⟨j ^ 2, hj⟩)
    (hR : ∀ (a : H) (w w' : D), ((w' : J) : H) = a * ((w : J) : H) * a⁻¹ →
      d.rightAction (QuotientGroup.mk' J a) (QuotientGroup.mk' Z w) = QuotientGroup.mk' Z w')
    (hpair : ∀ (b : J) (w : D),
      d.pairing (QuotientGroup.mk' D b) (QuotientGroup.mk' Z w) = 1 ↔
        Commute b (w : J)) :
    ∃ (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5))),
      Function.Injective φ ∧
      ∃ (model : Theory.GroupAction.BinaryQuadraticPairing
          (SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ) V W)
        (g : SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ)
        (β : V) (ω : W),
        orderOf g = 4 ∧ model.square β = model.rightAction (g ^ 2) ω * ω ∧
        model.square β ≠ 1 ∧
        (model.pairing β ω = 1 ↔ Tits.parrottCommutator n.b f.w = 1) := by
  obtain ⟨φ, hφ, ⟨c⟩⟩ := h.quotient_model
  let model : Theory.GroupAction.BinaryQuadraticPairing
      (SemidirectProduct (Multiplicative (ZMod 5)) (Multiplicative (ZMod 4)) φ) V W := {
    d with
    leftAction := d.leftAction.comp c.symm.toMonoidHom
    rightAction := d.rightAction.comp c.symm.toMonoidHom
    leftAction_injective := d.leftAction_injective.comp c.symm.injective
    rightAction_injective := d.rightAction_injective.comp c.symm.injective
    pairing_equivariant := fun a v w => d.pairing_equivariant (c.symm a) v w
    square_equivariant := fun a v => d.square_equivariant (c.symm a) v }
  obtain ⟨x, b, w, hx, hb, hw, horder, hdisp, hne⟩ :=
    f.bw_marked_square h d.square hsquare d.rightAction hR
  refine ⟨φ, hφ, model, c (QuotientGroup.mk' J x),
    QuotientGroup.mk' D b, QuotientGroup.mk' Z w, ?_, ?_, hne, ?_⟩
  · rw [c.orderOf_eq]
    exact horder
  · change d.square _ = d.rightAction (c.symm ((c (QuotientGroup.mk' J x)) ^ 2)) _ * _
    rw [← map_pow, c.symm_apply_apply]
    exact hdisp
  · change d.pairing _ _ = 1 ↔ _
    rw [hpair, Tits.parrottCommutator_eq_one_iff]
    let i := (H).subtype.comp (J).subtype
    have hi : Function.Injective i := (H).subtype_injective.comp (J).subtype_injective
    have hbval : i b = n.b := hb
    have hwval : i (w : J) = f.w := hw
    constructor
    · intro hbw
      have he := congrArg i hbw.eq
      change n.b * f.w = f.w * n.b
      simpa only [map_mul, hbval, hwval] using he
    · intro hbw
      apply hi
      simpa only [map_mul, hbval, hwval] using hbw.eq
end Stellmacher.Recognition
