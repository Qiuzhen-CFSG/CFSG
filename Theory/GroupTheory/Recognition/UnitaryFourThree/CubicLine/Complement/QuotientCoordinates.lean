module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.Complement.QuotientFrame
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.Complement.PairingLift
public import Theory.GroupTheory.CubicCentralPairingForm

/-!
# Canonical coordinates for the original complement and commutator space

The actual SL₂(3) factor fixes the center and the marked rotation inverts it.
Naturality of the original commutator pairing therefore makes the former
isometric and the latter a negative similitude. The marked action theorem
now supplies common coordinates for the original quaternion factor, cubic
and rotation, with the original commutator form scaled by a nonzero scalar.
No representation or rigidity premise is added to SourceConfiguration.

Source: Aschbacher, *Sporadic Groups* (1994), 45.11, p.248.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
open Theory.GroupTheory.CentralQuotient
open Theory.Representation.QuaternionSixteenTernary
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
  {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)



noncomputable def oddCenterCoordinate : center c.D ≃* Multiplicative (ZMod 3) := by
  let : IsExtraspecial 3 c.D := c.odd_extraspecial
  exact mulEquivOfPrimeCardEq (IsExtraspecial.center_order_p 3 c.D) (by simp)

omit [Finite G] in
private theorem pairing_action (k : c.K) (x y : c.D ⧸ center c.D) :
    (((pairing (c.complementQuotientAction k x) (c.complementQuotientAction k y) : center c.D) : c.D) : G)=
      (k:G)*(((pairing x y : center c.D):c.D):G)*(k:G)⁻¹ := by
  have hh := pairing_quotientAut (c.complementAction k) x y
  exact congrArg Subtype.val hh

omit [Finite G] in
private theorem pairingForm_special (eZ : center c.D ≃* Multiplicative (ZMod 3))
    (k : c.K) (hk : (k:G)∈c.J) (x y : Additive (c.D ⧸ center c.D)) :
    pairingForm eZ (c.complementLinearAction k x) (c.complementLinearAction k y)=pairingForm eZ x y := by
  have hc := c.special_centralizes_line hk
  have hp : pairing (c.complementQuotientAction k x.toMul) (c.complementQuotientAction k y.toMul)=
      pairing x.toMul y.toMul := by
    apply Subtype.ext
    apply Subtype.ext
    rw [c.pairing_action]
    have hw : (((pairing x.toMul y.toMul : center c.D):c.D):G)∈c.W := by
      exact c.odd_center.le (pairing x.toMul y.toMul).property
    rw [←hc _ hw,mul_inv_cancel_right]
  simp only [pairingForm_apply,complementLinearAction_apply,toMul_ofMul]
  exact congrArg (fun w=>(eZ w).toAdd) hp

omit [Finite G] in
private theorem pairingForm_rotation (eZ : center c.D ≃* Multiplicative (ZMod 3))
    (x y : Additive (c.D ⧸ center c.D)) :
    pairingForm eZ (c.complementLinearAction ⟨c.marking.s*c.marking.t,mem_sup_right (mem_zpowers _)⟩ x)
      (c.complementLinearAction ⟨c.marking.s*c.marking.t,mem_sup_right (mem_zpowers _)⟩ y)=
      -pairingForm eZ x y := by
  let R : c.K := ⟨c.marking.s*c.marking.t,mem_sup_right (mem_zpowers _)⟩
  have hp : pairing (c.complementQuotientAction R x.toMul) (c.complementQuotientAction R y.toMul)=
      (pairing x.toMul y.toMul)⁻¹ := by
    apply Subtype.ext
    apply Subtype.ext
    rw [c.pairing_action]
    have hw : (((pairing x.toMul y.toMul : center c.D):c.D):G)∈c.W := by
      exact c.odd_center.le (pairing x.toMul y.toMul).property
    exact c.rotation_inverts_line _ hw
  simp only [pairingForm_apply,complementLinearAction_apply,toMul_ofMul]
  have hh := congrArg (fun w=>(eZ w).toAdd) hp
  rw [map_inv,toAdd_inv] at hh
  exact hh

/-- Canonical coordinates for the literal source quotient, its actual marked
complement actors and its original commutator pairing. -/
theorem exists_quotient_pairing_coordinates :
    ∃ (E : (c.D ⧸ center c.D) ≃* Multiplicative V) (b : ZMod 3), b≠0 ∧
      (∀ v, (E (c.complementQuotientAction ⟨c.marking.s*c.marking.t,mem_sup_right (mem_zpowers _)⟩ v)).toAdd=
        r (E v).toAdd) ∧
      (∀ v, (E (c.complementQuotientAction ⟨c.actors.y,mem_sup_left (mem_sup_right (mem_zpowers _))⟩ v)).toAdd=
        lin y0 (E v).toAdd) ∧
      (∀ g : c.K, (g:G)∈h.toCentralizerHypothesis.factorData.rightCore → ∃ j : Fin 8, ∀ v,
        (E (c.complementQuotientAction g v)).toAdd=q j (E v).toAdd) ∧
      (∀ j : Fin 8, ∃ g : c.K, (g:G)∈h.toCentralizerHypothesis.factorData.rightCore ∧ ∀ v,
        (E (c.complementQuotientAction g v)).toAdd=q j (E v).toAdd) ∧
      (∀ x y, (c.oddCenterCoordinate (c.oddCommutatorPairing x y)).toAdd=
        b*standardForm (E x).toAdd (E y).toAdd) := by
  obtain ⟨M,hR,hY,hQ,hQ'⟩ := c.exists_marked_quotient_action
  let B := pairingForm c.oddCenterCoordinate
  have hformQ (k : Fin 8) (x y) : B (quaternionWord M.rotation M.reflection k x)
      (quaternionWord M.rotation M.reflection k y)=B x y := by
    obtain ⟨g,hg,hgact⟩ := hQ k
    rw [hgact,hgact]
    exact c.pairingForm_special c.oddCenterCoordinate g (mem_sup_left hg) x y
  have hformR (x y) : B (M.reflection x) (M.reflection y)= -B x y := by
    rw [hR,hR]
    exact c.pairingForm_rotation c.oddCenterCoordinate x y
  obtain ⟨F,b,hb,hFr,hFy,hFQ,hFQ',hFB⟩ := M.exists_marked_form_coordinates
    c.odd_central_quotient_card B (pairingForm_isAlt _) (pairingForm_nondegenerate _)
    hformQ hformR
  let E := F.toAddEquiv.toMultiplicativeRight
  refine ⟨E,b,hb,?_,?_,?_,?_,?_⟩
  · intro v
    have hh := hFr (Additive.ofMul v)
    rw [hR,complementLinearAction_apply] at hh
    exact hh
  · intro v
    have hh := hFy (Additive.ofMul v)
    rw [hY,complementLinearAction_apply] at hh
    exact hh
  · intro g hg
    obtain ⟨k,hk⟩ := hQ' g hg
    obtain ⟨j,hj⟩ := hFQ k
    refine ⟨j,?_⟩
    intro v
    have hh := hj (Additive.ofMul v)
    rw [hk,complementLinearAction_apply] at hh
    exact hh
  · intro j
    obtain ⟨k,hk⟩ := hFQ' j
    obtain ⟨g,hg,hgact⟩ := hQ k
    refine ⟨g,hg,?_⟩
    intro v
    have hh := hk (Additive.ofMul v)
    rw [hgact,complementLinearAction_apply] at hh
    exact hh
  · intro x y
    have hh := hFB (Additive.ofMul x) (Additive.ofMul y)
    change pairingForm c.oddCenterCoordinate (Additive.ofMul x) (Additive.ofMul y)=_ at hh
    rw [pairingForm_apply] at hh
    rw [c.oddCommutatorPairing_eq_pairing]
    exact hh
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
