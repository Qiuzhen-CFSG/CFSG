module
public import Theory.GroupTheory.CubicCentralInversion
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.Complement.Transport

/-!
# Constructing the original extraspecial identification from its pairing

The distinguished involution of the source configuration satisfies cubic
central inversion on the literal odd core. Its quotient and norm coordinates
therefore construct an extraspecial group isomorphism from any compatible
central-quotient and center isomorphisms, automatically preserving the
involution. The original normalizer consumer now needs only the commutator
space and complement-action identifications; it assumes no group-level lift.

Source: Aschbacher, *Sporadic Groups* (1994), 45.11, p.248.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] {z : G} {h : IsType z}
  {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)

theorem cubicCentralInversion : Theory.GroupTheory.CubicCentralInversion c.involutionAction where
  center_cube d := by
    apply Subtype.ext
    apply Subtype.ext
    exact c.odd_cube d.val d.val.property
  involutive d := by
    let zK : c.K := ⟨z,c.involution_mem_complement⟩
    have hz2 : zK^2=1 := Subtype.ext (h.involution ▸ pow_orderOf_eq_one z)
    have ha2 : c.involutionAction*c.involutionAction=1 := by
      change c.complementAction zK * c.complementAction zK=1
      rw [←map_mul,←pow_two,hz2,map_one]
    exact DFunLike.congr_fun ha2 d
  norm_central d := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (center c.D) (d*c.involutionAction d)=1
    have hd : QuotientGroup.mk' (center c.D) (c.involutionAction d) =
        (QuotientGroup.mk' (center c.D) d)⁻¹ := by
      simpa only [quotientAut_apply_mk] using c.involutionAction_inverts d
    rw [map_mul,hd,mul_inv_cancel]
  fixes_center d := by
    have hd : (d:c.D) ∈ c.W.subgroupOf c.D := c.odd_center ▸ d.property
    have hdC : ((d:c.D):G) ∈ centralizer z := (c.odd_fixed.symm ▸ hd).2
    apply Subtype.ext
    change z*((d:c.D):G)*z⁻¹=((d:c.D):G)
    rw [←mem_centralizer_singleton_iff.mp hdC,mul_inv_cancel_right]

def oddCommutatorPairing : (c.D ⧸ center c.D) →*
    ((c.D ⧸ center c.D) →* center c.D) := by
  let := c.odd_extraspecial.quotient_elementary_abelian
  exact Theory.GroupTheory.CentralQuotient.pairing

@[simp] theorem oddCommutatorPairing_eq_pairing :
    letI := c.odd_extraspecial.quotient_elementary_abelian
    c.oddCommutatorPairing=Theory.GroupTheory.CentralQuotient.pairing := by rfl

variable {G' : Type*} [Group G'] {z' : G'} {h' : IsType z'}
  {P' : Sylow 3 (centralizer z')} (c' : SourceConfiguration h' P')

noncomputable def extraspecialEquivOfPairing
    (eQ : (c.D ⧸ center c.D) ≃* (c'.D ⧸ center c'.D))
    (eZ : center c.D ≃* center c'.D)
    (hp : ∀ q r, eZ (c.oddCommutatorPairing q r) =
      c'.oddCommutatorPairing (eQ q) (eQ r)) : c.D ≃* c'.D := by
  let := c.odd_extraspecial.quotient_elementary_abelian
  let := c'.odd_extraspecial.quotient_elementary_abelian
  exact c.cubicCentralInversion.lift c'.cubicCentralInversion eQ eZ hp
@[simp] theorem extraspecialEquivOfPairing_quotient
    (eQ : (c.D ⧸ center c.D) ≃* (c'.D ⧸ center c'.D))
    (eZ : center c.D ≃* center c'.D)
    (hp : ∀ q r, eZ (c.oddCommutatorPairing q r) = c'.oddCommutatorPairing (eQ q) (eQ r))
    (d : c.D) : QuotientGroup.mk' (center c'.D) (c.extraspecialEquivOfPairing c' eQ eZ hp d) =
      eQ (QuotientGroup.mk' (center c.D) d) := by
  let := c.odd_extraspecial.quotient_elementary_abelian
  let := c'.odd_extraspecial.quotient_elementary_abelian
  exact c.cubicCentralInversion.lift_quotient c'.cubicCentralInversion eQ eZ hp d

theorem extraspecialEquivOfPairing_involution
    (eQ : (c.D ⧸ center c.D) ≃* (c'.D ⧸ center c'.D))
    (eZ : center c.D ≃* center c'.D)
    (hp : ∀ q r, eZ (c.oddCommutatorPairing q r) = c'.oddCommutatorPairing (eQ q) (eQ r)) :
    c.involutionAction.trans (c.extraspecialEquivOfPairing c' eQ eZ hp) =
      (c.extraspecialEquivOfPairing c' eQ eZ hp).trans c'.involutionAction := by
  let := c.odd_extraspecial.quotient_elementary_abelian
  let := c'.odd_extraspecial.quotient_elementary_abelian
  apply MulEquiv.ext
  intro d
  exact c.cubicCentralInversion.lift_involution c'.cubicCentralInversion eQ eZ hp d

variable [Finite G']

theorem normalizer_equiv_of_pairing_actions
    (eQ : (c.D ⧸ center c.D) ≃* (c'.D ⧸ center c'.D))
    (eZ : center c.D ≃* center c'.D) (eK : c.K ≃* c'.K)
    (hp : ∀ q r, eZ (c.oddCommutatorPairing q r) = c'.oddCommutatorPairing (eQ q) (eQ r))
    (ha : ∀ k q, eQ (c.complementQuotientAction k q) =
      c'.complementQuotientAction (eK k) (eQ q)) :
    ∃ e : normalizer (c.W : Set G) ≃* normalizer (c'.W : Set G'),
      (c.D.subgroupOf (normalizer (c.W : Set G))).map e.toMonoidHom =
        c'.D.subgroupOf (normalizer (c'.W : Set G')) ∧
      (c.K.subgroupOf (normalizer (c.W : Set G))).map e.toMonoidHom =
        c'.K.subgroupOf (normalizer (c'.W : Set G')) := by
  let eD := c.extraspecialEquivOfPairing c' eQ eZ hp
  apply c.normalizer_equiv_of_quotient_actions c' eD eK
    (c.extraspecialEquivOfPairing_involution c' eQ eZ hp)
  intro k
  apply MulEquiv.ext
  intro q'
  obtain ⟨q,rfl⟩ := eQ.surjective q'
  obtain ⟨d,rfl⟩ := QuotientGroup.mk'_surjective (center c.D) q
  have hd := c.extraspecialEquivOfPairing_quotient c' eQ eZ hp d
  calc
    quotientAut (center c'.D) (MulAut.congr eD (c.complementAction k))
        (eQ (QuotientGroup.mk' (center c.D) d)) =
      quotientAut (center c'.D) (MulAut.congr eD (c.complementAction k))
        (QuotientGroup.mk' (center c'.D) (eD d)) := by rw [hd]
    _ = QuotientGroup.mk' (center c'.D) (eD (c.complementAction k d)) := by
      rw [quotientAut_apply_mk,MulAut.congr_apply]
      simp only [MulEquiv.trans_apply,MulEquiv.symm_apply_apply]
    _ = eQ (QuotientGroup.mk' (center c.D) (c.complementAction k d)) :=
      c.extraspecialEquivOfPairing_quotient c' eQ eZ hp _
    _ = eQ (c.complementQuotientAction k (QuotientGroup.mk' (center c.D) d)) := by
      rw [complementQuotientAction,MonoidHom.comp_apply,quotientAut_apply_mk]
    _ = c'.complementQuotientAction (eK k) (eQ (QuotientGroup.mk' (center c.D) d)) := ha _ _
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
