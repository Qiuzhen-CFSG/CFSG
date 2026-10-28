module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.Complement.ActionComparison
public import Theory.GroupTheory.MarkedSemidirectRestriction

/-!
# The original normalizer equivalence with its marked actors

Compatible commutator-space and complement equivalences lift to the actual
extraspecial groups and their split normalizers. The split-product map
retains the specific complement map, so it preserves the original selected
cubic and the rotation, in addition to D and K.

Source: Aschbacher, *Sporadic Groups* (1994), 45.11, p.248.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
  {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)
  {G' : Type*} [Group G'] [Finite G'] {z' : G'} {h' : IsType z'}
  {P' : Sylow 3 (centralizer z')} (c' : SourceConfiguration h' P')

/-- Original normalizer comparison, retaining the selected cubic and rotation. -/
theorem exists_marked_normalizer_equiv :
    ∃ e : normalizer (c.W : Set G) ≃* normalizer (c'.W : Set G'),
      (c.D.subgroupOf (normalizer (c.W : Set G))).map e.toMonoidHom =
        c'.D.subgroupOf (normalizer (c'.W : Set G')) ∧
      (c.K.subgroupOf (normalizer (c.W : Set G))).map e.toMonoidHom =
        c'.K.subgroupOf (normalizer (c'.W : Set G')) ∧
      (∀ hy hy', e ⟨c.actors.y,hy⟩=⟨c'.actors.y,hy'⟩) ∧
      (∀ hr hr', e ⟨c.marking.s*c.marking.t,hr⟩=⟨c'.marking.s*c'.marking.t,hr'⟩) := by
  obtain ⟨eQ,eZ,eK,hp,ha,hy,hr⟩ := c.exists_pairing_action_equivalences c'
  let eD := c.extraspecialEquivOfPairing c' eQ eZ hp
  have hq (k : c.K) : quotientAut (center c'.D) (MulAut.congr eD (c.complementAction k))=
      c'.complementQuotientAction (eK k) := by
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
  have hact := c.action_intertwines_of_quotient c' eD eK
    (c.extraspecialEquivOfPairing_involution c' eQ eZ hp) hq
  obtain ⟨e,hD,hK,heK⟩ := Theory.GroupTheory.exists_markedSemidirectTransport_restriction
    _ c.D c.K c.complement_product.symm c.complement_normalizes_odd c.complement_disjoint
    _ c'.D c'.K c'.complement_product.symm c'.complement_normalizes_odd c'.complement_disjoint
    eD eK hact
  refine ⟨e,hD,hK,?_,?_⟩
  · intro hY hY'
    apply Subtype.ext
    have hh := heK ⟨c.actors.y,mem_sup_left (mem_sup_right (mem_zpowers _))⟩
    rw [hy] at hh
    exact hh
  · intro hR hR'
    apply Subtype.ext
    have hh := heK ⟨c.marking.s*c.marking.t,mem_sup_right (mem_zpowers _)⟩
    rw [hr] at hh
    exact hh
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
