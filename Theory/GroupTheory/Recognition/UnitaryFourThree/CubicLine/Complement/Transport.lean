module
public import Theory.GroupTheory.MarkedSemidirectProduct
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.Complement.Action

/-!
# Lifting the marked complement action to the original normalizer

An isomorphism of the extraspecial groups compatible with the distinguished
involutions lifts intertwining of the central-quotient actions to intertwining
of the full actions. The internal semidirect-product construction then gives
an isomorphism of the actual normalizers preserving D and K.

This isolates the extension step in Aschbacher, *Sporadic Groups* (1994),
45.11, p.248. The extraspecial and quotient-action identifications remain
explicit inputs to this helper; the finite similitude conjugacy theorem must
supply them before this becomes the source local rigidity theorem.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
variable {G : Type*} [Group G] {z : G} {h : IsType z}
  {P : Sylow 3 (centralizer z)} (c : SourceConfiguration h P)
variable {G' : Type*} [Group G'] [Finite G'] {z' : G'} {h' : IsType z'}
  {P' : Sylow 3 (centralizer z')} (c' : SourceConfiguration h' P')

theorem action_intertwines_of_quotient
    (eD : c.D ≃* c'.D) (eK : c.K ≃* c'.K)
    (hz : c.involutionAction.trans eD = eD.trans c'.involutionAction)
    (hq : ∀ k : c.K,
      quotientAut (center c'.D) (MulAut.congr eD (c.complementAction k)) =
        c'.complementQuotientAction (eK k)) :
    ∀ k : c.K, (c.complementAction k).trans eD =
      eD.trans (c'.complementAction (eK k)) := by
  let : IsExtraspecial 3 c'.D := c'.odd_extraspecial
  have hz' : MulAut.congr eD c.involutionAction = c'.involutionAction := by
    apply MulEquiv.ext
    intro d
    have hh := DFunLike.congr_fun hz (eD.symm d)
    simpa only [MulAut.congr_apply,MulEquiv.trans_apply,MulEquiv.apply_symm_apply] using hh
  intro k
  have hc : Commute c'.involutionAction (MulAut.congr eD (c.complementAction k)) := by
    rw [←hz']
    exact (c.complementAction_commute_involution k).map (MulAut.congr eD)
  have he := IsExtraspecial.aut_eq_of_quotient_eq_of_commute_inversion
    c'.involutionAction (MulAut.congr eD (c.complementAction k))
    (c'.complementAction (eK k)) c'.involutionAction_inverts hc
    (c'.complementAction_commute_involution (eK k)) (hq k)
  apply MulEquiv.ext
  intro d
  have hh := DFunLike.congr_fun he (eD d)
  simpa [MulAut.congr_apply] using hh

/-- Once the actual quotient actions and involutions are intertwined, the
original split normalizers are isomorphic with D and K preserved. -/
theorem normalizer_equiv_of_quotient_actions
    (eD : c.D ≃* c'.D) (eK : c.K ≃* c'.K)
    (hz : c.involutionAction.trans eD = eD.trans c'.involutionAction)
    (hq : ∀ k : c.K,
      quotientAut (center c'.D) (MulAut.congr eD (c.complementAction k)) =
        c'.complementQuotientAction (eK k)) :
    ∃ e : normalizer (c.W : Set G) ≃* normalizer (c'.W : Set G'),
      (c.D.subgroupOf (normalizer (c.W : Set G))).map e.toMonoidHom =
        c'.D.subgroupOf (normalizer (c'.W : Set G')) ∧
      (c.K.subgroupOf (normalizer (c.W : Set G))).map e.toMonoidHom =
        c'.K.subgroupOf (normalizer (c'.W : Set G')) := by
  exact Theory.GroupTheory.exists_markedSemidirectTransport
    _ c.D c.K c.complement_product.symm c.complement_normalizes_odd c.complement_disjoint
    _ c'.D c'.K c'.complement_product.symm c'.complement_normalizes_odd c'.complement_disjoint
    eD eK (c.action_intertwines_of_quotient c' eD eK hz hq)
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceConfiguration
