module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Lie.Basic
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.Quotient
public import Theory.GroupAction.PerfectCentralQuotient.ComponentImage
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Projecting the embedded component in the classical field rows

The actual central cover of I gives an involution of order two on any specified
quotient model. Its fixed subgroup contains the projected L as a component,
including fixed quotient elements that do not lift to fixed elements upstairs.
Restricting the cover to L preserves its quotient by the center. Condition (E1)
then identifies this quotient with the original L/O₂(L), so the smaller endpoint
remains the genuine derived group at the square-root field order.

`ComponentFixerBound` states the remaining intrinsic calculation. It retains the
actual embedded component, its two-group center, and its central quotient; neither an abstract group
isomorphism nor a fixed-group table alone proves that calculation. The finite,
simple, and perfect hypotheses on the ambient model are inherited from I.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.4(4),
16.1.7(3a), and 16.3.5, printed pp.1171–1173 and 1178–1179.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldClassical
open Subgroup Theory.GroupTheory PerfectCentralCovering
open CounterexampleGeometry.CoveredPersistence
universe u v

/-- The unproved model calculation for one field family. Its component is an
actual subgroup of the involution fixed group, not merely an isomorphism type. -/
def ComponentFixerBound (X : FieldFamily) : Prop :=
  ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S] [Group.IsPerfect S]
    (n : ℕ), 1 ≤ n → X.ModelAt S (2 ^ (2 * n)) →
    ∀ (a : MulAut S), orderOf a = 2 → ∀ P : Subgroup S,
      IsComponentIn P a.fixedSubgroup →
      IsPGroup 2 (center P) →
      X.DerivedAt (P ⧸ center P) (2 ^ n) →
      Nat.card (fixingSubgroup (MulAut S) (P : Set S)) < 4

variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
variable {E L I : Subgroup G} {t i : G} {S : Type v} [Group S]

/-- The source quotient comparison, expressed as a quotient by the center. -/
noncomputable def centerModelEquiv (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) :
    (I ⧸ center I) ≃* S :=
  (QuotientGroup.quotientMulEquivOfEq
    (hG.evenType.component_center_eq_twoCore h.setup.involution_i h.component)).trans e

/-- The image of the actual embedded L under the prescribed model map. -/
noncomputable def projected (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) : Subgroup S :=
  (L.subgroupOf I).map (h.coreCover hG e).toMonoidHom

/-- The descended action of the distinguished involution. -/
noncomputable def modelAction (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) : MulAut S :=
  MulAut.centralQuotientAction (centerModelEquiv h hG e) h.involutionAction

/-- Faithful central descent preserves order two. -/
theorem modelAction_order (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) :
    orderOf (modelAction h hG e) = 2 := by
  let := h.component.quasisimple
  exact (orderOf_injective _ (MulAut.centralQuotientAction_injective
    (centerModelEquiv h hG e)) _).trans h.involutionAction_orderOf

private theorem projected_eq (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) :
    projected h hG e = ((L.subgroupOf I).map (QuotientGroup.mk' (center I))).map
      (centerModelEquiv h hG e).toMonoidHom := by
  rw [Subgroup.map_map]
  rfl

private theorem map_fixed {A B : Type*} [Group A] [Group B]
    (a : MulAut A) (e : A ≃* B) :
    a.fixedSubgroup.map e.toMonoidHom = (MulAut.congr e a).fixedSubgroup := by
  ext x
  rw [mem_map_equiv, MulAut.mem_fixedSubgroup, MulAut.mem_fixedSubgroup]
  change a (e.symm x) = e.symm x ↔ e (a (e.symm x)) = x
  rw [← e.apply_symm_apply x, e.injective.eq_iff]
  simp only [e.symm_apply_apply]

/-- The image is a component of the full fixed subgroup downstairs. -/
theorem projected_component (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) :
    IsComponentIn (projected h hG e) (modelAction h hG e).fixedSubgroup := by
  have hc := (MulAut.component_image_in_quotient_fixed h.involutionAction
    (L.subgroupOf I) h.component_in_action_fixed).map (centerModelEquiv h hG e)
  rw [← projected_eq h hG e, map_fixed] at hc
  exact hc

/-- Restrict the actual central cover to L and its image. -/
noncomputable def projectedCover (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) :
    Cover L (projected h hG e) where
  toMonoidHom := ((h.coreCover hG e).toMonoidHom.subgroupMap (L.subgroupOf I)).comp
    (subgroupOfEquivOfLe h.proper.le).symm.toMonoidHom
  surjective := (MonoidHom.subgroupMap_surjective _ _).comp
    (subgroupOfEquivOfLe h.proper.le).symm.surjective
  isPerfect := h.setup.component.quasisimple.toIsPerfect
  ker_le_center := by
    intro x hx
    have hx' : (⟨(x : G), h.proper.le x.property⟩ : I) ∈
        (h.coreCover hG e).toMonoidHom.ker := congrArg Subtype.val hx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (congrArg (fun z : I => (z : G))
      (mem_center_iff.mp ((h.coreCover hG e).ker_le_center hx')
        ⟨(y : G), h.proper.le y.property⟩))

/-- The image has exactly the source central quotient of L. -/
noncomputable def projectedCenterEquiv (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) :
    (projected h hG e ⧸ center (projected h hG e)) ≃* (L ⧸ pCore 2 L) :=
  (projectedCover h hG e).quotientCenterEquiv.symm.trans
    (QuotientGroup.quotientMulEquivOfEq
      (hG.evenType.component_center_eq_twoCore h.setup.involution_t h.setup.component))

/-- The projected component retains the two-group center supplied by (E1). -/
theorem projected_center_isTwoGroup (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S) :
    IsPGroup 2 (center (projected h hG e)) := by
  let f := projectedCover h hG e
  have hmap : (center L).map f.toMonoidHom = center (projected h hG e) := by
    rw [← f.comap_center, Subgroup.map_comap_eq_self]
    rw [f.toMonoidHom.range_eq_top_of_surjective f.surjective]
    exact le_top
  have hz : IsPGroup 2 (center L) := by
    rw [hG.evenType.component_center_eq_twoCore h.setup.involution_t h.setup.component]
    exact pCore_isPGroup
  rw [← hmap]
  exact hz.map f.toMonoidHom

/-- Preserve the derived endpoint without identifying it with the full group. -/
theorem projected_derived (h : PairContext E L I t i)
    (hG : Hypothesis1611 𝒦 G) (e : (I ⧸ pCore 2 I) ≃* S)
    (X : FieldFamily) (q : ℕ) (hsmall : X.DerivedAt (L ⧸ pCore 2 L) q) :
    X.DerivedAt (projected h hG e ⧸ center (projected h hG e)) q := by
  obtain ⟨M, hM, hfin, hm, ⟨d⟩⟩ := hsmall
  exact ⟨M, hM, hfin, hm, ⟨(projectedCenterEquiv h hG e).trans d⟩⟩

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction.CentralizerCalculation.FieldClassical
