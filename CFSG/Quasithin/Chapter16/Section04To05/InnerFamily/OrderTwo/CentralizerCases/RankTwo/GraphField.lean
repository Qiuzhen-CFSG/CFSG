module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.InnerExclusions
public import Theory.SpecificGroups.PSL3Four.GraphFieldTransport
public import Theory.GroupAction.AutomorphismFixerTransport

/-!
# Marked transport of the PSL₃(4) graph-field branch

A compatible equivalence carries the actual projected O²(C_L(r)) onto the
concrete graph-field residual in PSL₃(4). It also identifies their full
pointwise automorphism fixers. The permitted bound for that concrete fixer
therefore gives case (I), including for central covers of the component.

The final corollary constructs the marking from conjugacy of the actual
quotient actor to inverse transpose times Frobenius. Conjugacy is the
branch condition supplied by the earlier involution classification; it
asserts neither a residual isomorphism nor a centralizer bound. Classification
of all rank-two actors and the other fixer calculations remain separate.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4(5) and the proof of 16.4.9(1), printed pp.1171 and 1189.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.RankTwo
open Subgroup Theory.GroupTheory OuterResidual
open Matrix.PSL3Four
variable {G S : Type*} [Group G] [Finite G] [Group S]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The marked ambient map carries the actual residual onto the concrete subgroup. -/
theorem graphField_modelResidual_map [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) (e : (L ⧸ center L) ≃* S)
    (d : S ≃* PSL) (hn : r ∈ normalizer (L : Set G))
    (ha : ∀ x, d (modelAction L e (actionElement L r hn) x) =
      (Matrix.PSL3.OuterSolvable.graph F * pslFrobenius) (d x)) :
    (modelResidual L e r).map d.toMonoidHom = projectiveGraphFieldResidual := by
  rw [modelResidual_eq_fixedTwoResidual L e r hn hodd]
  exact MulAut.map_embedded_fixedResidual_of_compatible 2 d _ _ ha

/-- Transport identifies the full pointwise fixers, with no standard-automorphism restriction. -/
noncomputable def graphField_fixerEquiv [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) (e : (L ⧸ center L) ≃* S)
    (d : S ≃* PSL) (hn : r ∈ normalizer (L : Set G))
    (ha : ∀ x, d (modelAction L e (actionElement L r hn) x) =
      (Matrix.PSL3.OuterSolvable.graph F * pslFrobenius) (d x)) :
    fixingSubgroup (MulAut S) (modelResidual L e r : Set S) ≃*
      fixingSubgroup (MulAut PSL) (projectiveGraphFieldResidual : Set PSL) :=
  MulAut.fixingSubgroupEquivOfMap d _ _ (graphField_modelResidual_map hodd e d hn ha)

/-- The one permitted concrete fixer bound proves the graph-field branch. -/
theorem graphField_alternative
    (hG : HasEvenTypeCentralizers G) (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (e : (L ⧸ center L) ≃* S)
    (d : S ≃* PSL)
    (ha : ∀ x, d (modelAction L e
      (actionElement L r (h.sylow_normalizes (h.le_sylow hr))) x) =
      (Matrix.PSL3.OuterSolvable.graph F * pslFrobenius) (d x))
    (hfix : ¬ 4 ∣ Nat.card
      (fixingSubgroup (MulAut PSL) (projectiveGraphFieldResidual : Set PSL))) :
    ResidualCentralizerAlternative T L r := by
  let := h.component.quasisimple
  let : Finite S := Finite.of_equiv (L ⧸ center L) e.toEquiv
  apply alternative_of_fixer_not_four_dvd L e h hr hr2
  rwa [Nat.card_congr (graphField_fixerEquiv
    (component_oddCore hG h.toCentralComponentSetup) e d
    (h.sylow_normalizes (h.le_sylow hr)) ha).toEquiv]

/-- An arbitrary conjugate graph-field actor inherits the bound through its actual marking. -/
theorem graphField_alternative_of_isConj
    (hG : HasEvenTypeCentralizers G) (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2) (e : (L ⧸ center L) ≃* PSL)
    (ha : IsConj (modelAction L e
      (actionElement L r (h.sylow_normalizes (h.le_sylow hr))))
      (Matrix.PSL3.OuterSolvable.graph F * pslFrobenius))
    (hfix : ¬ 4 ∣ Nat.card
      (fixingSubgroup (MulAut PSL) (projectiveGraphFieldResidual : Set PSL))) :
    ResidualCentralizerAlternative T L r := by
  obtain ⟨d, hd⟩ := isConj_iff.mp ha
  apply graphField_alternative hG h hr hr2 e d _ hfix
  intro x
  have hx := congrArg (fun a : MulAut PSL => a (d x)) hd
  change d (modelAction L e
    (actionElement L r (h.sylow_normalizes (h.le_sylow hr))) (d.symm (d x))) = _ at hx
  simpa only [d.symm_apply_apply] using hx

/-- The branch calculation over any four-element coefficient field, with an
arbitrary conjugate of inverse transpose times the squaring automorphism. -/
theorem graphField_alternative_of_field_isConj
    {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    (σ : K ≃+* K) (hσ : ∀ x, σ x = x ^ 2)
    (hG : HasEvenTypeCentralizers G) (h : IntersectionSetup T z L g R)
    (hr : r ∈ R) (hr2 : orderOf r = 2)
    (e : (L ⧸ center L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K)
    (ha : IsConj (modelAction L e
      (actionElement L r (h.sylow_normalizes (h.le_sylow hr))))
      (Matrix.PSL3.OuterSolvable.graph K * Matrix.PSL3.OuterSolvable.fieldAction K σ))
    (hfix : ¬ 4 ∣ Nat.card
      (fixingSubgroup (MulAut PSL) (projectiveGraphFieldResidual : Set PSL))) :
    ResidualCentralizerAlternative T L r := by
  obtain ⟨d, hd⟩ := exists_graphField_marking hK σ hσ _ ha
  exact graphField_alternative hG h hr hr2 e d hd hfix

end CFSG.Quasithin.Chapter16.Intersections.OrderTwo.CentralizerCases.RankTwo
