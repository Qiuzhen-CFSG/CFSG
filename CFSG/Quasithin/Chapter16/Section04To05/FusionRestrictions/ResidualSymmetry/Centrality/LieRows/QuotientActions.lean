module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.LieRows.Actions

/-!
# Central-quotient markings for the remaining Lie families

The actual component image in N(L)/C(L) maps to the inner automorphisms
of a specified model of L/Z(L). Perfectness makes this map injective,
so it preserves the actor order and the Sylow-centrality marking.
This does not identify residuals through different central kernels.

The catalogue reduction transports the surviving source models from
L/O₂(L) to L/Z(L), excluding only the supplied Bender alternative. Every
rank-two parameter and derived endpoint is retained.

Source: Aschbacher–Smith, 16.1.2–4 and 16.5.6(4), pp.1170–1172,1197.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows
open Subgroup Theory.GroupTheory

variable {G H : Type*} [Group G] [Group H] {L : Subgroup G}

/-- The existing faithful marked action on the central quotient model. -/
abbrev quotientModelAction (e : (L ⧸ center L) ≃* H) :
    ActionQuotient L →* MulAut H := OrderTwo.CentralizerCases.modelAction L e

/-- The actor is the action induced by its actual lift in the normalizer. -/
theorem quotientModelAction_actor (e : (L ⧸ center L) ≃* H)
    (u : normalizer (L : Set G)) :
    quotientModelAction e (actionMap le_rfl u) =
      MulAut.centralQuotientAction e (L.normalizerMonoidHom u) := rfl

/-- Inner images are marked by the specified center quotient map. -/
theorem quotientModelAction_inner (e : (L ⧸ center L) ≃* H) (x : L) :
    quotientModelAction e (actionMap L.le_normalizer x) =
      MulAut.conj (e (QuotientGroup.mk' (center L) x)) := by
  change MulAut.centralQuotientAction e
    (L.normalizerMonoidHom (inclusion L.le_normalizer x)) = _
  have he : L.normalizerMonoidHom (inclusion L.le_normalizer x) = MulAut.conj x := by
    ext y
    rfl
  rw [he, MulAut.centralQuotientAction_conj]

/-- The component maps onto the inner subgroup of the quotient model. -/
theorem quotientModelAction_component (e : (L ⧸ center L) ≃* H) :
    (componentImage L).map (quotientModelAction e) = MulAut.innerSubgroup H := by
  ext a
  constructor
  · rintro ⟨b, ⟨x, rfl⟩, rfl⟩
    exact ⟨e (QuotientGroup.mk' (center L) x), (quotientModelAction_inner e x).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨y, rfl⟩ := e.surjective x
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (center L) y
    exact ⟨actionMap L.le_normalizer z, ⟨z, rfl⟩, quotientModelAction_inner e z⟩

/-- Perfectness ensures that quotienting the component loses no actor order. -/
theorem quotientModelAction_order [Group.IsPerfect L]
    (e : (L ⧸ center L) ≃* H) (u : normalizer (L : Set G)) :
    orderOf (quotientModelAction e (actionMap le_rfl u)) =
      orderOf (actionMap le_rfl u) :=
  orderOf_injective (quotientModelAction e)
    (OrderTwo.CentralizerCases.modelAction_injective L e) _

/-- Both directions of the Sylow marking, with the central kernel retained. -/
theorem quotientModelAction_twoCentral_iff [Finite G] [Finite H] [Group.IsPerfect L]
    (e : (L ⧸ center L) ≃* H) (a : ActionQuotient L) :
    IsTwoCentralIn (MulAut.innerSubgroup H) (quotientModelAction e a) ↔
      IsTwoCentralIn (componentImage L) a := by
  rw [← quotientModelAction_component e]
  exact twoCentral_map_injective_iff _ (OrderTwo.CentralizerCases.modelAction_injective L e)

/-- The residual image is the genuine model fixed two-residual. This is an
isomorphism only of the image; no covering kernel is asserted to be trivial. -/
noncomputable def quotientResidualEquiv [Finite G] [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) (e : (L ⧸ center L) ≃* H)
    (u : normalizer (L : Set G)) :
    SylowSymmetry.ReverseDelta.centralImage L (involutionTwoResidual L u.val) ≃*
      pResidual 2 (quotientModelAction e (actionMap le_rfl u)).fixedSubgroup :=
  SylowSymmetry.ReverseDelta.Comparison.centralImageModelEquiv hodd e u.property

/-- Reduction to precisely the remaining rank-two and higher-linear models. -/
theorem surviving_quotient_models [Finite G] [IsQuasisimple L]
    (hodd : pPrimeCore 2 L = ⊥) (hL : IsEvenTypeLieComponent L)
    (hb : ¬ ClassificationModels.IsBenderModel (L ⧸ center L)) :
    (∃ f, ChapterA.Section02.IsTheoremCRankTwoModel (L ⧸ center L) f) ∨
      ∃ n, (n = 4 ∨ n = 5) ∧ ClassicalGroup.IsPSL (L ⧸ center L) n 2 := by
  let e := LiePreliminaries.centerQuotientEquivTwoCore hodd
  rcases hL.1 with h | h | h
  · exact (hb (h.of_mulEquiv e)).elim
  · obtain ⟨f, hf⟩ := h
    exact Or.inl ⟨f, hf.of_mulEquiv e⟩
  · obtain ⟨n, hn, hm⟩ := h
    exact Or.inr ⟨n, hn, hm.of_mulEquiv e⟩

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows
