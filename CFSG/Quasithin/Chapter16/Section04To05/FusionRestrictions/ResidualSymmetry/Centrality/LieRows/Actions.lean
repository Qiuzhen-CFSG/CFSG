module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Centrality.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.OrderTwo.CentralizerCases.Basic
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.Transport
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.GroupTheory.PResidual.CoprimeIndexValuation
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Actions and residual order invariants for the Lie rows

The normalizer quotient embeds faithfully in the automorphism group of a
specified model of the full component. Its component image maps to the
actual inner automorphism subgroup. Two-centrality transports through this
embedding, using genuine Sylow subgroups in both directions.

The two-part of the modified residual has the same order as the two-part
of the ordinary fixed two-residual. Thus a table comparison may use this
invariant without suppressing the O³ modification or proving unrelated
disjointness of model catalogues. These tools do not assert row separation.

Source: Aschbacher–Smith, 16.1.3–4 and 16.5.5–6(4), printed pp.1171,1197.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows
open Subgroup

variable {G H : Type*} [Group G] [Group H]

/-- An embedding preserves two-centrality in the image of the specified
subgroup; the ambient target need not be the whole image. -/
theorem twoCentral_map_injective_iff [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Injective f) {L : Subgroup G} {u : G} :
    IsTwoCentralIn (L.map f) (f u) ↔ IsTwoCentralIn L u := by
  let e := L.equivMapOfInjective f hf
  constructor
  · rintro ⟨hu, S, ⟨P, rfl⟩, huP, hc⟩
    let Q := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    refine ⟨(orderOf_injective f hf u).symm.trans hu,
      (Q : Subgroup L).map L.subtype, ⟨Q, rfl⟩, ?_, ?_⟩
    · obtain ⟨x, hx, he⟩ := huP
      refine ⟨e.symm x, mem_map.mpr ⟨x, hx, rfl⟩, ?_⟩
      apply hf
      exact (congrArg Subtype.val (e.apply_symm_apply x)).trans he
    · rintro y ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      apply hf
      have hh := mem_centralizer_singleton_iff.mp
        (hc (mem_map_of_mem (L.map f).subtype hz))
      have he : f (e.symm z : G) = z :=
        congrArg Subtype.val (e.apply_symm_apply z)
      rw [map_mul, map_mul]
      change f ((e.symm z : L) : G) * f u = f u * f ((e.symm z : L) : G)
      rw [he]
      exact hh
  · rintro ⟨hu, S, ⟨P, rfl⟩, huP, hc⟩
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    refine ⟨(orderOf_injective f hf u).trans hu,
      (Q : Subgroup (L.map f)).map (L.map f).subtype, ⟨Q, rfl⟩, ?_, ?_⟩
    · obtain ⟨x, hx, rfl⟩ := huP
      exact mem_map.mpr ⟨e x, mem_map.mpr ⟨x, hx, rfl⟩, rfl⟩
    · rintro y ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      change f (z : G) * f u = f u * f (z : G)
      simpa only [map_mul, subtype_apply] using congrArg f
        (mem_centralizer_singleton_iff.mp (hc (mem_map_of_mem L.subtype hz)))

variable {L : Subgroup G}

/-- The faithful action on a model of the full component, retaining its center. -/
noncomputable def fullModelAction (e : L ≃* H) : ActionQuotient L →* MulAut H :=
  (MulAut.congr e).toMonoidHom.comp (OrderTwo.CentralizerCases.quotientAction L)

theorem fullModelAction_injective (e : L ≃* H) :
    Function.Injective (fullModelAction e) :=
  (MulAut.congr e).injective.comp (OrderTwo.CentralizerCases.quotientAction_injective L)

/-- The actor in the normalizer quotient induces its actual conjugation action. -/
theorem fullModelAction_actor (e : L ≃* H) (u : normalizer (L : Set G)) :
    fullModelAction e (actionMap le_rfl u) = MulAut.congr e (L.normalizerMonoidHom u) := rfl

/-- Inner elements retain their specified model images. -/
theorem fullModelAction_inner (e : L ≃* H) (x : L) :
    fullModelAction e (actionMap L.le_normalizer x) = MulAut.conj (e x) := by
  change MulAut.congr e (L.normalizerMonoidHom (inclusion L.le_normalizer x)) = _
  have he : L.normalizerMonoidHom (inclusion L.le_normalizer x) = MulAut.conj x := by
    ext y
    rfl
  rw [he, MulAut.congr_conj]

/-- The component maps onto the whole inner automorphism subgroup of the model. -/
theorem fullModelAction_component (e : L ≃* H) :
    (componentImage L).map (fullModelAction e) = MulAut.innerSubgroup H := by
  ext a
  constructor
  · rintro ⟨b, ⟨x, rfl⟩, rfl⟩
    exact ⟨e x, (fullModelAction_inner e x).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨actionMap L.le_normalizer (e.symm x), ⟨e.symm x, rfl⟩, ?_⟩
    rw [fullModelAction_inner, e.apply_symm_apply]

/-- The row marking tests two-centrality in the actual inner subgroup. -/
theorem fullModelAction_twoCentral_iff [Finite G] [Finite H]
    (e : L ≃* H) (a : ActionQuotient L) :
    IsTwoCentralIn (MulAut.innerSubgroup H) (fullModelAction e a) ↔
      IsTwoCentralIn (componentImage L) a := by
  rw [← fullModelAction_component e]
  exact twoCentral_map_injective_iff _ (fullModelAction_injective e)

/-- The full fixed two-residual is transported, before any central quotient. -/
noncomputable def fullResidualEquiv (e : L ≃* H) (u : normalizer (L : Set G)) :
    involutionTwoResidual L u.val ≃*
      pResidual 2 (fullModelAction e (actionMap le_rfl u)).fixedSubgroup := by
  let c := (SylowSymmetry.ReverseDelta.Comparison.fixedCentralizerEquiv u.property).symm.trans
    (MulAut.fixedSubgroupCongr e (L.normalizerMonoidHom u))
  exact ((pResidual 2 (L ⊓ centralizer ({u.val} : Set G) : Subgroup G)).equivMapOfInjective
    (L ⊓ centralizer ({u.val} : Set G)).subtype (subtype_injective _)).symm.trans
    (((pResidual 2 _).equivMapOfInjective c.toMonoidHom c.injective).trans
      (MulEquiv.subgroupCongr (map_pResidual 2 c)))

/-- The O³ modification never changes the two-part of a residual order. -/
theorem modifiedResidual_twoValuation [Finite G] (u : G) :
    padicValNat 2 (Nat.card (modifiedCentralizerResidual L u)) =
      padicValNat 2 (Nat.card (involutionTwoResidual L u)) := by
  classical
  unfold modifiedCentralizerResidual
  split_ifs
  · rw [Nat.card_congr ((pResidual 3 (involutionTwoResidual L u)).equivMapOfInjective
      (involutionTwoResidual L u).subtype (subtype_injective _)).toEquiv.symm]
    exact pResidual_card_padicValNat 2 3 (by decide)
  · rfl

/-- An isomorphism of modified residuals forces equality of the two-parts
of their full model fixed two-residuals. -/
theorem fixedResidual_twoValuation_eq [Finite G] (e : L ≃* H)
    (u v : normalizer (L : Set G))
    (d : modifiedCentralizerResidual L u.val ≃* modifiedCentralizerResidual L v.val) :
    padicValNat 2 (Nat.card (pResidual 2
      (fullModelAction e (actionMap le_rfl u)).fixedSubgroup)) =
    padicValNat 2 (Nat.card (pResidual 2
      (fullModelAction e (actionMap le_rfl v)).fixedSubgroup)) := by
  rw [← Nat.card_congr (fullResidualEquiv e u).toEquiv,
    ← Nat.card_congr (fullResidualEquiv e v).toEquiv,
    ← modifiedResidual_twoValuation, ← modifiedResidual_twoValuation,
    Nat.card_congr d.toEquiv]

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Centrality.LieRows
