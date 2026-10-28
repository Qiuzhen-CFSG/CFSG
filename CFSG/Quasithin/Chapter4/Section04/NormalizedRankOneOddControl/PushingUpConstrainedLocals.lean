module

public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpConstrainedAction
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.LinearLeviLocals
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedG2Normality
public import CFSG.Quasithin.ChapterC.Section04.A5LinearThreeNormality

/-!
# Large constrained rows in the normalized rank-one argument

Transfer the literal radical intersection through the star and central
quotients. The nontrivial intersection and the action with soluble kernel
place the marked simple section in a binary linear-Levi local subgroup.
Its two-subgroup exponent then excludes the degree-three linear,
symplectic and G2 rows.

Source: Aschbacher--Smith C.2.7 and 4.2.12--13, pp.146--147,610--612.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open ChapterC.Section04Constrained
variable {G S : Type*} [Group G] [Finite G] [Group S] [Finite S] [IsSimpleGroup S]
variable {H M F R W : Subgroup G}

omit [Finite G] in
private theorem intrinsic_intersection_ne_bot
    (K : Subgroup H) (hn : coreCentralIntersectionImage (K.map H.subtype) R ≠ ⊥) :
    coreCentralIntersectionImage K (R.subgroupOf H) ≠ ⊥ := by
  let eK := K.equivMapOfInjective H.subtype H.subtype_injective
  let ec := coreCentralQuotientCongr eK
  have he : (coreCentralIntersectionImage K (R.subgroupOf H)).map ec.toMonoidHom =
      coreCentralIntersectionImage (K.map H.subtype) R := by
    ext x
    constructor
    · rintro ⟨y,⟨k,hk,rfl⟩,rfl⟩
      exact ⟨eK k,hk,(coreCentralQuotientCongr_apply eK k).symm⟩
    · rintro ⟨k,hk,rfl⟩
      refine ⟨coreCentralProjection K (eK.symm k),⟨eK.symm k,?_,rfl⟩,?_⟩
      · change ((eK.symm k : K) : H).val ∈ R
        have hh := congrArg (fun a : K.map H.subtype => (a : G)) (eK.apply_symm_apply k)
        change ((eK.symm k : K) : H).val = (k : G) at hh
        rwa [hh]
      · change coreCentralQuotientCongr eK (coreCentralProjection K (eK.symm k)) = _
        rw [coreCentralQuotientCongr_apply,eK.apply_symm_apply]
  intro hb
  apply hn
  rw [←he,hb,Subgroup.map_bot]

private theorem normalized_model_representation
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    {Q : Type*} [Group Q] (e : coreCentralQuotient K ≃* Q) :
    ∃ r : F →* Q, Group.IsSolvable r.ker ∧
      r.range ≤ normalizer ((coreCentralIntersectionImage K (R.subgroupOf H)).map
        e.toMonoidHom : Set Q) := by
  obtain ⟨r,hker,hr⟩ := constrained_normalized_inner_representation h hn K hK hq hout
  let := hker
  let q := e.toMonoidHom.comp r
  have hk : q.ker = r.ker := MonoidHom.ker_comp_of_injective r e.toMonoidHom e.injective
  refine ⟨q,hk.symm ▸ hker,?_⟩
  change (e.toMonoidHom.comp r).range ≤ _
  rw [MonoidHom.range_comp]
  exact (map_mono hr).trans ((coreCentralIntersectionImage K (R.subgroupOf H)).le_normalizer_map _)

/-- The original constrained symplectic row is incompatible with the marked simple quotient. -/
theorem no_constrained_normalized_symplectic
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : F →* S) (hπ : Function.Surjective π)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃*
      Theory.SpecificGroups.SymplecticFour.Sp E) (hE : 4 ≤ Nat.card E) : False := by
  let ec := h.constrained_symplectic_simple_equiv K hK hq hout hfK e
  have hnI := intrinsic_intersection_ne_bot K (source_symplectic_intersection_ne_bot
    (h.constrained_source_input K hK hq hout hfK) e hE)
  let I := coreCentralIntersectionImage K (R.subgroupOf H)
  let P := I.map ec.toMonoidHom
  have hp : IsPGroup 2 P := (coreCentralIntersectionImage_isPGroup K _ h.isRadical.isPGroup).map _
  have hpne : P ≠ ⊥ := fun hb => hnI ((I.map_eq_bot_iff_of_injective ec.injective).mp hb)
  obtain ⟨r,hker,hr⟩ := normalized_model_representation h hn K hK hq hout ec
  let := hker
  let : Group.IsPerfect F := (h.normalized_span_eq hn) ▸ h.span_perfect
  exact no_symplectic_four_local hS hexp π hπ P hp hpne r hr

/-- The same literal action excludes the constrained G₂ row. -/
theorem no_constrained_normalized_g2
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : F →* S) (hπ : Function.Surjective π)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* Atlas.G2.Model E)
    (hE : 4 ≤ Nat.card E) : False := by
  let ec := h.constrained_g2_simple_equiv K hK hq hout hfK e hE
  have hnI := intrinsic_intersection_ne_bot K (source_g2_intersection_ne_bot
    (h.constrained_source_input K hK hq hout hfK) e hE)
  let I := coreCentralIntersectionImage K (R.subgroupOf H)
  let P := I.map ec.toMonoidHom
  have hp : IsPGroup 2 P := (coreCentralIntersectionImage_isPGroup K _ h.isRadical.isPGroup).map _
  have hpne : P ≠ ⊥ := fun hb => hnI ((I.map_eq_bot_iff_of_injective ec.injective).mp hb)
  obtain ⟨r,hker,hr⟩ := normalized_model_representation h hn K hK hq hout ec
  let := hker
  let : Group.IsPerfect F := (h.normalized_span_eq hn) ▸ h.span_perfect
  exact no_g2_local hS hexp π hπ (by omega) P hp hpne r hr

/-- The large constrained SL₃ star row retains its exact projective action. -/
theorem no_constrained_normalized_linear_three
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hS : ¬ Group.IsSolvable S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : F →* S) (hπ : Function.Surjective π)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K)
    (E : ChapterB.QuasisimpleSource.BinaryField) (hE : 1 < E.degree)
    (e : starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(3,E.Carrier)) : False := by
  let ec := h.constrained_linear_three_simple_equiv K hK hq hout hfK e
  have hcard : 4 ≤ Nat.card E.Carrier := by
    rw [E.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ E.degree)
  have hnI := intrinsic_intersection_ne_bot K (source_linear_three_intersection_ne_bot
    (h.constrained_source_input K hK hq hout hfK) e hcard)
  let I := coreCentralIntersectionImage K (R.subgroupOf H)
  let P := I.map ec.toMonoidHom
  have hp : IsPGroup 2 P := (coreCentralIntersectionImage_isPGroup K _ h.isRadical.isPGroup).map _
  have hpne : P ≠ ⊥ := fun hb => hnI ((I.map_eq_bot_iff_of_injective ec.injective).mp hb)
  obtain ⟨r,hker,hr⟩ := normalized_model_representation h hn K hK hq hout ec
  let := hker
  let : Group.IsPerfect F := (h.normalized_span_eq hn) ▸ h.span_perfect
  exact no_linear_three_local hS hexp π hπ hE E.card_eq P hp hpne r hr

end CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl

end
