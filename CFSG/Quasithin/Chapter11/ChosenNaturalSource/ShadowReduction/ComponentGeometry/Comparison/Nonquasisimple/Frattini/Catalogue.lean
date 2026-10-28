module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Catalogue.Models
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Catalogue.Nilpotent
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Nonquasisimple.Frattini.Kernel
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank

/-!
# The complete nonquasisimple catalogue reduction on the chosen flag

The actual point component is SQTK inside its two-local point centralizer.
The noncentral-Fitting theorem bounds its two-core quotient's two-rank by
one. Applying every row of the complete 11.1.1 catalogue leaves two extension
models. The nilpotent SL₂(5) row makes the nontrivial perfect flag seed
supplement the literal Fitting preimage and contradicts movement of V₁.

The surviving elementary-plane extension forces field degree two and gives
the original SL₂(p) two-Fitting quotient. The existing radical, Frattini and
kernel proofs then supply R₁'s Sylow placement in O∞(KzR₁), the Fitting
factorization, and the inclusion-induced PSL₂(p) residual quotient. Its
representative equation preserves the literal original maps.

The earlier complete catalogue is supplied by qt-natural1111-embedding-models.
Fitting centralization and the residual-overcomponent Cartan argument remain
with qt-d-1222-comparison-nonquasisimple, which retains final assembly. This
module does not assert the complete source theorem.
Source: Aschbacher--Smith, 11.1.1 and 11.4.2, printed pp.761 and 777.
-/

set_option backward.isDefEq.respectTransparency false

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
open Chapter1.Section02.LocalModels LocalGeometry.Components
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {E : Closure.Geometry D}

/-- The actual point component's nonquasisimple two-core quotient has two-rank at most one. -/
theorem point_quotient_two_rank_le_one
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : EarlierGeometry E)
    (hn : ¬ IsQuasisimple (E.Kz ⧸ pCore 2 E.Kz)) :
    primeRank 2 (E.Kz ⧸ pCore 2 E.Kz) ≤ 1 := by
  let Q := E.Kz ⧸ pCore 2 E.Kz
  have hlocal := hG.twoLocal_sqtk
    (point_twoLocal E h.point_mem h.point_fixed h.point_ne_one)
  have hs : IsSQTK KnownSimple.IsKnownSimple E.Kz :=
    (IsSQTK.equiv (subgroupOfEquivOfLe h.point_component.1)).mp
      (hlocal.subgroup (E.Kz.subgroupOf (Gz E)))
  have hQ : IsSQTK KnownSimple.IsKnownSimple Q := by
    refine ⟨?_, hs.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hs.stronglyQuasithin p hp ho)
  have htop : (⊤ : Subgroup E.Kz).IsCComponent := by
    simpa only [subgroupOf_self] using
      h.point_component.2.subgroupOf_of_le le_rfl h.point_component.1
  let : Group.IsNilpotent (pCore 2 E.Kz) := pCore_isNilpotent
  have hbar : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      htop.map_quotient (pCore 2 E.Kz)
  by_contra! hr
  change 1 < primeRank 2 Q at hr
  have hr' : 2 ≤ primeRank 2 (⊤ : Subgroup Q) := by
    rw [primeRank_equiv 2 (topEquiv (G := Q))]
    omega
  let := ChapterA.Section03.NoncentralFitting.quasisimple_of_two_le_two_rank
    hQ (pCore_quotient_pCore_eq_bot 2) hbar hr'
  exact hn (IsQuasisimple.of_mulEquiv topEquiv)

/-- All rows of the complete 11.1.1 catalogue reduce to its exceptional elementary
extension, with the original field degree and literal two-Fitting quotient. -/
theorem ofFlag_exceptional_extension_of_catalogue (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hF : fittingPreimage (ofFlag S f X z H) ≤ centralizer ((ofFlag S f X z H).V₁ : Set G))
    (hc : LocalGeometry.Components.ComponentAlternative (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz S.field.degree) :
    S.field.degree = 2 ∧ ∃ p, Source.ExceptionalPrime p ∧
      HasExtension ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)
        (ElementaryModel p 2) (fun Q _ => Source.IsSL Q 2 p) ∧
      Source.IsSL ((ofFlag S f X z H).Kz ⧸ twoFittingCore (ofFlag S f X z H).Kz) 2 p := by
  let E := ofFlag S f X z H
  have hr := point_quotient_two_rank_le_one S.source.simpleQTKE h hn
  let : Group.IsPerfect E.Kz := Radical.relative_component_perfect h.point_component
  cases hc with
  | equal he => exact ((h.strict_comparison hf hne).2.1.ne he).elim
  | lie hm => exact (hn (Catalogue.lie_quasisimple_of_rank_le_one S.field.degree_pos hr hm)).elim
  | four hd hm =>
    rcases Catalogue.fieldFour_extensions hr hn hm with hnil | ⟨p, hp, he⟩
    · exact (ofFlag_not_nilpotent_extension S f X z H h hA hf hne hF hnil).elim
    · have hp3 : 3 < p := by have := hp.1.two_le; have := hp.2.1; omega
      let : Fact p.Prime := ⟨hp.1⟩
      exact ⟨hd, p, hp, he, twoFitting_sl2_of_elementary_extension hp3 he⟩

/-- The actual Frattini product and inclusion-induced residual quotient now follow
from the complete catalogue, without an extra model or kernel premise. -/
theorem ofFlag_frattini_of_catalogue (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H)) (hA : f.Li 0 ≠ ⊥)
    (hseed : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hf : V ⊓ centralizer (L : Set G) = ⊥)
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hn : ¬ IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hF : fittingPreimage (ofFlag S f X z H) ≤ centralizer ((ofFlag S f X z H).V₁ : Set G))
    (hc : LocalGeometry.Components.ComponentAlternative (ofFlag S f X z H).L₁ (ofFlag S f X z H).Kz S.field.degree) :
    (ofFlag S f X z H).Kz = fittingPreimage (ofFlag S f X z H) ⊔ normalizerResidual (ofFlag S f X z H) ∧
    S.field.degree = 2 ∧
    (ofFlag S f X z H).R₁ ≤
      (solvableRadical (pointRadicalJoin (ofFlag S f X z H))).map
        (pointRadicalJoin (ofFlag S f X z H)).subtype ∧
    Chapter1.IsSylowIn 2 (ofFlag S f X z H).R₁
      ((solvableRadical (pointRadicalJoin (ofFlag S f X z H))).map
        (pointRadicalJoin (ofFlag S f X z H)).subtype) ∧
    ∃ p, Source.ExceptionalPrime p ∧
      ClassicalGroup.IsPSL (normalizerResidual (ofFlag S f X z H) ⧸
        pCore 2 (normalizerResidual (ofFlag S f X z H))) 2 p ∧
      ∃ e : (normalizerResidual (ofFlag S f X z H) ⧸ pCore 2 (normalizerResidual (ofFlag S f X z H))) ≃*
          ((ofFlag S f X z H).Kz ⧸ solvableRadical (ofFlag S f X z H).Kz),
        ∀ x : normalizerResidual (ofFlag S f X z H),
          e (QuotientGroup.mk' (pCore 2 (normalizerResidual (ofFlag S f X z H))) x) =
            residualProjection (ofFlag S f X z H) x := by
  obtain ⟨hd, p, hp, he, hm⟩ :=
    ofFlag_exceptional_extension_of_catalogue S f X z H h hA hf hne hn hF hc
  let : Fact p.Prime := ⟨hp.1⟩
  have hp3 : 3 < p := by have := hp.1.two_le; have := hp.2.1; omega
  have hmodel := radical_model_of_fitting_sl2 hp3 hm
  exact ⟨ofFlag_fitting_factorization_of_extension S f X z H h hA hseed hp he,
    hd, ofFlag_le_join_radical_of_prime_model S f X z H h hA hp3 hmodel,
    ofFlag_sylow_in_join_radical_of_prime_model S f X z H h hA hseed hp3 hmodel,
    p, hp, ofFlag_residual_psl_of_extension S f X z H h hA hseed hp hn he,
    ofFlag_residualQuotientEquiv S f X z H h hA hseed hp hn he,
    ofFlag_residualQuotientEquiv_mk S f X z H h hA hseed hp hn he⟩
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Frattini
