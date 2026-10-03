module

public import Stellmacher.SectionNine.NineFiveSupportSeedProducer
public import Stellmacher.SectionNine.NineFiveSupportProducer
public import Stellmacher.SectionNine.NineFiveSmallModel
public import Stellmacher.SectionNine.NineFiveLargeModel

/-!
# Stellmacher (9.5): the transvection support dichotomy

For a commuting critical pair of distance greater than one, an actor in the
first-step module with index-two terminal displacement has two possible
terminal modules: order eight with SL₂(2) core quotient, or order thirty-two
with regular wreath-product core quotient and an order-eight intersection
with the prescribed backward module.

The faithful terminal action on V/Z selects a canonical four-element
quotient support from (1.7). The penultimate-core conjugator spans V by
two lifted supports. Equal supports give order eight; distinct supports
intersect in the central line and give order thirty-two. In the latter
case the neighboring intersection is the inverse image of the common fixed
subgroup of two conjugate transvections, which has order four. Faithful
action and the canonical factor pair identify the two quotient models.
The ambient form retains Hypothesis Two on H and the graph on G; its
identity-embedding specialization preserves the legacy theorem.

Source: Stellmacher, Journal of Algebra 190 (1997), (9.5), printed pp.52–53.
The scan of p.52 states SL₂(2) ≀ C₂ in the second alternative; the former
direct-product transcription was incorrect. The direct product on p.56
belongs to a proper normalizer in (9.9), not this whole stabilizer quotient.
-/

open scoped BigOperators Pointwise

namespace Stellmacher.SectionNine

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

/-- The ambient-retaining transvection support dichotomy of (9.5). -/
public theorem lemma_nine_five_ambient
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (aMinus2 : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) aMinus2)
    (t : G)
    (ht : t ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      t ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers t⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a')
      (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hcontain : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers t⁆ ≤
      VAt ctx.Γ aMinus2) :
    (Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 3 ∧
        QuotientIsModel
          (GAt ctx.Γ ctx.criticalPath.a')
          (QAt ctx.Γ ctx.criticalPath.a') SL2Two) ∨
      (Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 5 ∧
        QuotientIsModel
          (GAt ctx.Γ ctx.criticalPath.a')
          (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2 ∧
        Nat.card
          (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ aMinus2 : Subgroup G) = 2 ^ 3) := by
  have htP : t ∈ GAt ctx.Γ ctx.criticalPath.a' :=
    (lemma_seven_four ctx.sectionSeven ctx.Γ ctx.criticalPath).first_containment.2 ht.1
  let actor : GAt ctx.Γ ctx.criticalPath.a' := ⟨t, htP⟩
  obtain ⟨hN, hW, action, hact, hkernel, hyp, factor, hfactor, seed, hseed⟩ :=
    nine_five_support_seed ctx hb aMinus2 hpath t ht hindex hcontain
  let _ := hN
  let _ := hW
  obtain ⟨data, hsupport⟩ := nine_five_support_data_of_seed_eq ctx hb
    aMinus2 hpath t ht hindex hcontain seed
  obtain ⟨mover, _, hmover⟩ := lemma_seven_five_endpoint_alignment ctx.sectionSeven
    ctx.Γ ctx.criticalPath ctx.commutator_eq
  have horbit : IsConjugateVertex ctx.Γ ctx.criticalPath.firstStep
      ctx.criticalPath.a' := ⟨mover, hmover⟩
  rcases nine_five_cardinalities_of_support ctx.toLocalContext hb aMinus2 t data with
    hsmall | ⟨hlarge, hintersection⟩
  · refine Or.inl ⟨hsmall, ?_⟩
    exact nine_five_small_model ctx hb _ horbit actor hindex (by simpa [AmbientSectionNineContext.toLocalContext] using hsmall)
  · refine Or.inr ⟨hlarge, ?_, hintersection⟩
    have hne := (nine_five_support_distinct_iff_card_thirty_two
      ctx.toLocalContext hb aMinus2 t data).mpr hlarge
    apply nine_five_large_model_of_canonical_support ctx hb aMinus2 t data
      hne hN hW action hact hkernel hyp factor hfactor
    rw [hsupport]
    exact hseed


/-- **Stellmacher (9.5).**  The two possibilities for `V_{a'}` when an
involution has the prescribed transvection-sized commutator. -/
public theorem lemma_nine_five
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2)
    (hb : 1 < ctx.criticalPath.length)
    (aMinus2 : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) aMinus2)
    (t : H)
    (ht : t ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      t ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers t⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a')
      (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hcontain : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers t⁆ ≤
      VAt ctx.Γ aMinus2) :
    (Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 3 ∧
        QuotientIsModel
          (GAt ctx.Γ ctx.criticalPath.a')
          (QAt ctx.Γ ctx.criticalPath.a') SL2Two) ∨
      (Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2 ^ 5 ∧
        QuotientIsModel
          (GAt ctx.Γ ctx.criticalPath.a')
          (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2 ∧
        Nat.card
          (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ aMinus2 : Subgroup H) = 2 ^ 3) := by
  exact lemma_nine_five_ambient ctx.toAmbientContext hb aMinus2 hpath t ht
    hindex hcontain

end Stellmacher.SectionNine
