module
public import Stellmacher.SectionEight.EightSixInitialThreeSupplement
/-!
# The actual initial three-Sylow has order three

The initial stabilizer in the local configuration of Stellmacher (8.6)
has quotient SL₂(2) by its two-core. Consequently every supplied Sylow
three-subgroup has order three. This branch-independent statement supplies
the cubic generator used in the cost-four normalizer construction.

Projection is injective on the three-Sylow because its kernel is a two-group.
The image is a Sylow three-subgroup of the quotient of order six, so the
Sylow cardinal formula gives order three. Cardinality transports first
through the restricted quotient map and then to the actual ambient subgroup.
Source: the initial quotient in Stellmacher (8.6), printed pp.41–44.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_initial_three_card
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (T : Subgroup G) (hT : IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a)) :
    Nat.card T = 3 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let P := GAt ctx.Γ ctx.criticalPath.a
  obtain ⟨f,hf,hker⟩ := hquot
  obtain ⟨sylow,hsylow⟩ := hT
  have hkerTwo : IsPGroup 2 f.ker := by
    rw [hker]
    change IsPGroup 2 ((ctx.Γ.twoCoreAt ctx.criticalPath.a).subgroupOf P)
    rw [ctx.Γ.twoCoreAt_def]
    have hh : (twoCoreIn P).subgroupOf P = pCore 2 P :=
      Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
    change IsPGroup 2 ((twoCoreIn P).subgroupOf P)
    rw [hh]
    exact pCore_isPGroup
  have hdis : Disjoint (sylow : Subgroup P) f.ker :=
    sylow.isPGroup'.disjoint_of_coprime hkerTwo (by decide)
  let restricted := f.comp (sylow : Subgroup P).subtype
  have hinj : Function.Injective restricted := by
    rw [←MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro a ha
    exact Subtype.ext (hdis.le_bot ⟨a.property,ha⟩)
  have himage : restricted.range = (sylow : Subgroup P).map f := by
    rw [MonoidHom.range_comp,Subgroup.range_subtype]
  have hmodelCard : Nat.card SL2Two = 6 :=
    SectionOne.RankOneThreeGroupAssembly.isSL2Two_card ⟨MulEquiv.refl _⟩
  have himageCard : Nat.card ((sylow : Subgroup P).map f) = 3 := by
    have hh := (sylow.mapSurjective hf).card_eq_multiplicity
    change Nat.card ((sylow : Subgroup P).map f) = _ at hh
    rw [hmodelCard] at hh
    have hfac : (6 : ℕ).factorization 3 = 1 := by
      change Nat.factorization (2 * 3) 3 = 1
      rw [Nat.factorization_mul (by decide) (by decide)]
      norm_num [Nat.prime_two.factorization,Nat.prime_three.factorization]
    rw [hfac,pow_one] at hh
    exact hh
  have hsylowCard : Nat.card sylow = 3 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,himage]
    exact himageCard
  rw [←hsylow,Subgroup.card_map_of_injective P.subtype_injective]
  exact hsylowCard
end Stellmacher.SectionEight
