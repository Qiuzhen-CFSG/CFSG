module

public import Stellmacher.SectionNine.NineFiveSpanAlgebra
public import Stellmacher.SectionNine.NineFiveSupportSeed
public import Stellmacher.SectionNine.NineFivePenultimateConjugator
public import Stellmacher.SectionNine.LemmaNineThree

/-!
# Assembly of the two-conjugate support data in (9.5)

A selected four-element quotient support with the intersection controls
supplies the complete two-conjugate support data. The ambient wrapper
obtains the initial center order from (9.3), constructs the penultimate
residual-core conjugator from the original transvection hypotheses, and
uses residual generation to prove that the two supports span the terminal
module. The lower-level assembly retains an explicit conjugator for callers
that already have one. Companion existence theorems retain equality of the
assembled support with the selected seed, so quotient-factor recognition can
reuse the same support image.

Support selection remains an explicit input: these theorems do not assert
its existence. Source: Stellmacher (9.5), printed pp.52–53 of
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven

universe u

/-- Assemble data while retaining the selected support and conjugator. -/
public theorem nine_five_support_data_of_seed_and_conjugator_eq
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (prev : ctx.Γ.Vertex) (actor : G)
    (seed : NineFiveSupportSeed ctx prev actor)
    (conjugator : G)
    (hconjugator : conjugator ∈ twoCoreIn (EAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)))
    (hcenter : ZAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤
      (ZAt ctx.Γ ctx.criticalPath.a' ⊔
        ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆) ⊔
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆).map
          (MulAut.conj conjugator⁻¹).toMonoidHom) :
    ∃ data : NineFiveSupportData ctx prev actor,
      data.support = seed.support ∧ data.conjugator = conjugator := by
  have hcenter_support := hcenter.trans
    (sup_le (sup_le (seed.center_le.trans le_sup_left)
      (seed.commutator_le.trans le_sup_left))
      ((Subgroup.map_mono seed.commutator_le).trans le_sup_right))
  have hspan := nine_five_two_support_span_of_neighbor_center ctx _ _
    (nine_five_penultimate_adjacent ctx) seed.support conjugator
    seed.support_le seed.residual_normalizes
    (nine_five_penultimate_core_le_terminal ctx hconjugator) hcenter_support
  exact ⟨{
    support := seed.support
    conjugator := conjugator
    center_card := seed.center_card
    center_le := seed.center_le
    support_index := seed.support_index
    commutator_le := seed.commutator_le
    residual_normalizes := seed.residual_normalizes
    conjugator_mem := hconjugator
    span := hspan
    support_intersection := seed.support_intersection conjugator hconjugator
    neighbor_intersection := seed.neighbor_intersection conjugator hconjugator hspan
  }, rfl, rfl⟩

public theorem nine_five_support_data_of_seed_and_conjugator
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (prev : ctx.Γ.Vertex) (actor : G)
    (seed : NineFiveSupportSeed ctx prev actor)
    (conjugator : G)
    (hconjugator : conjugator ∈ twoCoreIn (EAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)))
    (hcenter : ZAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤
      (ZAt ctx.Γ ctx.criticalPath.a' ⊔
        ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆) ⊔
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆).map
          (MulAut.conj conjugator⁻¹).toMonoidHom) :
    Nonempty (NineFiveSupportData ctx prev actor) := by
  obtain ⟨data, _, _⟩ := nine_five_support_data_of_seed_and_conjugator_eq
    ctx prev actor seed conjugator hconjugator hcenter
  exact ⟨data⟩

/-- The ambient assembly retains the selected support exactly. -/
public theorem nine_five_support_data_of_seed_eq
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (prev : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) prev)
    (actor : G)
    (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hcontain : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤
      VAt ctx.Γ prev)
    (seed : NineFiveSupportSeed ctx.toLocalContext prev actor) :
    ∃ data : NineFiveSupportData ctx.toLocalContext prev actor,
      data.support = seed.support := by
  have hfour := (lemma_nine_three_ambient ctx hb ctx.criticalPath.a
    ⟨1, ctx.Γ.act_one _⟩).2
  obtain ⟨conjugator, hconjugator, hcenter⟩ :=
    nine_five_penultimate_conjugator_of_initial_four
      ctx hfour hb prev hpath actor hactor hindex hcontain
  obtain ⟨data, hsupport, _⟩ := nine_five_support_data_of_seed_and_conjugator_eq
    ctx.toLocalContext prev actor seed conjugator hconjugator hcenter
  exact ⟨data, hsupport⟩

/-- A selected support supplies the two-conjugate data under the original ambient hypotheses. -/
public theorem nine_five_support_data_of_seed
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length) (prev : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath
      (ctx.criticalPath.length - 2) prev)
    (actor : G)
    (hactor : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep ∧
      actor ∉ QAt ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
        ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2)
    (hcontain : ⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ≤
      VAt ctx.Γ prev)
    (seed : NineFiveSupportSeed ctx.toLocalContext prev actor) :
    Nonempty (NineFiveSupportData ctx.toLocalContext prev actor) := by
  obtain ⟨data, _⟩ := nine_five_support_data_of_seed_eq
    ctx hb prev hpath actor hactor hindex hcontain seed
  exact ⟨data⟩

end Stellmacher.SectionNine
