module

public import Stellmacher.LaterDefs
public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven

/-!
# Ambient-retaining Section Nine contexts

Section Nine uses Hypothesis Two on H and the Section Seven graph on the
generated group G. The local record contains only genuine Section Seven
hypotheses and the commuting critical pair; it does not assert that these
alone imply the terminal results. The ambient record additionally retains
Hypothesis Two and an injective homomorphism identifying the local pair and
intersection with their actual subgroups in H.
Mapping the local generation equality proves that the embedding's range is
exactly P1 ⊔ P2, rather than requiring that this join be all of H.

The generated specialization uses the inclusion of P1 ⊔ P2. Its constructor
only needs explicitly supplied local data: subgroup restriction followed by
inclusion recovers the pair, and Hypothesis Two supplies S ≤ P1. The legacy
adapter uses the identity homomorphism. Both keep the exact graph and critical
path, without inheriting Hypothesis Two or transporting a graph to H.

For (9.1), a local subgroup U has ambient normalizer N_H(U.map embedding),
not N_G(U). A quotient model for the latter is not a quotient model for the
former. No numbered conclusion is a field of either context.

Source: Stellmacher, Hypothesis Two, Sections Seven and Nine openings,
(9.1)(c), and Section Eleven; refs/latex/stellmacher-n-group.tex.
This is the commuting analogue of SectionEight/GeneratedContext.lean;
neither local interface claims to cover the ambient uses in (8.3).
-/

namespace Stellmacher.Later

open SectionsFiveToSeven

universe u

public structure SectionNineLocalContext
    (G : Type u) [Group G] [Finite G] (T A B : Subgroup G) where
  sectionSeven : SectionSevenHypotheses G T A B
  Γ : CosetGraphContext G T A B
  criticalPath : CriticalPath Γ
  commutator_eq : ⁅Γ.z criticalPath.a, Γ.z criticalPath.a'⁆ = ⊥

public structure AmbientSectionNineContext
    (H : Type u) [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    {G : Type u} [Group G] [Finite G]
    (embedding : G →* H) (T A B : Subgroup G)
    extends SectionNineLocalContext G T A B where
  hypothesisTwo : HypothesisTwo H S0 S P1 P2
  embedding_injective : Function.Injective embedding
  map_S : T.map embedding = S
  map_P1 : A.map embedding = P1
  map_P2 : B.map embedding = P2

public abbrev GeneratedSectionNineContext
    (H : Type u) [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H) :=
  AmbientSectionNineContext H S0 S P1 P2 (P1 ⊔ P2).subtype
    (S.subgroupOf (P1 ⊔ P2)) (P1.subgroupOf (P1 ⊔ P2)) (P2.subgroupOf (P1 ⊔ P2))

@[expose] public def AmbientSectionNineContext.toLocalContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) :
    SectionNineLocalContext G T A B := ctx.toSectionNineLocalContext

public theorem AmbientSectionNineContext.range_eq_join
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) :
    embedding.range = P1 ⊔ P2 := by
  rw [MonoidHom.range_eq_map, ← ctx.sectionSeven.generated, Subgroup.map_sup,
    ctx.map_P1, ctx.map_P2]

@[expose] public def SectionNineContext.toLocalContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2) : SectionNineLocalContext H S P1 P2 where
  sectionSeven := ctx.hypothesisTwo.sectionSevenHypotheses ctx.generated
  Γ := ctx.Γ
  criticalPath := ctx.criticalPath
  commutator_eq := ctx.commutator_eq

@[expose] public def SectionNineContext.toAmbientContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2) :
    AmbientSectionNineContext H S0 S P1 P2 (MonoidHom.id H) S P1 P2 where
  toSectionNineLocalContext := ctx.toLocalContext
  hypothesisTwo := ctx.hypothesisTwo
  embedding_injective := Function.injective_id
  map_S := Subgroup.map_id S
  map_P1 := Subgroup.map_id P1
  map_P2 := Subgroup.map_id P2

@[expose] public def GeneratedSectionNineContext.ofLocalContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (hypothesisTwo : HypothesisTwo H S0 S P1 P2)
    (localContext : SectionNineLocalContext (P1 ⊔ P2 : Subgroup H)
      (S.subgroupOf (P1 ⊔ P2)) (P1.subgroupOf (P1 ⊔ P2)) (P2.subgroupOf (P1 ⊔ P2))) :
    GeneratedSectionNineContext H S0 S P1 P2 where
  toSectionNineLocalContext := localContext
  hypothesisTwo := hypothesisTwo
  embedding_injective := (P1 ⊔ P2).subtype_injective
  map_S := Subgroup.map_subgroupOf_eq_of_le
    (hypothesisTwo.fiveOne.P1_mem.1.2.1.1.trans le_sup_left)
  map_P1 := Subgroup.map_subgroupOf_eq_of_le le_sup_left
  map_P2 := Subgroup.map_subgroupOf_eq_of_le le_sup_right

public theorem GeneratedSectionNineContext.ofLocalContext_toLocalContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (hypothesisTwo : HypothesisTwo H S0 S P1 P2)
    (localContext : SectionNineLocalContext (P1 ⊔ P2 : Subgroup H)
      (S.subgroupOf (P1 ⊔ P2)) (P1.subgroupOf (P1 ⊔ P2)) (P2.subgroupOf (P1 ⊔ P2))) :
    (GeneratedSectionNineContext.ofLocalContext hypothesisTwo localContext).toLocalContext =
      localContext := rfl

public theorem SectionNineContext.toAmbientContext_toLocalContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionNineContext H S0 S P1 P2) :
    ctx.toAmbientContext.toLocalContext = ctx.toLocalContext := rfl

end Stellmacher.Later
