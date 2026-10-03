module

public import Stellmacher.SectionNine.GeneratedContext

/-!
# Ambient-retaining Section Ten contexts

Section Ten is the critical-distance-three specialization of Section Nine.
The local and ambient records extend the corresponding commuting contexts;
their adapters preserve the actual graph and path. The generated constructor
uses the Section Nine inclusion constructor, so Hypothesis Two remains on H
while Section Seven holds on P1 ⊔ P2. No Sylow subgroup of the join or
hereditary global hypothesis is needed. The legacy adapter uses the identity
embedding and keeps all old context and theorem declarations unchanged.

The ambient embedding is essential when consuming (10.1)(a): the source's
involution x belongs to Q_{a+2} minus Z_{a+2} and has nonsolvable C_G(x).
Nonsolvability passes to C_H(embedding x) by the injective centralizer map,
not by identifying the two centralizers. The W-subgroups, derived-intersection
equality, and all quotient orientations in (10.1) remain in the graph group.
These contexts contain none of the conclusions of the opening lemmas or (10.1).

Source: Stellmacher, Sections Nine and Ten openings and (10.1), printed
pp. 59--65; refs/files/stellmacher-n-group.pdf and its LaTeX transcription.
-/

namespace Stellmacher.Later

open SectionsFiveToSeven

universe u

public structure SectionTenLocalContext
    (G : Type u) [Group G] [Finite G] (T A B : Subgroup G)
    extends SectionNineLocalContext G T A B where
  critical_length : criticalPath.length = 3

public structure AmbientSectionTenContext
    (H : Type u) [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    {G : Type u} [Group G] [Finite G]
    (embedding : G →* H) (T A B : Subgroup G)
    extends AmbientSectionNineContext H S0 S P1 P2 embedding T A B where
  critical_length : criticalPath.length = 3

public abbrev GeneratedSectionTenContext
    (H : Type u) [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H) :=
  AmbientSectionTenContext H S0 S P1 P2 (P1 ⊔ P2).subtype
    (S.subgroupOf (P1 ⊔ P2)) (P1.subgroupOf (P1 ⊔ P2)) (P2.subgroupOf (P1 ⊔ P2))

@[expose] public def AmbientSectionTenContext.toLocalContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B) :
    SectionTenLocalContext G T A B where
  toSectionNineLocalContext := ctx.toAmbientSectionNineContext.toLocalContext
  critical_length := ctx.critical_length

@[expose] public def SectionTenContext.toNineContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionTenContext H S0 S P1 P2) : SectionNineContext H S0 S P1 P2 where
  hypothesisTwo := ctx.hypothesisTwo
  generated := ctx.generated
  Γ := ctx.Γ
  criticalPath := ctx.criticalPath
  commutator_eq := ctx.commutator_eq

@[expose] public def SectionTenContext.toLocalContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionTenContext H S0 S P1 P2) : SectionTenLocalContext H S P1 P2 where
  toSectionNineLocalContext := ctx.toNineContext.toLocalContext
  critical_length := ctx.critical_length

@[expose] public def SectionTenContext.toAmbientContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionTenContext H S0 S P1 P2) :
    AmbientSectionTenContext H S0 S P1 P2 (MonoidHom.id H) S P1 P2 where
  toAmbientSectionNineContext := ctx.toNineContext.toAmbientContext
  critical_length := ctx.critical_length

@[expose] public def AmbientSectionNineContext.toTenContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (critical_length : ctx.criticalPath.length = 3) :
    AmbientSectionTenContext H S0 S P1 P2 embedding T A B where
  toAmbientSectionNineContext := ctx
  critical_length := critical_length

@[expose] public def GeneratedSectionTenContext.ofLocalContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (hypothesisTwo : HypothesisTwo H S0 S P1 P2)
    (localContext : SectionTenLocalContext (P1 ⊔ P2 : Subgroup H)
      (S.subgroupOf (P1 ⊔ P2)) (P1.subgroupOf (P1 ⊔ P2)) (P2.subgroupOf (P1 ⊔ P2))) :
    GeneratedSectionTenContext H S0 S P1 P2 :=
  (GeneratedSectionNineContext.ofLocalContext hypothesisTwo
    localContext.toSectionNineLocalContext).toTenContext localContext.critical_length

public theorem GeneratedSectionTenContext.ofLocalContext_toLocalContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (hypothesisTwo : HypothesisTwo H S0 S P1 P2)
    (localContext : SectionTenLocalContext (P1 ⊔ P2 : Subgroup H)
      (S.subgroupOf (P1 ⊔ P2)) (P1.subgroupOf (P1 ⊔ P2)) (P2.subgroupOf (P1 ⊔ P2))) :
    (GeneratedSectionTenContext.ofLocalContext hypothesisTwo localContext).toLocalContext =
      localContext := rfl

public theorem SectionTenContext.toAmbientContext_toLocalContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionTenContext H S0 S P1 P2) :
    ctx.toAmbientContext.toLocalContext = ctx.toLocalContext := rfl

public theorem AmbientSectionNineContext.toTenContext_toNineContext
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (critical_length : ctx.criticalPath.length = 3) :
    (ctx.toTenContext critical_length).toAmbientSectionNineContext = ctx := rfl

end Stellmacher.Later
