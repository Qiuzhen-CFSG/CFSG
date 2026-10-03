module

public import Stellmacher.SectionNine.GeneratedContext
public import Theory.GroupTheory.ElementaryEightNormalizerRecognition

/-!
# The proof obligations and final assembly for (9.1)

These predicates separate the reductions in Stellmacher (9.1), Journal of
Algebra 190 (1997), pp. 46–48. They are conclusions to prove, not extra fields
of a graph or ambient hypothesis. The faithful action calculation in relation
(8) concerns the quotient by the centralizer of the starting center. The later
core calculation proves the two local quotients, the Sylow order, the equality
of the starting core and center, and the quaternion central product.

The final witness obligation remains in the original ambient group: construct
a self-centralizing elementary subgroup of order eight in the image of Vstar,
and two distinct S4 subgroups of its ambient normalizer quotient. The proved
elementary-eight recognition theorem identifies that quotient with PSL3(2).
The assembly theorem composes its equivalence with the canonical quotient
map and transfers the Sylow order along the injective graph-group embedding.
It does not prove any of the preceding local-structure or witness obligations.
-/

namespace Stellmacher.SectionNine

open Stellmacher.Later Stellmacher.SectionsFiveToSeven

universe u

@[expose] public def DistanceOneFaithfulConclusion
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) : Prop :=
  Nat.card (ZAt ctx.Γ ctx.criticalPath.a) = 2 ^ 4 ∧
    QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G))
      SL2TwoWreathC2

@[expose] public def DistanceOneLocalConclusion
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) : Prop :=
  let Vstar := conjugateClosure
    (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ ctx.criticalPath.a')
  QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2TwoWreathC2 ∧
    QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2Two ∧
    Nat.card T = 2 ^ 7 ∧
    QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ ctx.criticalPath.a ∧
    IsCentralProductQ8Q8 Vstar

@[expose] public def DistanceOneNormalizerInput
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {T A B : Subgroup G} (embedding : G →* H)
    (ctx : SectionNineLocalContext G T A B) : Prop :=
  let Vstar := conjugateClosure
    (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
    (GAt ctx.Γ ctx.criticalPath.a')
  ∃ U : Subgroup H,
    U ≤ Vstar.map embedding ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 8 ∧
      Subgroup.centralizer (U : Set H) = U ∧
      ∃ X Y : Subgroup
          ((Subgroup.normalizer (U : Set H)) ⧸
            U.subgroupOf (Subgroup.normalizer (U : Set H))),
        X ≠ Y ∧ Nonempty (X ≃* Equiv.Perm (Fin 4)) ∧
          Nonempty (Y ≃* Equiv.Perm (Fin 4))

public theorem distance_one_conclusion_of_data
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hlocal : DistanceOneLocalConclusion ctx.toLocalContext)
    (hwitness : DistanceOneNormalizerInput embedding ctx.toLocalContext) :
    let Vstar := conjugateClosure
      (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ ctx.criticalPath.a')
    QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
        (QAt ctx.Γ ctx.criticalPath.a) SL2TwoWreathC2 ∧
      QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
        (QAt ctx.Γ ctx.criticalPath.a') SL2Two ∧
      Nat.card S = 2 ^ 7 ∧
      QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ ctx.criticalPath.a ∧
      IsCentralProductQ8Q8 Vstar ∧
      ∃ U : Subgroup H,
        U ≤ Vstar.map embedding ∧ Nat.card U = 2 ^ 3 ∧
          QuotientIsModel (Subgroup.normalizer (U : Set H)) U L3Two := by
  obtain ⟨hfirst, hsecond, hcard, hcore, hproduct⟩ := hlocal
  obtain ⟨U, hUle, helementary, hUcard, hcentral, X, Y, hne, hX, hY⟩ := hwitness
  let _ : IsElementaryAbelian 2 U := helementary
  obtain ⟨equiv⟩ :=
    elementaryEight_normalizer_quotient_equiv_PSL3 U hUcard hcentral X Y hne hX hY
  have hScard : Nat.card S = 2 ^ 7 := by
    rw [← ctx.map_S, Subgroup.card_map_of_injective ctx.embedding_injective]
    exact hcard
  refine ⟨hfirst, hsecond, hScard, hcore, hproduct, U, hUle, hUcard, ?_⟩
  let projection := QuotientGroup.mk' (U.subgroupOf (Subgroup.normalizer (U : Set H)))
  refine ⟨equiv.toMonoidHom.comp projection,
    equiv.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  rw [MonoidHom.ker_comp_of_injective projection equiv.toMonoidHom equiv.injective,
    QuotientGroup.ker_mk']

end Stellmacher.SectionNine
