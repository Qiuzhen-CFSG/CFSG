module

public import Stellmacher.SectionTen.GeneratedContext
public import Stellmacher.ExceptionalType

/-!
# Exact ambient conclusion interface for Stellmacher (10.1)

The conclusion record retains every common equation and both alternatives
from the scan. The group orders and local structures live in the graph group.
The involution obstruction lives in the original ambient group; the injective
centralizer map also transports a locally established obstruction there.

The projection supplies every field of `TenOneCaseBTypeData`, including the
critical-path length and offset. The completed theorem in `AmbientTenOne`
provides the conclusion used by the actual generated-context consumer.
This interface sits below that theorem and its identity-embedding wrapper
in `LemmaTenOne`.

Source: `refs/files/stellmacher-n-group.pdf`, printed pp. 59--65 / PDF pp. 49--55.
In particular, the displayed derived subgroup on printed p. 59 is
`DerivedAmbient Wnext`, not `Wnext` itself.
-/

open scoped BigOperators Pointwise

namespace Stellmacher.SectionTen

open Later SectionsFiveToSeven

universe u

public theorem nonsolvable_centralizer_map
    {G H : Type u} [Group G] [Group H]
    (embedding : G →* H) (hinjective : Function.Injective embedding) (point : G)
    (hnonsolvable : ¬ Group.IsSolvable (Subgroup.centralizer ({point} : Set G))) :
    ¬ Group.IsSolvable (Subgroup.centralizer ({embedding point} : Set H)) := by
  intro hsolvable
  let centralizerMap : Subgroup.centralizer ({point} : Set G) →*
      Subgroup.centralizer ({embedding point} : Set H) :=
    (embedding.comp (Subgroup.centralizer ({point} : Set G)).subtype).codRestrict
      (Subgroup.centralizer ({embedding point} : Set H)) (by
        intro element
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        simpa only [map_mul, MonoidHom.comp_apply, Subgroup.subtype_apply] using congrArg embedding
          (Subgroup.mem_centralizer_singleton_iff.mp element.property))
  have hinjectiveMap : Function.Injective centralizerMap := by
    intro left right hequal
    apply Subtype.ext
    exact hinjective (congrArg Subtype.val hequal)
  exact hnonsolvable (Group.isSolvable_of_isSolvable_injective hinjectiveMap)

public inductive AmbientLemmaTenOneAlternative
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (next : ctx.Γ.Vertex) (W W0 Wnext : Subgroup G) : Prop
  | a
      (_ : 2 ^ 6 ≤ Nat.card T ∧ Nat.card T ≤ 2 ^ 7)
      (_ : QuotientIsModel
        (GAt ctx.Γ ctx.criticalPath.firstStep)
        (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two ∧
        QuotientIsModel (GAt ctx.Γ next) (QAt ctx.Γ next) SL2Two)
      (_ : ZAt ctx.Γ next = W ∧
        IsModel (twoCoreIn (EAt ctx.Γ next)) (C4 × C4))
      (_ : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2 ^ 3 ∧
        IsExtraspecial 2 (↥(twoCoreIn
          (EAt ctx.Γ ctx.criticalPath.firstStep))) ∧
        Nat.card (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)) = 2 ^ 5)
      (_ : ∃ point : G,
        Later.IsInvolution point ∧ point ∈ QAt ctx.Γ next ∧ point ∉ ZAt ctx.Γ next ∧
        ¬ Group.IsSolvable (Subgroup.centralizer ({embedding point} : Set H)))
  | b
      (_ : 2 ^ 11 ≤ Nat.card T ∧ Nat.card T ≤ 2 ^ 12)
      (_ : QuotientIsModel (GAt ctx.Γ next) (QAt ctx.Γ next) SL2Two ∧
        QuotientIsFrobenius20
          (GAt ctx.Γ ctx.criticalPath.firstStep)
          (QAt ctx.Γ ctx.criticalPath.firstStep))
      (_ : QuotientCardEq
          (VAt ctx.Γ ctx.criticalPath.firstStep)
          (ZAt ctx.Γ ctx.criticalPath.firstStep) (2 ^ 4) ∧
        QuotientCardEq
          (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep))
          (VAt ctx.Γ ctx.criticalPath.firstStep) (2 ^ 4) ∧
        DerivedAmbient (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep)) =
          VAt ctx.Γ ctx.criticalPath.firstStep)
      (_ : Nat.card (ZAt ctx.Γ next) = 4 ∧
        QuotientCardEq W (DerivedAmbient Wnext) 4 ∧
        QuotientCardEq Wnext W0 4 ∧
        QuotientCardEq (twoCoreIn (EAt ctx.Γ next) ⊔ Wnext) Wnext 4 ∧
        QuotientCardEq (DerivedAmbient Wnext) (ZAt ctx.Γ next) 2)

public structure AmbientLemmaTenOneConclusion
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (next : ctx.Γ.Vertex) (W W0 Wnext : Subgroup G) : Prop where
  definitions :
    W = conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ next) ∧
    Wnext = GeneratedNeighborhoodV ctx.Γ next ∧
    W0 = NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ next) ⊓ Wnext
  index_conclusions : QuotientCardEq W0 W 2 ∧ QuotientCardEq Wnext W (2 ^ 3)
  derived_intersection :
    DerivedAmbient Wnext = VAt ctx.Γ ctx.criticalPath.firstStep ⊓
      VAt ctx.Γ ctx.criticalPath.a'
  alternative : AmbientLemmaTenOneAlternative ctx next W W0 Wnext

public theorem ambient_ten_one_case_b_or_nonsolvable_centralizer_of_conclusion
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (next : ctx.Γ.Vertex) (W W0 Wnext : Subgroup G)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 next)
    (hconclusion : AmbientLemmaTenOneConclusion ctx next W W0 Wnext) :
    (∃ next : ctx.Γ.Vertex, ∃ W W0 Wnext : Subgroup G,
      TenOneCaseBTypeData ctx.Γ ctx.criticalPath next W W0 Wnext) ∨
    (∃ point : G, Later.IsInvolution point ∧
      ¬ Group.IsSolvable (Subgroup.centralizer ({embedding point} : Set H))) := by
  cases hconclusion.alternative with
  | a _ _ _ _ hobstruction =>
    obtain ⟨point, hinvolution, _, _, hnonsolvable⟩ := hobstruction
    exact Or.inr ⟨point, hinvolution, hnonsolvable⟩
  | b hcard hquotients hstructure hindices =>
    exact Or.inl ⟨next, W, W0, Wnext, {
      critical_length := ctx.critical_length
      path_offset := hpath
      definitions := hconclusion.definitions
      derived_intersection := hconclusion.derived_intersection
      index_conclusions := hconclusion.index_conclusions
      card_S := hcard
      local_quotients := hquotients
      first_step_structure := hstructure
      remaining_indices := hindices }⟩

end Stellmacher.SectionTen
