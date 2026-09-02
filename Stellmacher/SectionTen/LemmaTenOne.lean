module

public import Stellmacher.LaterDefs

open scoped BigOperators Pointwise

namespace Stellmacher.SectionTen

open Stellmacher.Later
open Stellmacher.SectionsFiveToSeven

universe u

public inductive LemmaTenOneAlternative
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionTenContext H S0 S P1 P2)
    (aPlus2 : ctx.Γ.Vertex) (W W0 Wnext : Subgroup H) : Prop
  | a
      (_ : 2 ^ 6 ≤ Nat.card S ∧ Nat.card S ≤ 2 ^ 7)
      (_ : QuotientIsModel
        (GAt ctx.Γ ctx.criticalPath.firstStep)
        (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two ∧
        QuotientIsModel (GAt ctx.Γ aPlus2) (QAt ctx.Γ aPlus2) SL2Two)
      (_ : ZAt ctx.Γ aPlus2 = W ∧
        IsModel (twoCoreIn (EAt ctx.Γ aPlus2)) (C4 × C4))
      (_ : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2 ^ 3 ∧
        IsExtraspecial 2 (↥(twoCoreIn
          (EAt ctx.Γ ctx.criticalPath.firstStep))) ∧
        Nat.card (twoCoreIn
          (EAt ctx.Γ ctx.criticalPath.firstStep)) = 2 ^ 5)
      (_ : ∃ x : H,
        IsInvolution x ∧ x ∈ QAt ctx.Γ aPlus2 ∧
        x ∉ ZAt ctx.Γ aPlus2 ∧
        ¬ Group.IsSolvable (Subgroup.centralizer ({x} : Set H)))
  | b
      (_ : 2 ^ 11 ≤ Nat.card S ∧ Nat.card S ≤ 2 ^ 12)
      (_ : QuotientIsModel (GAt ctx.Γ aPlus2) (QAt ctx.Γ aPlus2) SL2Two ∧
        QuotientIsFrobenius20
          (GAt ctx.Γ ctx.criticalPath.firstStep)
          (QAt ctx.Γ ctx.criticalPath.firstStep))
      (_ : QuotientCardEq
          (VAt ctx.Γ ctx.criticalPath.firstStep)
          (ZAt ctx.Γ ctx.criticalPath.firstStep) (2 ^ 4) ∧
        QuotientCardEq
          (twoCoreIn (EAt ctx.Γ ctx.criticalPath.firstStep))
          (VAt ctx.Γ ctx.criticalPath.firstStep) (2 ^ 4) ∧
        DerivedAmbient (twoCoreIn
          (EAt ctx.Γ ctx.criticalPath.firstStep)) =
          VAt ctx.Γ ctx.criticalPath.firstStep)
      (_ : Nat.card (ZAt ctx.Γ aPlus2) = 4 ∧
        QuotientCardEq W Wnext 4 ∧
        QuotientCardEq Wnext W0 4 ∧
        QuotientCardEq
          (twoCoreIn (EAt ctx.Γ aPlus2) ⊔ Wnext) Wnext 4 ∧
        QuotientCardEq Wnext (ZAt ctx.Γ aPlus2) 2)

public structure LemmaTenOneConclusion
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionTenContext H S0 S P1 P2)
    (aPlus2 : ctx.Γ.Vertex) (W W0 Wnext : Subgroup H) : Prop where
  definitions :
    W = conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
        QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ aPlus2) ∧
    Wnext = GeneratedNeighborhoodV ctx.Γ aPlus2 ∧
    W0 = NeighborhoodQIntersection ctx.Γ
      (Neighborhood ctx.Γ aPlus2) ⊓ Wnext
  index_conclusions : QuotientCardEq W0 W 2 ∧
    QuotientCardEq Wnext W (2 ^ 3)
  barred_intersection :
    ∃ w : QuotientWitness
        (GAt ctx.Γ ctx.criticalPath.a')
        (ZAt ctx.Γ ctx.criticalPath.a'),
      let _ := w.groupX
      let _ := w.finiteX
      ∃ Wbar : Subgroup w.X,
        Wbar =
          ((VAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
              (GAt ctx.Γ ctx.criticalPath.a')).map w.projection ⊓
            ((VAt ctx.Γ ctx.criticalPath.a').subgroupOf
              (GAt ctx.Γ ctx.criticalPath.a')).map w.projection
  alternative : LemmaTenOneAlternative ctx aPlus2 W W0 Wnext

/-- **Stellmacher (10.1).**  In the remaining case `b=3`, the subgroups
`W`, `W₀`, and `W_{a+2}` have the stated indices and one of the two displayed
local configurations occurs. -/
public theorem lemma_ten_one
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionTenContext H S0 S P1 P2)
    (aPlus2 : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 aPlus2)
    (W W0 Wnext : Subgroup H)
    (hW : W = conjugateClosure
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓
        QAt ctx.Γ ctx.criticalPath.a')
      (GAt ctx.Γ aPlus2))
    (hWnext : Wnext = GeneratedNeighborhoodV ctx.Γ aPlus2)
    (hW0 : W0 = NeighborhoodQIntersection ctx.Γ
      (Neighborhood ctx.Γ aPlus2) ⊓ Wnext) :
    LemmaTenOneConclusion ctx aPlus2 W W0 Wnext := by
  sorry

end Stellmacher.SectionTen
