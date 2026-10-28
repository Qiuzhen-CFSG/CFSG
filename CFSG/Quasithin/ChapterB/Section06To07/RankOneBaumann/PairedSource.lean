module
public import CFSG.Quasithin.ChapterB.Section02.Baumann.ActionQuotient
public import Theory.Representation.SL2NaturalOffenders.NaturalPair

/-!
# The paired natural source layer discharges Baumann hypothesis (c)

Keep the actual quotient by C_G(U). The B.6.9 best-offender layer may have
a faithful natural two-factor quotient even when the whole ambient group
permutes the factors. Strong replacement lies in that layer, so the concrete
product estimate excludes strong offenders in the original group.
The literal quotient/action transport then gives B.2.18(c).
The B.6.9 layer and natural marker are explicit earlier-source inputs;
no Baumann image, fixed-space splitting, or Sylow conclusion is assumed.
Source: Aschbacher–Smith B.6.9–10 and E.2.3, pp.116–117 and216–217.
-/

open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
variable {G A F : Type*} [Group G] [Finite G] [Group A] [Finite A]
  [Field F] [Finite F] [Algebra (ZMod 2) F]
local notation "D" => SL2NaturalOffenders.NoStrong.Actor F

public theorem noStrong_of_naturalPair_source_layer
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* A) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (Y : Subgroup A)
    (hY : BinaryOffender.offenderSubgroup
      (NormalElementaryQuotient.representation U q hq hker) ≤ Y)
    (j : Y →* D × D) (hj : Function.Injective j)
    (f : Additive U →ₗ[ZMod 2] ((Fin 2 → F) × (Fin 2 → F))) (hf : Function.Surjective f)
    (he : ∀ (g : Y) w, f (NormalElementaryQuotient.representation U q hq hker (g : A) w) =
      SL2NaturalOffenders.naturalPair (F := F) (j g) (f w))
    (R : Subgroup G) : BaumannArgument.NoStrongOffenders U R := by
  apply BaumannArgument.noStrong_of_centralizer_quotient U q hq hker _ R
  exact SL2NaturalOffenders.not_strong_of_naturalPair_layer
    (NormalElementaryQuotient.representation U q hq hker) Y hY j hj f hf he
end CFSG.Quasithin.ChapterB.RankOneBaumann
