module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Source
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers.Alignment
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.LocalClauses
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Head
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Remaining component arguments for original plane centralizers

These contracts expose three unfinished source arguments. The first constructs
an actual escaping relative C-component and a Sylow subgroup of C_G(A) inside
N_G(L). The second performs C.2.7 inspection, with literal block and quotient
models. The third excludes the binary linear-three row using the original
chief factors. None of these implications is asserted here.

The normalizer condition is Q ≤ N_G(J), not ambient normality of J. The
linear-three input is formed inside JQ, and its residual is O^{3'}(C_G(A)),
using `primeToResidual`, not the 3-group residual. The compatible Sylow in
C_G(A) is chosen independently of the initially fixed T.

Source: Aschbacher--Smith 13.3.12, printed pp.889--890; C.2.3--7 and C.1.34.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
open ChapterE Atlas.G2.Natural.BinaryNondegeneratePlane
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A chart carrying the original subgroup A to the standard nondegenerate plane. -/
structure MarkedPlane (V : Subgroup G) [IsElementaryAbelian 2 V] where
  chart : Automizer V →* Atlas.G2.Model K
  coordinates : Additive V ≃ₗ[K] W
  equivariant : ∀ a v, coordinates (automizerRepresentation V a v) =
    rho (chart a) (coordinates v)
  A : Subgroup G
  le_module : A ≤ V
  plane_space : pointCoordinateSubspace coordinates A = plane

variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The actual C.2.3 setup and escaping normalized component, before inspection. -/
structure LocalData (T : Sylow 2 G) (L : Subgroup G) (d : MarkedPlane V) (J : Subgroup G) where
  input : Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.Input
    KnownSimple.IsKnownSimple (centralizer (d.A : Set G)) ((L ⊔ T).pCoreIn 2)
      (centralizer (d.A : Set G) ⊓ normalizer (L : Set G)) J
  characteristic : HasCharacteristicTwo (centralizer (d.A : Set G))
  sylow : Sylow 2 (centralizer (d.A : Set G))
  sylow_in_M : (sylow : Subgroup (centralizer (d.A : Set G))).map
    (centralizer (d.A : Set G)).subtype ≤ normalizer (L : Set G)

/-- The terminal rank-one row. Perpendicular containment in U(J) is not assumed. -/
structure RankOneRow (T : Sylow 2 G) (L : Subgroup G) (d : MarkedPlane V)
    (J : Subgroup G) : Prop where
  block : ChapterC.IsL2EvenBlock J 2
  sylow : Chapter1.IsSylowIn 2 ((L ⊔ T).pCoreIn 2) (J ⊔ (L ⊔ T).pCoreIn 2)
  characteristic : HasCharacteristicTwo (J ⊔ (L ⊔ T).pCoreIn 2 : Subgroup G)
  cubic : ∃ n : normalizer (V : Set G), n.val ∈ J ∧
    d.chart (V.normalizerMonoidHom.rangeRestrict n) = cubic

/-- The terminal linear-three row, with the genuine binary MS hypotheses. -/
structure LinearThreeRow (T : Sylow 2 G) (L : Subgroup G) (d : MarkedPlane V)
    (J : Subgroup G) where
  input : ChapterC.BinaryMS.Input KnownSimple.IsKnownSimple
    (J.subgroupOf (J ⊔ (L ⊔ T).pCoreIn 2))
    (((L ⊔ T).pCoreIn 2).subgroupOf (J ⊔ (L ⊔ T).pCoreIn 2))
  residual : J = (primeToResidual 3 (centralizer (d.A : Set G))).map
    (centralizer (d.A : Set G)).subtype
  cubic : ∃ n : normalizer (V : Set G), n.val ∈ J ∧
    d.chart (V.normalizerMonoidHom.rangeRestrict n) = cubic

/-- Pending source extraction, including exclusion of the swapped-component branch. -/
@[expose] def LocalExtraction (T : Sylow 2 G) (L V : Subgroup G) [IsElementaryAbelian 2 V] : Prop :=
  ∀ d : MarkedPlane V, ¬ centralizer (d.A : Set G) ≤ normalizer (L : Set G) →
    ∃ J : Subgroup G, Nonempty (LocalData T L d J)

/-- Pending specialized C.2.7 inspection, including the field-degree reductions. -/
@[expose] def ComponentInspection (T : Sylow 2 G) (L V : Subgroup G) [IsElementaryAbelian 2 V] : Prop :=
  ∀ (d : MarkedPlane V) (J : Subgroup G), LocalData T L d J →
    RankOneRow T L d J ∨ Nonempty (LinearThreeRow T L d J)

/-- Pending construction of the chief-factor contradiction in the original Q/V. -/
@[expose] def LinearThreeExclusion (T : Sylow 2 G) (L V : Subgroup G) [IsElementaryAbelian 2 V] : Prop :=
  ∀ (d : MarkedPlane V) (J : Subgroup G), LocalData T L d J →
    LinearThreeRow T L d J → False

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion.OriginalPlaneCentralizers
