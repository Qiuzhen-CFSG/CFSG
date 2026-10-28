module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.Held.FFModels
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.FFClassification

/-!
# The Held component excluded by the proved full FF source theorem

Original characteristic-two and CPU geometry constructs the local omega
action and its actual offender. Full B.5.1 places the same Held quotient on
its ten-model list, contradicting the concrete Sylow-center and order
comparisons. The complete C.2.7 classification is no longer an input to
this retained branch of the adequate intrinsic embedding theorem.
Source: Aschbacher--Smith B.5.1, C.2.7 and 15.4.20.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination
open BlockSieve BlockSieve.ExchangedCases.SourceAssembly
universe u
variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K : Subgroup G}

theorem not_held_single_component_from_ff
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (h : Input d i j H U K)
    (unique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      d.wholeX ⊔ (d.T : Subgroup G) ≤ N → N = d.M₁)
    (hK : (K.subgroupOf H).IsCComponent)
    (hq : IsQuasisimple (Chapter1.XiQuotient K))
    (e : Chapter1.XiQuotient K ≃* Held.He) : False :=
  HeldModels.not_ff_model (source_held_ff_model hG h unique hK hq e)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination
