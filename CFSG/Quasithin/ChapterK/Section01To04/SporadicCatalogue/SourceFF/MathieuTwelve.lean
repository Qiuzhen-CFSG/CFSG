module
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.SourceFF.Remaining
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.NoFF

/-!
# The original M12 source action has no FF offenders

Native recognition marks the full original action by an injective map to
Aut(M12) and the literal ten-dimensional heart. The completed inner and outer
involution displacement bounds exclude FF on that heart; its equivariant
marking transports this exclusion to the original source module.

Source: Aschbacher--Smith B.4.2, K.4 and H.11, printed pp.86, 457 and 392--394.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
open Subgroup Representation Representation.BinaryOffender
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- The M12 source branch has no additional module or local-action premise. -/
theorem not_ff_m12 (h : RankOne.SourceHypotheses ρ L)
    (he : Nonempty (L ⧸ center L ≃* KnownSimple.SporadicName.m12.Carrier)) :
    ¬ IsFFModule ρ :=
  not_ff_m12_of_native
    ChapterH.Section10To12.M12Calculations.automorphismRepresentation_not_isFFModule h he
end CFSG.Quasithin.ChapterK.SporadicCatalogue.SourceFF
