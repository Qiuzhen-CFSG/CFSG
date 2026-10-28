module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSevenMathieu
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction
/-!
# Original Cartan A₇ witnesses exclude the unwanted Mathieu rows

The actual local-family witness and its full Sylow normalization feed the
M₂₂/M₂₄ containing-carrier exclusions, with the original X and K and their
literal two-core quotient maps. No exchanged selection or exceptional
embedding catalogue is assumed.
Source: Aschbacher–Smith 1.2.8, pp.506–507, and 5.1.13, p.637.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original A₇ Cartan witness excludes both unwanted Mathieu
quotients of its maximal local overcomponent. -/
theorem localCartan_alternatingSeven_overcomponent_not_mathieuTwentyTwo_or_Four
    {T : Sylow 2 G} {H A Y X D K : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D)
    (hK : K ∈ Chapter1.LStar G (T : Subgroup G)) (hXK : X ≤ K)
    (hA : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7))) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) ∧
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M24) :=
  Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenMathieu.local_overcomponent_not_mathieuTwentyTwo_or_Four
    T (d.mem_localFamily hTH hY) (d.sylow_normalizes hTH hY.2) hK.1 hXK hA

/-- The same original witness also excludes the full central three-cover
of M₂₂, preserving the covering kernel in the containing quotient. -/
theorem localCartan_alternatingSeven_overcomponent_not_mathieuTwentyTwo_cover
    {T : Sylow 2 G} {H A Y X D K : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D)
    (hK : K ∈ Chapter1.LStar G (T : Subgroup G)) (hXK : X ≤ K)
    (hA : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7))) :
    ¬ Chapter1.Section02.LocalModels.IsM22Cover (K ⧸ pCore 2 K) :=
  Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenMathieu.local_overcomponent_not_mathieuTwentyTwo_cover
    T (d.mem_localFamily hTH hY) (d.sylow_normalizes hTH hY.2) hK.1 hXK hA

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
