module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSevenOdd
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction
/-!
# The original Cartan A₇ witness excludes all odd Theorem C rows

The literal original local section and its full Sylow normalizer feed the
odd linear and ternary exclusions. The core is retained, including the
centralizer argument when the original two-core is nontrivial.
Source: Aschbacher–Smith 1.2.8, pp.506–507, and 5.1.13, p.637.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original A₇ witness excludes every odd containing-quotient row. -/
theorem localCartan_alternatingSeven_overcomponent_not_odd
    {T : Sylow 2 G} {H A Y X D K : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D)
    (hK : K ∈ Chapter1.LStar G (T : Subgroup G)) (hXK : X ≤ K)
    (hA : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7))) :
    ¬ ChapterA.Section02.IsTheoremCOddModel (K ⧸ pCore 2 K) :=
  Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenOdd.local_overcomponent_not_odd
    T (d.mem_localFamily hTH hY) (d.sylow_normalizes hTH hY.2) hK.1 hXK hA

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
