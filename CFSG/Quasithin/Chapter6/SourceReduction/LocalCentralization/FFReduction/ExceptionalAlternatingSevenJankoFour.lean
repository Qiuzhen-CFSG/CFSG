module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.ExceptionalOvercomponentsAlternatingSevenJankoFour
public import CFSG.Quasithin.Chapter6.SourceReduction.LocalCentralization.FFReduction
/-!
# The original Cartan A₇ witness excludes J₄

The actual local family and its full Sylow normalization give the local
J₄ pair placement. Both native involution-centralizer classes are excluded
through their full M₂₂ and M₂₄ quotient maps, preserving the original
containing subgroup and its two-core quotient.
Source: Aschbacher–Smith 1.2.8, pp.506–507, and 5.1.13, p.637.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The original A₇ witness excludes J₄ as the actual maximal local quotient. -/
theorem localCartan_alternatingSeven_overcomponent_not_jankoFour
    {T : Sylow 2 G} {H A Y X D K : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D)
    (hK : K ∈ Chapter1.LStar G (T : Subgroup G)) (hXK : X ≤ K)
    (hA : Nonempty ((X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 7))) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) :=
  Chapter1.Section02.ExceptionalOvercomponents.AlternatingSevenJankoFour.local_overcomponent_not_jankoFour
    T (d.mem_localFamily hTH hY) (d.sylow_normalizes hTH hY.2) hK.1 hXK hA

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
