module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductSeed
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalSelection

/-!
# TerminalProductSeed at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalProductSeed`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

omit [Finite G] in

private theorem orbit_eq_span_at (A H : Subgroup G) :
    componentOrbit A H = conjugateSpanBy A H := by
  apply le_antisymm
  · exact iSup_conjugates_le_of_le_normalizer A H _
      (le_conjugateSpanBy A H) (le_normalizer_conjugateSpanBy A H)
  · exact conjugateSpanBy_le (le_componentOrbit A H) (le_normalizer_componentOrbit A H)

theorem L1_eq_ambient_residual_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hres : (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L) :
    P.L1 = (primeToResidual 3 (centralizer (P.Z : Set G))).map
      (centralizer (P.Z : Set G)).subtype := by
  have he := embedded_primeToResidual_intersection 3 (normalizer (L : Set G))
    (centralizer (P.Z : Set G))
  rw [hres, inf_eq_right.mpr (omega_center_centralizer_le_at S D structural)] at he
  exact he

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

