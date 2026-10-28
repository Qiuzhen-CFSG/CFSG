module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalComponentA314
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentAmbientUniqueness

/-!
# TerminalComponentA314 at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalComponentA314`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

theorem proper_component_eq_residual_of_natural_omega_source_at
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (R : P.ResidualAnalysis) (F : P.Overcomponents)
    (hKY : P.K < F.Y) {W : Subgroup G} (SY : Setup T F.Y W)
    (DY : SY.NaturalCoordinates) (hsplit : SY.NaturalOmegaDecomposition)
    (hLe : F.E = F.Y → P.Le ≤ F.Y) : F.E = P.K :=
  P.proper_component_eq_residual_of_natural_omega_at structural R F hKY SY DY hsplit
    (P.a314RestrictionInput R) hLe

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

