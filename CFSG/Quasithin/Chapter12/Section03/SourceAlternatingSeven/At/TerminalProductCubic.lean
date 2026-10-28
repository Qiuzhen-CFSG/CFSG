module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductCubic
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalComponentPreparation
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.TerminalProductResidual

/-!
# TerminalProductCubic at the original ambient group and Sylow subgroup

These are the same source arguments as `TerminalProductCubic`, with structural
12.2.2 and its module alternatives restricted to the original G,T. Every
chosen subgroup, central quotient, action and relative normality statement
is retained. Independent definitions and lemmas are imported unchanged.
The universal statements remain available from the original module.

Source: Aschbacher–Smith, 12.3.1–13, printed pp.807–812.
-/

@[expose] public noncomputable section

open Subgroup Theory.GroupTheory

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

open Section02 BinarySevenCode

universe u

variable {G : Type u} [Group G] [Finite G]

variable {T : Sylow 2 G} {L V : Subgroup G}

variable {S : Setup T L V} {D : S.LocalAnalysis}

namespace TerminalPoint

variable (P : TerminalPoint S D)

theorem L1_eq_ambient_residual_of_component_at (C : P.ComponentAnalysis)
    (structural : Structural1222At KnownSimple.IsKnownSimple T) :
    P.L1 = (primeToResidual 3 (centralizer (P.Z : Set G))).map
      (centralizer (P.Z : Set G)).subtype :=
  P.L1_eq_ambient_residual_at structural (P.normalizer_residual C)

end TerminalPoint

end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

