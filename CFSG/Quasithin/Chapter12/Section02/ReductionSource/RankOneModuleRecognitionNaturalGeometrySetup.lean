module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometrySetup
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryNormalizer

/-!
# G.2.1 and its closure consequences on the Chapter 12 layer

The actual natural action on [R₂(LT),L] supplies G.2.1, including the
irreducibility of its quotient by Z_S under O²(N_L(Z_S)). The existing
normalizer bound and E.6.1 discharge all extra premises of the closure
comparison, giving the literal U its Frattini and full-normalizer core
bounds. These are the G.2.2 inputs consumed by 6.1.21.

The initial natural marking and escaping nonabelianness remain with
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.20–21, pp.675–676, and G.2.1–2, p.332.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The original five subgroups satisfy all of G.2.1. -/
theorem source_escape_G2_hypothesis
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n) :
    (naturalEscapeSetup (T : Subgroup G) L (wholeReduced T L)).Hypothesis :=
  natural_escape_G2_hypothesis h611 hnatural

/-- The exact earlier G.2.2 conclusions needed by the escaping geometry.
The source E.6.1 and normalizer bound are discharged on this whole layer. -/
theorem source_escape_frattini_and_normalizer_core
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n) :
    (frattini (Escape.U (T : Subgroup G) L (wholeReduced T L))).map
        (Escape.U (T : Subgroup G) L (wholeReduced T L)).subtype ≤
        ZS (T : Subgroup G) L (wholeReduced T L) ∧
      Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
        (Escape.H (T : Subgroup G) L (wholeReduced T L)).pCoreIn 2 ∧
      ⁅Escape.U (T : Subgroup G) L (wholeReduced T L),
        (Escape.H (T : Subgroup G) L (wholeReduced T L)).pCoreIn 2⁆ ≤
        ZS (T : Subgroup G) L (wholeReduced T L) :=
  natural_escape_frattini_and_normalizer_core h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_central_line_S_normalizer_le D h h611)

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
