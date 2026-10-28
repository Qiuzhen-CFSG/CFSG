module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5ZeroPairedModules

/-!
# The original zero-center block's marked natural layer

The original Hypothesis 13.3.1 input supplies the Fundamental Setup, and the
source zero-center theorem identifies the intrinsic block layer with one
natural support of its actual paired quotient action.
Source: Aschbacher–Smith, 10.2.1 and13.3.2(2), pp.742–743 and884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem zero_original_layer_coordinates
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      Chapter10.SourceZeroOriginalLayerCoordinates D := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact ⟨D,Chapter10.source_a5_zero_original_layer_coordinates D e hn hout hz⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
