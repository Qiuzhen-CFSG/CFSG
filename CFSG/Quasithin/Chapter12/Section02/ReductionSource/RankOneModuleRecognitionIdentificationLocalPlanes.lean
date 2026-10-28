module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalPlanes
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalInitial

/-!
# Central-plane fusion on the whole Chapter 12 layer

The chosen module supplies E.6.1 and the distinguished-plane normalizer
factorization. A plane whose normalizer contains an ambient Sylow is of
central type; applying this to a conjugate of Z_S proves uniqueness of
the original natural layer over Z_S. This discharges LocalAnalysis.plane_unique
without assuming that record or invoking M₂₂ recognition.

The remaining common analysis stays with qt-d-1222-recognition-local-analysis;
final identification is owned by qt-d-1222-rankone-recognition-identification.
Source: Aschbacher--Smith, 6.2.5(3--4), printed p.681, applied to
[R₂(LT),L] in 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Central-type plane fusion on the actual whole reduced layer. -/
theorem source_local_plane_of_sylow_normalizer
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    {U : Subgroup G} (hUB : U ≤ commutatorLayer T L) (hU : Nat.card U = 4)
    (P : Sylow 2 G) (hPN : (P : Subgroup G) ≤ normalizer (U : Set G)) :
    ∃ l ∈ L, U = (ZS (T : Subgroup G) L (wholeReduced T L)).map
      (MulAut.conj l).toMonoidHom := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  exact local_plane_of_sylow_normalizer h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat) hUB hU P hPN

/-- The exact plane_unique clause of the common recognition analysis. -/
theorem source_local_plane_unique
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G) (hg : ZS (T : Subgroup G) L (wholeReduced T L) ≤
      (commutatorLayer T L).map (MulAut.conj g).toMonoidHom) :
    (commutatorLayer T L).map (MulAut.conj g).toMonoidHom = commutatorLayer T L := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  exact local_plane_unique h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    (source_central_line_normalizer_factorization D h.toHypothesis1221 h611 hnatural.2.2.2.1)
    g hg

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
