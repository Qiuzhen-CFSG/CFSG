module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalNoncyclic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalInitial

/-!
# Noncyclic-intersection commutation on the original Chapter 12 layer

The chosen module supplies E.6.1 and the distinguished-plane normalizer
factorization for the literal layer [R₂(LT),L]. Applying the field-plane
core argument to both conjugates proves the commuting_noncyclic clause
of the common LocalAnalysis contract, with no additional source premises.

The remaining local-analysis fields stay with
qt-d-1222-recognition-local-analysis; the final identification is assembled
by qt-d-1222-rankone-recognition-identification.

Source: Aschbacher--Smith, 6.2.5(5), printed p.681, applied to the whole
reduced layer in 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Source 6.2.5(5) for the actual whole reduced Chapter 12 layer. -/
theorem source_local_commuting_noncyclic
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hcard : 4 ≤ Nat.card (commutatorLayer T L ⊓
      (commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    ⁅commutatorLayer T L, (commutatorLayer T L).map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  exact local_commuting_noncyclic h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    (source_central_line_normalizer_factorization D h.toHypothesis1221 h611 hnatural.2.2.2.1)
    g hcard

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
