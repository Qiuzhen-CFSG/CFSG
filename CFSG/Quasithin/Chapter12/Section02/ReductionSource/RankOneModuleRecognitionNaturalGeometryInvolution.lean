module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryInvolution
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryHyperplanes

/-!
# The odd common-involution centralizer on the original reduced layer

The chosen module supplies E.6.1, global s=n and the central-line
normalizer bound. Applied to the odd critical configuration, the common
involution has a characteristic-two centralizer whose two-core contains
the closure of the natural Sylow line and centralizes it modulo the
involution. Both the original natural layer and a displayed moving layer
escape that two-core. The second application constructs this configuration
from the contrary abelian-closure assumption.

The remaining transvection argument, initial natural action and
Sylow-centralizer proof, and final source 6.1.27 assembly remain with
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.19, printed pp.674–675.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The involution centralizer and its line closure, with the Chapter 12
rank and normalizer premises discharged on the literal reduced layer. -/
theorem source_escape_odd_involution_centralizer_geometry
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (d : NaturalEscapeGraph.OddConfiguration T L (normalizer (L : Set G)) (wholeReduced T L)) :
    n = 2 ∧ ∃ z : G,
      z ∈ ZS (T : Subgroup G) L (wholeReduced T L) ⊓
        (ZS (T : Subgroup G) L (wholeReduced T L)).map
          (MulAut.conj d.representative).toMonoidHom ∧
      orderOf z = 2 ∧
      let C := centralizer ({z} : Set G)
      let Q := conjugateSpanBy (ZS (T : Subgroup G) L (wholeReduced T L)) C
      C ∈ Chapter1.He G ∧ Q ≤ C.pCoreIn 2 ∧ ⁅Q,C.pCoreIn 2⁆ ≤ zpowers z ∧
      ¬ commutatorLayer T L ≤ C.pCoreIn 2 ∧
      ∃ a : G, z ∈ (commutatorLayer T L).map (MulAut.conj a).toMonoidHom ∧
        ¬ (commutatorLayer T L).map (MulAut.conj a).toMonoidHom ≤ C.pCoreIn 2 :=
  d.exists_involution_centralizer_geometry h611 hnatural
    (source_natural_layer_hypothesisE61 D h h611 hnatural)
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2
    (source_central_line_S_normalizer_le D h h611)

/-- An abelian escaping closure supplies the actual odd configuration and
common involution used in the remaining transvection contradiction. -/
theorem source_escape_involution_centralizer_geometry_of_abelian
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    (hab : Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G)) :
    n = 2 ∧
    ∃ d : NaturalEscapeGraph.OddConfiguration T L (normalizer (L : Set G)) (wholeReduced T L),
      ∃ z : G,
        z ∈ ZS (T : Subgroup G) L (wholeReduced T L) ⊓
          (ZS (T : Subgroup G) L (wholeReduced T L)).map
            (MulAut.conj d.representative).toMonoidHom ∧
        orderOf z = 2 ∧
        let C := centralizer ({z} : Set G)
        let Q := conjugateSpanBy (ZS (T : Subgroup G) L (wholeReduced T L)) C
        C ∈ Chapter1.He G ∧ Q ≤ C.pCoreIn 2 ∧ ⁅Q,C.pCoreIn 2⁆ ≤ zpowers z ∧
        ¬ commutatorLayer T L ≤ C.pCoreIn 2 ∧
        ∃ a : G, z ∈ (commutatorLayer T L).map (MulAut.conj a).toMonoidHom ∧
          ¬ (commutatorLayer T L).map (MulAut.conj a).toMonoidHom ≤ C.pCoreIn 2 := by
  obtain ⟨d⟩ := source_escape_odd_configuration_of_abelian D h h611 hnatural hI hab
  obtain ⟨hn,hz⟩ := source_escape_odd_involution_centralizer_geometry D h h611 hnatural d
  exact ⟨hn,d,hz⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
