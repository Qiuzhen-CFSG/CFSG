module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryGraphNeighbors
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryGraphEndpoints

/-!
# The moving neighbor on the original reduced layer

The contrary abelian assumption supplies the actual odd critical
configuration. Its generation parameter one now constructs an opposite
neighbor with an index-two normalizer in the original closure. The chosen
module supplies the exact global-s bound, proving that the resulting
hyperplane acts nontrivially. Both crossed centralizers retain the original
ambient conjugator.

These are the first neighbor and movement steps of 6.1.19. The remaining
commutator-line, parameter and nonabelianness arguments, the initial natural
action and final 6.1.27 assembly remain with
qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.19, printed pp.673–675; F.7.13(1), p.314.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The source's opposite neighbor, its hyperplane normalizer and its
nontrivial action, with E-generation and the global-s premise discharged. -/
theorem source_escape_moving_neighbor_of_abelian
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    (hab : Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G)) :
    ∃ d : NaturalEscapeGraph.OddConfiguration T L (normalizer (L : Set G)) (wholeReduced T L),
      d.localClosure.map (MulAut.conj d.representative).toMonoidHom ≤
        d.H ⊓ Escape.I (T : Subgroup G) L (wholeReduced T L) ∧
      d.localClosure ≤ (d.H ⊓ Escape.I (T : Subgroup G) L (wholeReduced T L)).map
        (MulAut.conj d.representative).toMonoidHom ∧
      ∃ a : G, let E := (commutatorLayer T L).map (MulAut.conj a).toMonoidHom
        d.representative⁻¹ * a ∈ d.H ∧
        (ZS (T : Subgroup G) L (wholeReduced T L)).map (MulAut.conj a).toMonoidHom =
          (ZS (T : Subgroup G) L (wholeReduced T L)).map
            (MulAut.conj d.representative).toMonoidHom ∧
        E ≤ d.localClosure.map (MulAut.conj d.representative).toMonoidHom ∧
        (normalizer (E : Set G)).relIndex d.localClosure = 2 ∧
        ⁅E,d.localClosure ⊓ normalizer (E : Set G)⁆ ≠ ⊥ := by
  obtain ⟨d,hleft,hright⟩ := source_escape_odd_crossed_configuration_of_abelian
    D h h611 hnatural hI hab
  exact ⟨d,hleft,hright,d.exists_moving_index_two_neighbor h611
    (source_natural_layer_rank_bounds D h h611 hnatural).2.2⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
