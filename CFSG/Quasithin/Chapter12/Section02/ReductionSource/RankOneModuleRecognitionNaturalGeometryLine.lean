module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryLine
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalGeometryGraphNeighbors

/-!
# Both moving neighbors on the original reduced layer

The contrary abelian assumption constructs the actual odd critical
configuration. The chosen module supplies the global-s value, E.6.1 and
the central-line normalizer bound. The line-identification argument then
constructs both index-two neighbors, proves their exact commutator lines,
and shows that the first neighbor escapes the local two-core.

This supplies the two-neighbor configuration in source 6.1.19 without
extra selection or displacement premises. Its parameter reduction and
nonabelianness, initial natural action, and final 6.1.27 assembly remain
with qt-d-1222-rankone-recognition-natural.
Source: Aschbacher–Smith, 6.1.19, printed pp.673–675.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The distinct endpoint lines, both actual neighbors, both index-two
normalizers and both commutator-line equalities on the Chapter 12 layer. -/
theorem source_escape_two_neighbors_of_abelian
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : IsNaturalModule L (commutatorLayer T L) n)
    (hI : ¬ Escape.I (T : Subgroup G) L (wholeReduced T L) ≤ normalizer (L : Set G))
    (hab : Escape.U (T : Subgroup G) L (wholeReduced T L) ≤
      centralizer (Escape.U (T : Subgroup G) L (wholeReduced T L) : Set G)) :
    ∃ d : NaturalEscapeGraph.OddConfiguration T L (normalizer (L : Set G)) (wholeReduced T L),
      let Z := ZS (T : Subgroup G) L (wholeReduced T L)
      let Z' := Z.map (MulAut.conj d.representative).toMonoidHom
      Z' ≠ Z ∧
      d.localClosure.map (MulAut.conj d.representative).toMonoidHom ≤
        d.H ⊓ Escape.I (T : Subgroup G) L (wholeReduced T L) ∧
      d.localClosure ≤ (d.H ⊓ Escape.I (T : Subgroup G) L (wholeReduced T L)).map
        (MulAut.conj d.representative).toMonoidHom ∧
      ∃ (a : G) (k : d.H), let E := (commutatorLayer T L).map (MulAut.conj a).toMonoidHom
        let V₀ := (commutatorLayer T L).map (MulAut.conj (k : G)).toMonoidHom
        d.representative⁻¹ * a ∈ d.H ∧
        E ≤ d.localClosure.map (MulAut.conj d.representative).toMonoidHom ∧
        V₀ ≤ d.localClosure ∧
        (normalizer (E : Set G)).relIndex d.localClosure = 2 ∧
        ⁅E,d.localClosure ⊓ normalizer (E : Set G)⁆ = Z' ∧
        ¬ E ≤ d.H.pCoreIn 2 ∧
        (normalizer (V₀ : Set G)).relIndex E = 2 ∧
        ⁅V₀,E ⊓ normalizer (V₀ : Set G)⁆ = Z := by
  obtain ⟨d,hleft,hright⟩ := source_escape_odd_crossed_configuration_of_abelian
    D h h611 hnatural hI hab
  have hE := source_natural_layer_hypothesisE61 D h h611 hnatural
  have hs := (source_natural_layer_rank_bounds D h h611 hnatural).2.2
  have hNS := source_central_line_S_normalizer_le D h h611
  exact ⟨d,d.endpoint_line_ne h611 hnatural hE hNS,hleft,hright,
    d.exists_two_neighbors h611 hnatural hE hs hNS⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
