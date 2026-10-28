module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryLines
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryClosureSource
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryResidual

/-!
# The quadratic conjugate line on the original field-fixed layer

The elementary N_G(U)-closure makes every actor centralizing U quadratic
on B. The exact one-sided conjugate corank and A₂ geometry identify the
resulting commutator with an actual conjugate of Z_S. These supply both
geometric premises of the earlier residual-action construction and its
field-escape contradiction.

The final applications retain only relative normality of O²(N_L(U)) in
N_G(U). This is the local-component obligation in 6.1.14(5), still owned by
qt-d-1222-rankone-recognition-natural-contained. The conditional contained
branch is not asserted as the completed source proposition 6.1.15.
Source: Aschbacher–Smith, 6.1.14(5)–6.1.15, printed pp.671–672.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G} {n : ℕ}

/-- The exact conjugate-line equality, with no mutual-normalization premise. -/
theorem source_field_conjugate_line
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (g : G) (hg : commutatorLayer T L ≤
      normalizer ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    ∃ x : G, ⁅(commutatorLayer T L).map (MulAut.conj g).toMonoidHom,
      commutatorLayer T L⁆ =
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)).map
        (MulAut.conj x).toMonoidHom := by
  let := h611.layer_elementary
  have hE := source_natural_layer_hypothesisE61 D h h611 hnatural
  have hs := (source_natural_layer_rank_bounds D h h611 hnatural).2.2
  exact inverse_conjugate_commutator_line h611.n_gt_one hnatural hE.normalizer_le hs
    T h611.sylow_normalizes_L g hg hnon

/-- The elementary closure makes centralizers of U quadratic on B. -/
theorem source_field_conjugate_quadratic
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n) (hUne : U ≠ ⊥) (hn : 2 < n)
    (A : Subgroup G) (hA : A ≤ centralizer (U : Set G)) :
    ⁅A, commutatorLayer T L⁆ ≤ centralizer (commutatorLayer T L : Set G) := by
  obtain ⟨_, _, _, _, _, _, hEl, _⟩ :=
    source_field_fixedSpace_closure D h h611 hnatural hfield hUne hn
  let := hEl
  have hB : commutatorLayer T L ≤ fieldModuleClosure (commutatorLayer T L) U :=
    le_conjugateSpanBy _ _
  have hN : A ≤ normalizer (fieldModuleClosure (commutatorLayer T L) U : Set G) :=
    (hA.trans (Subgroup.centralizer_le_normalizer _)).trans (le_normalizer_conjugateSpanBy _ _)
  exact ((commutator_mono le_rfl hB).trans
    (le_normalizer_iff_commutator_le_right.mp hN)).trans
    ((fieldModuleClosure (commutatorLayer T L) U).le_centralizer.trans (centralizer_le hB))

/-- The field-escape contradiction after discharging the two geometric premises. -/
theorem source_field_escape_of_residual_normal
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n) (hUne : U ≠ ⊥) (hn : 2 < n)
    (hN : ((fieldLocalResidual L U).subgroupOf (normalizer (U : Set G))).Normal)
    (g : G) (hg : (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (U : Set G))
    (hmut : commutatorLayer T L ≤
      normalizer ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    ¬ centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G) := by
  obtain ⟨x, hline⟩ := source_field_conjugate_line D h h611 hnatural g hmut hnon
  exact source_field_conjugate_escape_of_residual_normality D h h611 hnatural
    hfield hUne hn hN g hg x hline
    (source_field_conjugate_quadratic D h h611 hnatural hfield hUne hn _ hg) hnon

/-- All local-action premises are now discharged except relative normality
of the field residual. That local-component theorem remains with this owner. -/
theorem source_fieldNaturalLocalAction_of_residual_normality
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hN : 2 < n → ∀ U : Subgroup G, U ≠ ⊥ →
      IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
        (commutatorLayer T L) U n →
      ((fieldLocalResidual L U).subgroupOf (normalizer (U : Set G))).Normal) :
    FieldNaturalLocalAction L (normalizer (L : Set G)) (commutatorLayer T L)
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)) n := by
  intro hn g U hUne _ hfield hg hmut hnon _
  obtain ⟨x, hline⟩ := source_field_conjugate_line D h h611 hnatural g hmut hnon
  have hquad := source_field_conjugate_quadratic D h h611 hnatural hfield hUne hn _ hg
  have hc : Nat.card (⁅(commutatorLayer T L).map (MulAut.conj g).toMonoidHom,
      commutatorLayer T L⁆ : Subgroup G) = 2 ^ n := by
    rw [hline, card_map_of_injective (MulAut.conj x).injective]
    exact (hnatural.sylow_intersection_geometry T h611.sylow_normalizes_L).1
  obtain ⟨m, hnm, hnat⟩ := source_field_conjugate_displacement_natural hnatural hfield
    hUne hn (hN hn U hUne hfield) g hg hquad hc hnon
  rw [hline] at hnat
  exact ⟨m, x, hnm, hnat⟩

/-- The contained-branch consumer, retaining exactly the pending residual
normality construction and no Sylow, weak-closure or line callbacks. -/
theorem source_contained_natural_of_residual_normality
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hout : Chapter3.HasMaximalOutside T (normalizer (L : Set G)))
    (hN : 2 < n → ∀ U : Subgroup G, U ≠ ⊥ →
      IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
        (commutatorLayer T L) U n →
      ((fieldLocalResidual L U).subgroupOf (normalizer (U : Set G))).Normal)
    (hI : centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G)) :
    ContainedAlternative (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) n :=
  source_contained_natural_of_field_action D h h611 hnatural hout
    (source_fieldNaturalLocalAction_of_residual_normality D h h611 hnatural hN) hI

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
