module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometrySubmodule
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometrySplitting
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldSolvable

/-!
# Invariant conjugate lines on the original Chapter 12 layer

The two-copy decomposition supplies natural markings on residual-invariant
subgroups of the required order. For a conjugate of Z_S contained in the
original layer, the proved Sylow fixed-line order supplies that order.
The actual normalizer action is then nonsolvable, contrary to the proved
solvable action in M when C_G(Z_S) is contained in M.

The containment and invariance of this conjugate remain explicit geometric
premises owned by qt-d-1222-rankone-recognition-natural-contained. These
applications prove the representation and contradiction steps, not the
whole source 6.1.14(5) or 6.1.15.
Source: Aschbacher–Smith, printed pp.671–672.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U A : Subgroup G} {n : ℕ}

/-- The source corank-n subgroup is natural once the residual normalizes it. -/
theorem source_field_fixedSpace_corank_invariant_natural
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n) (hUne : U ≠ ⊥) (hn : 2 < n)
    (hAB : A ≤ commutatorLayer T L)
    (hcor : ChapterE.subgroupCorank (commutatorLayer T L) A = n)
    (hRA : fieldLocalResidual L U ≤ normalizer (A : Set G)) :
    ∃ m, n = 2 * m ∧ Chapter6.Source.IsNaturalModule (fieldLocalResidual L U) A m := by
  let := h611.layer_elementary
  exact field_fixedSpace_corank_invariant_natural hnatural hfield hUne hn hAB hcor hRA

/-- The Sylow fixed-line order supplies the natural marking on an invariant
conjugate line lying in the original layer. -/
theorem source_field_conjugate_natural
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n) (hUne : U ≠ ⊥) (hn : 2 < n) (x : G)
    (hxB : (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)).map
      (MulAut.conj x).toMonoidHom ≤ commutatorLayer T L)
    (hxR : fieldLocalResidual L U ≤ normalizer
      ((Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)).map
        (MulAut.conj x).toMonoidHom : Set G)) :
    ∃ m, n = 2 * m ∧ Chapter6.Source.IsNaturalModule (fieldLocalResidual L U)
      ((Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)).map
        (MulAut.conj x).toMonoidHom) m := by
  apply field_fixedSpace_invariant_natural hnatural hfield hUne hn hxB _ hxR
  rw [card_map_of_injective (MulAut.conj x).injective]
  exact (hnatural.sylow_intersection_geometry T h611.sylow_normalizes_L).1

/-- Applying the marked line to the literal normalizer action gives the
field-escape contradiction. Its geometric containment and invariance
premises remain with the contained-branch source assembly. -/
theorem source_field_conjugate_escape_of_invariant_line
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n) (hUne : U ≠ ⊥) (hn : 2 < n) (x : G)
    (hxB : (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)).map
      (MulAut.conj x).toMonoidHom ≤ commutatorLayer T L)
    (hxR : fieldLocalResidual L U ≤ normalizer
      ((Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)).map
        (MulAut.conj x).toMonoidHom : Set G)) :
    ¬ centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G) := by
  obtain ⟨m, hnm, hnat⟩ := source_field_conjugate_natural h611 hnatural hfield hUne hn x hxB hxR
  apply centralizer_not_le_of_nonsolvable_conjugate_action
    (normalizer (L : Set G)) (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L))
    (fieldLocalResidual L U) x _ (source_central_line_action_solvable h611 hnatural) hxR
    (normalizerAction_not_solvable_of_natural hnat (by omega))
  intro hI d hd
  obtain ⟨c, hc, m, hm, rfl⟩ :=
    source_central_line_normalizer_factorization D h h611 hI d hd
  exact mul_mem (hI hc) hm.1

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
