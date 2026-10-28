module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryDisplacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometrySubmodule

/-!
# Residual action and the source field-escape contradiction

On the original Chapter 12 layer, relative normality of O²(N_L(U)) gives
its invariance of the literal conjugate displacement. The two-copy image
argument then gives a genuine natural marking when this displacement is
quadratic and has the order of Z_S. Identifying it with a conjugate of Z_S
supplies its order and contradicts the proved solvability of Aut_M(Z_S).

The Sylow/local-component normality and quadratic line identification remain
explicit source obligations of qt-d-1222-rankone-recognition-natural-contained.
No assertion of the full 6.1.14(5) or 6.1.15 is made here.
Source: Aschbacher–Smith, printed pp.671–672.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G} {n : ℕ}

/-- The residual preserves the exact conjugate displacement in 6.1.14(5). -/
theorem source_field_residual_normalizes_conjugate_displacement
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n) (hUne : U ≠ ⊥) (hn : 2 < n)
    (hN : ((fieldLocalResidual L U).subgroupOf (normalizer (U : Set G))).Normal)
    (g : G) (hg : (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (U : Set G)) :
    fieldLocalResidual L U ≤ normalizer
      (⁅(commutatorLayer T L).map (MulAut.conj g).toMonoidHom,
        commutatorLayer T L⁆ : Subgroup G) :=
  field_fixedSpace_residual_normalizes_displacement hnatural hfield hUne hn hN hg

/-- A quadratic conjugate displacement of order 2ⁿ has the actual half-degree
natural action of the residual, even if it lies outside the original B. -/
theorem source_field_conjugate_displacement_natural
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n) (hUne : U ≠ ⊥) (hn : 2 < n)
    (hN : ((fieldLocalResidual L U).subgroupOf (normalizer (U : Set G))).Normal)
    (g : G) (hg : (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (U : Set G))
    (hquad : ⁅(commutatorLayer T L).map (MulAut.conj g).toMonoidHom,
      commutatorLayer T L⁆ ≤ centralizer (commutatorLayer T L : Set G))
    (hcard : Nat.card (⁅(commutatorLayer T L).map (MulAut.conj g).toMonoidHom,
      commutatorLayer T L⁆ : Subgroup G) = 2 ^ n)
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    ∃ m, n = 2 * m ∧ Chapter6.Source.IsNaturalModule (fieldLocalResidual L U)
      ⁅(commutatorLayer T L).map (MulAut.conj g).toMonoidHom, commutatorLayer T L⁆ m :=
  field_fixedSpace_displacement_natural hnatural hfield hUne hn hN hg hquad hcard hnon

/-- Relative normality and the quadratic conjugate-line identification supply
the actual natural action and hence the field-escape contradiction. These
geometric premises remain with this task's final source assembly. -/
theorem source_field_conjugate_escape_of_residual_normality
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n) (hUne : U ≠ ⊥) (hn : 2 < n)
    (hN : ((fieldLocalResidual L U).subgroupOf (normalizer (U : Set G))).Normal)
    (g : G) (hg : (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (U : Set G)) (x : G)
    (hline : ⁅(commutatorLayer T L).map (MulAut.conj g).toMonoidHom,
        commutatorLayer T L⁆ =
      (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L)).map
        (MulAut.conj x).toMonoidHom)
    (hquad : ⁅(commutatorLayer T L).map (MulAut.conj g).toMonoidHom,
      commutatorLayer T L⁆ ≤ centralizer (commutatorLayer T L : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    ¬ centralizer (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L) : Set G) ≤
      normalizer (L : Set G) := by
  have hcard : Nat.card (⁅(commutatorLayer T L).map (MulAut.conj g).toMonoidHom,
      commutatorLayer T L⁆ : Subgroup G) = 2 ^ n := by
    rw [hline, card_map_of_injective (MulAut.conj x).injective]
    exact (hnatural.sylow_intersection_geometry T h611.sylow_normalizes_L).1
  obtain ⟨m, hnm, hnat⟩ := source_field_conjugate_displacement_natural
    hnatural hfield hUne hn hN g hg hquad hcard hnon
  rw [hline] at hnat
  have hxR := source_field_residual_normalizes_conjugate_displacement
    hnatural hfield hUne hn hN g hg
  rw [hline] at hxR
  apply centralizer_not_le_of_nonsolvable_conjugate_action
    (normalizer (L : Set G)) (Chapter6.Source.ZS (T : Subgroup G) L (wholeReduced T L))
    (fieldLocalResidual L U) x _ (source_central_line_action_solvable h611 hnatural) hxR
    (normalizerAction_not_solvable_of_natural hnat (by omega))
  intro hI d hd
  obtain ⟨c, hc, m, hm, rfl⟩ :=
    source_central_line_normalizer_factorization D h h611 hI d hd
  exact mul_mem (hI hc) hm.1
end CFSG.Quasithin.Chapter12.Section02.RankOneModule
