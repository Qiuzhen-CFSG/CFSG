module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.ParabolicTransport.Applications
public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Commutators.NaturalHead
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.NaturalNormalizer

/-!
# The source seed for the outer-involution argument

The L-conjugates of U generate S, whose order exceeds that of U, so one
conjugate is distinct. J.2.2(5) supplies its literal quotient image and
intersection with HC. The seed construction then gives a z-fused involution
of Q outside HC, and the proved parabolic transport gives one in H outside K.
All the earlier natural-section and conjugate-geometry premises are discharged.

Source: Aschbacher–Smith J.2.6, printed pp.434–435, using J.2.2(3),(5).
-/

public section

open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
open ConjugateIntersections
variable {G : Type*} [Group G] [Finite G]

/-- The centralizer of U centralizes V and hence lies in S. -/
theorem source_HC_le_S (d : LocalSetup G) : d.toTypeRuSetup.HC ≤ d.toTypeRuSetup.S := by
  have hh := (inf_le_right : d.toTypeRuSetup.HC ≤
    centralizer (d.toTypeRuSetup.U : Set G)).trans
      (centralizer_le (le_conjugateSpan d.toTypeRuSetup.H d.V))
  rwa [d.ru1.centralizer_V] at hh

/-- A nontrivial L-conjugate of U supplies a z-fused involution outside HC. -/
theorem exists_Q_seed_of_localSetup (d : LocalSetup G)
    {z : G} (hz : z ∈ d.toTypeRuSetup.Z) (hz1 : z ≠ 1) :
    ∃ x : G, x ∈ d.toTypeRuSetup.Q ∧ x ∉ d.toTypeRuSetup.HC ∧
      orderOf x = 2 ∧ IsConj x z := by
  obtain ⟨l, hl⟩ : ∃ l : d.L, conjugateU d l ≠ d.toTypeRuSetup.U := by
    by_contra! hn
    have hSU : d.toTypeRuSetup.S ≤ d.toTypeRuSetup.U := by
      rw [← conjugateSpan_eq_S d]
      exact iSup_le (fun l => (hn l).le)
    have hc := card_le_of_le hSU
    rw [d.ru1.card_S, d.ru2.card_U d.card_Z] at hc
    omega
  obtain ⟨hAH, hcard, hinter⟩ := lemma_J_2_2_five d d.dualSection d.noRankOne
    l l.property hl
  exact exists_Q_seed_of_conjugate d.toTypeRuSetup d.card_Z
    (d.center_eq.le.trans inf_le_left) hz hz1 l
    ((relativeIndex_eq_star_card d.toTypeRuSetup _ hAH).trans hcard) hinter

/-- The source outer seed, with every earlier transport and geometry premise discharged. -/
theorem exists_fused_outer_seed (d : LocalSetup G)
    {z : G} (hz : z ∈ d.toTypeRuSetup.Z) (hz1 : z ≠ 1) :
    ∃ j ∈ involutionsOutside d.toTypeRuSetup.H d.toTypeRuSetup.K, IsConj j z :=
  exists_outer_seed_of_localSetup d d.fusionNaturalHead (source_HC_le_S d)
    (exists_Q_seed_of_localSetup d hz hz1)
end CFSG.Quasithin.ChapterJ.Fusion.Outer
