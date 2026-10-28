module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.Preparation
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.RootComponent
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.TwoCentral
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal.SylowAction

/-!
# Five-local source calculations and their exact consumer interface

This module assembles Aschbacher, *Sporadic Groups* (1994), 47.2, printed
p.261 (PDF p.136), from the order and marked involution geometry of 47.1.
Recognition of the literal five-centralizer quotient constructs the marked
root-five family. Its component and inverter give the two-central family;
their nonfusion and the faithful five-plane action give the split Sylow
normalizer and exhaustive coverage. No five-local conclusion is an input.

`sourceConclusion_of_selectedGeometry` retains the actual component,
generation by the seed orbit, inverting conjugate, and internal complements.
The separate conjugacy and Sylow corollaries expose the two classes, order
25, elementary abelianness, self-centralization, faithful D₁₂ action and
the two three-line orbits. `fiveNormalizerTypes_of_selectedGeometry`
supplies the precise predicate consumed by the existing edge-centralizer
theorem. Its direct source application is in `FiveLocal.EdgeApplication`.

The order and selected geometry remain earlier-source inputs: their
construction is the separate 47.1 theorem, not an additional five-local
assumption or a conclusion encoded in the seed.
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal

variable {G : Type*} [Group G] [Finite G]

/-- The root-four family is one actual conjugacy class, from the marked 47.1 model. -/
theorem root_five_orbit {D : Seed G} {t : G}
    (C : InvolutionGeometry.SecondCentralizer D t) :
    ∃ E : Subgroup G, Nat.card E = 5 ∧ E ≤ involutionCentralizer t ∧
      ∀ F : Subgroup G, FiveCentralizing t F ↔
        F ∈ MulAction.orbit (ConjAct G) E := by
  have ht : 5 ^ (Nat.card (involutionCentralizer t)).factorization 5 = 5 := by
    rw [C.centralizer_card]
    decide +kernel
  obtain ⟨E, hE, hEt⟩ := exists_fiveCentralizing t ht
  exact ⟨E, hE, hEt, fiveCentralizing_iff_mem_orbit t ht E hE hEt⟩

/-- The source noncontainment M ≰ C_G(t), using X ≤ P ≤ M and the literal centralizer. -/
theorem five_centralizer_not_le_root_centralizer {D : Seed G} {t : G}
    (C : InvolutionGeometry.SecondCentralizer D t) (hG : Nat.card G = 604800)
    (P : Sylow 5 G) (E : Subgroup G) (hEP : E ≤ (P : Subgroup G)) :
    ¬ centralizer (E : Set G) ≤ involutionCentralizer t := by
  intro h
  exact sylow_not_le_card_240 hG P _ C.centralizer_card
    ((sylow_le_centralizer hG P E hEP).trans h)

/-- Conditional assembly of exactly two classes, with genuine subgroup conjugacy. -/
theorem two_conjugacy_classes_of_branches {D : Seed G} {t : G}
    (C : InvolutionGeometry.SecondCentralizer D t)
    (hB : TwoCentralFiveFamily D t) (hP : SylowFiveFamily D t) :
    ∃ A B : Subgroup G, FiveCentralizing t A ∧ FiveCentralizing D.z B ∧
      B ∉ MulAction.orbit (ConjAct G) A ∧
      ∀ E : Subgroup G, Nat.card E = 5 ↔
        E ∈ MulAction.orbit (ConjAct G) A ∨ E ∈ MulAction.orbit (ConjAct G) B := by
  obtain ⟨A, hA, hAt, hAo⟩ := root_five_orbit C
  obtain ⟨B, hBc, hBz, hBo⟩ := twoCentral_five_orbit D
  have hAf : FiveCentralizing t A := ⟨hA, t, IsConj.refl t, hAt⟩
  have hBf : FiveCentralizing D.z B := ⟨hBc, D.z, IsConj.refl D.z, hBz⟩
  refine ⟨A, B, hAf, hBf, fun h => hB.separated B ((hAo B).mpr h) hBf, ?_⟩
  intro E
  rw [← hAo E, ← hBo E]
  exact ⟨hP.coverage E, fun h => h.elim And.left And.left⟩

/-- Conditional adapter to the already proved edge-centralizer consumer. -/
theorem fiveNormalizerTypes_of_branches {D : Seed G} {t : G}
    (hA : RootFiveFamily D t) (hB : TwoCentralFiveFamily D t)
    (hP : SylowFiveFamily D t) : FiveNormalizerTypes G := by
  intro E hE
  rcases hP.coverage E hE with h | h
  · obtain ⟨W⟩ := hA E h
    exact Or.inl ⟨W.equiv⟩
  · exact Or.inr (hB.normalizer E h)

/-- All four clauses of source 47.2, conditional only on the order and marked
involution geometry from 47.1. The three five-local branches are proved here
in their dependency order, with every intermediate premise discharged. -/
theorem sourceConclusion_of_selectedGeometry {D : Seed G}
    (hG : Nat.card G = 604800) (S : InvolutionGeometry.SelectedGeometry D) :
    SourceConclusion D S.t := by
  have hA := RootComponent.rootFiveFamily_of_selectedGeometry S hG
  have hB := twoCentralFiveFamily_of_root_family hG S hA
  exact ⟨hA, hB, SylowAction.family hG S hA hB⟩

/-- The two involution-centralizing families are exactly the two distinct
ambient conjugacy classes of order-five subgroups, as asserted in 47.2(1). -/
theorem two_conjugacy_classes_of_selectedGeometry {D : Seed G}
    (hG : Nat.card G = 604800) (S : InvolutionGeometry.SelectedGeometry D) :
    ∃ A B : Subgroup G, FiveCentralizing S.t A ∧ FiveCentralizing D.z B ∧
      B ∉ MulAction.orbit (ConjAct G) A ∧
      ∀ E : Subgroup G, Nat.card E = 5 ↔
        E ∈ MulAction.orbit (ConjAct G) A ∨ E ∈ MulAction.orbit (ConjAct G) B := by
  have h := sourceConclusion_of_selectedGeometry hG S
  exact two_conjugacy_classes_of_branches S.model h.twoCentral h.sylow

/-- The exact unmarked interface needed by the edge-centralizer consumer,
now derived from the earlier 47.1 inputs rather than assumed five-local data. -/
theorem fiveNormalizerTypes_of_selectedGeometry {D : Seed G}
    (hG : Nat.card G = 604800) (S : InvolutionGeometry.SelectedGeometry D) :
    FiveNormalizerTypes G := by
  have h := sourceConclusion_of_selectedGeometry hG S
  exact fiveNormalizerTypes_of_branches h.root h.twoCentral h.sylow

/-- The Sylow-five conclusion of 47.2(4), with an actual internal D₁₂
complement and its faithful ambient conjugation action. -/
theorem sylow_structure_of_selectedGeometry {D : Seed G}
    (hG : Nat.card G = 604800) (S : InvolutionGeometry.SelectedGeometry D)
    (P : Sylow 5 G) :
    Nat.card P = 25 ∧ IsElementaryAbelian 5 P ∧
      centralizer (P : Set G) = (P : Subgroup G) ∧
      Nat.card (normalizer (P : Set G)) = 300 ∧
      ∃ W : SylowSplitWitness P, Function.Injective W.dihedralAction := by
  have h := sourceConclusion_of_selectedGeometry hG S
  obtain ⟨W⟩ := h.sylow.split P
  exact ⟨sylow_card hG P, h.twoCentral.elementary P, h.twoCentral.self_centralizing P,
    W.normalizer_card hG, W, W.dihedralAction_injective (h.twoCentral.self_centralizing P)⟩

/-- The last paragraph of 47.2 yields two actual three-line conjugation
orbits on the six order-five subgroups of each Sylow subgroup. The frame
marks the root and two-central families in the original ambient group. -/
theorem sylow_two_orbits_of_selectedGeometry {D : Seed G}
    (hG : Nat.card G = 604800) (S : InvolutionGeometry.SelectedGeometry D)
    (P : Sylow 5 G) :
    ∃ F : SylowAction.SourceFrame D S.t P, SylowAction.TwoOrbitConclusion F.frame := by
  have h := sourceConclusion_of_selectedGeometry hG S
  exact SylowAction.exists_frame_two_orbits hG S h.root h.twoCentral P

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.FiveLocal
