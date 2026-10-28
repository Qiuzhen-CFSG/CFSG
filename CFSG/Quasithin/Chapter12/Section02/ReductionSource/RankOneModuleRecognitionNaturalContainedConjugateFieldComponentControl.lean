module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldComponentControl
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometry

/-!
# Solvable centralizer overgroups on the original Chapter 12 layer

At the Sylow arranged by the complete field geometry, the original global
rank equality and both weak-closure bounds discharge E.3.19. Every solvable
subgroup of C_G(U) containing C_P(U) therefore lies in N_G(L). This is the
source premise used to exclude an escaping solvable radical in 6.1.14(5).
The local-component identification remains with the contained-branch owner.

Source: Aschbacher–Smith, 6.1.14(5), printed p.671.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G} {n : ℕ}

/-- Solvable containment at any Sylow carrying the proved field geometry. -/
theorem source_field_solvable_overgroup_le
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hn : 2 < n) (P : Sylow 2 G)
    (hg : FieldFixedSpaceGeometry L (normalizer (L : Set G)) (commutatorLayer T L) U n P)
    (X : Subgroup G) [Group.IsSolvable X]
    (hXC : X ≤ centralizer (U : Set G))
    (hRX : (P : Subgroup G) ⊓ centralizer (U : Set G) ≤ X) :
    X ≤ normalizer (L : Set G) := by
  let : IsElementaryAbelian 2 (commutatorLayer T L) := h611.layer_elementary
  have hE := source_natural_layer_hypothesisE61 D h h611 hnatural
  have hs := (source_natural_layer_rank_bounds D h h611 hnatural).2.2
  have hUB : U ≤ commutatorLayer T L := by
    obtain ⟨_, _, _, he, _⟩ := hg.field_actor
    exact he.le.trans inf_le_left
  have hBC : commutatorLayer T L ≤ centralizer (U : Set G) :=
    (commutatorLayer T L).le_centralizer.trans (centralizer_le hUB)
  have hSyl : Chapter1.IsSylowIn 2
      ((P : Subgroup G) ⊓ centralizer (U : Set G)) (centralizer (U : Set G)) :=
    hg.centralizer_sylow
  obtain ⟨S, hS⟩ := hSyl.restrict hRX hXC
  apply field_solvable_overgroup_le hE
    (field_sylow_kernel P _ hg.normalizes_module) (le_inf hg.module_le hBC)
    (inf_le_inf_left _ (centralizer_le hUB))
    (P.isPGroup'.to_le inf_le_left) hg.weak_zero ((hg.weak_one hn).trans inf_le_right)
    (S := S) (hS := hS)
  rw [hs]
  exact ENat.natCast_lt_natCast.mpr (by omega)

/-- The full geometry and the solvable-containment step are produced together
from the original source inputs, with no local callback. -/
theorem source_field_geometry_and_solvable_control
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n) (hUne : U ≠ ⊥) (hn : 2 < n) :
    ∃ P : Sylow 2 G,
      FieldFixedSpaceGeometry L (normalizer (L : Set G)) (commutatorLayer T L) U n P ∧
      ∀ X : Subgroup G, Group.IsSolvable X → X ≤ centralizer (U : Set G) →
        (P : Subgroup G) ⊓ centralizer (U : Set G) ≤ X → X ≤ normalizer (L : Set G) := by
  obtain ⟨P, hg⟩ := source_field_fixedSpace_geometry D h h611 hnatural hfield hUne hn
  refine ⟨P, hg, ?_⟩
  intro X hsol hXC hRX
  let := hsol
  exact source_field_solvable_overgroup_le D h h611 hnatural hn P hg X hXC hRX

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
