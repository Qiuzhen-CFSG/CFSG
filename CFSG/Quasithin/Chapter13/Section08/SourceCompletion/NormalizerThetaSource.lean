module

public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.ThetaSixSource
public import CFSG.Quasithin.Chapter13.Section07.SourceCover

/-!
# Original normalizer and theta statements in the natural A₆ setup

The source 12.2.8 calculation gives theta(M)=L on the original subgroup M,
using the central quotient already constructed in SourceCover. The genuine
12.2.2 structural input supplies TI for the original chosen module. Source
12.2.6 then identifies H∩M with N_H(V) whenever H≤N(V₁), and normalizes
V for the literal point-centralizing subgroups used in 13.3.9.

The original maximal-local hypothesis is kept separately: the raw natural
module setup does not itself assert maximality. No theta or normalizer
conclusion is an input. Full structural 12.2.2 remains with its source owner.
Source: Aschbacher--Smith, 12.2.6, 12.2.8, 13.3.9 and 13.7.3(9),
printed pp.797, 887 and 936--937.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.NaturalSetup
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ : Subgroup G}
variable (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The literal 13.7 normalizer theta, from the original maximal-local hypothesis. -/
theorem source_theta_normalizer
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X) :
    closure {x : G | x ∈ M ∧ orderOf x=3}=L := by
  rw [d.local_normalizer]
  exact h.source_theta_eq_of_central_quotient_six d.normalizes_L hA hC
    (Section07.source_central_quotient d)

theorem source_chosen_trivial_intersections
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) :
    ∀ g ∈ normalizer (L : Set G), V ⊓ V.map (MulAut.conj g).toMonoidHom=⊥ ∨
      V.map (MulAut.conj g).toMonoidHom=V :=
  h.source_chosen_TI structural d.chosen

theorem source_point_subgroup_normalizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    {v : G} (hv : v ∈ V) (hne : v ≠ 1) {Y : Subgroup G}
    (hY : Y ≤ M ⊓ centralizer ({v} : Set G)) : Y ≤ normalizer (V : Set G) := by
  apply h.source_point_normalizes_chosen structural d.chosen hv hne
  simpa only [d.local_normalizer] using hY

theorem source_line_intersection
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    {H : Subgroup G} (hH : H ≤ G₁) :
    H ⊓ M = H ⊓ normalizer (V : Set G) := by
  have hne : V₁ ≠ ⊥ := by
    intro he
    have hc := d.line_card
    rw [he, Subgroup.card_bot] at hc
    omega
  rw [d.local_normalizer]
  exact h.source_intersection_normalizer structural hA hC d.chosen hne
    (d.line_le_plane.trans (d.plane_le_seed.trans d.seed_le))
    (d.first_normalizer ▸ hH)

theorem source_theta_intersection_le
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (H : Subgroup G) :
    closure {x : G | x ∈ H ⊓ M ∧ orderOf x=3} ≤ L := by
  rw [←d.source_theta_normalizer h hA hC]
  exact Subgroup.closure_mono fun _ hx => ⟨hx.1.2,hx.2⟩

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.NaturalSetup
