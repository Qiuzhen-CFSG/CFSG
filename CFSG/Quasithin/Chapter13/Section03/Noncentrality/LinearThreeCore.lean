module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Quotient
public import CFSG.Quasithin.Chapter12.Section08.Setup.PointCoreMovement
public import Theory.ElementaryAbelian.Quotient

/-!
# The natural L₃(2) application of reduction 13.3.14(c)

The original point-parabolic two-core moves V₃=V. Reduction (a) therefore
forces a nontrivial two-core in the literal image of L₁ in G₁/O₂(G₁).
The movement is derived from the earlier natural marking, rather than
assumed as a further premise of the application.

Source: Aschbacher–Smith, Lemma 13.3.14(c), printed pp.891–892.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality
open Subgroup Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G]
  {K : GroupClass.{u}} {T : Sylow 2 G} {L V : Subgroup G}

/-- Reduction (c) for the original natural L₃(2) flag, using precisely
the omega-center conclusion of reduction (a). -/
theorem linearThree_star_core_ne_bot_of_reduction_a
    (h : HigherRankHypothesis K T L V 3) (F : InvariantFlag T V 3)
    (ha : conjugateSpanBy (F.Vi 3) F.H ≤
      Stellmacher.omegaOneCenterAmbient (F.H.pCoreIn 2)) :
    pCore 2 (star F.H (F.Li L 1) ((F.Li_le L 1).trans inf_le_right)) ≠ ⊥ := by
  let := h.chosen.elementary
  apply reduction_c_of_reduction_a F.H (F.Li L 1) (F.Vi 3)
    ((F.Li_le L 1).trans inf_le_right) ha
  simpa only [F.last] using F.point_core_moves_seed_of_natural h.naturalMarking

/-- The actual contrary-centrality application of reduction (c). Both the
parabolic generation and the omega-center containment are derived here. -/
theorem linearThree_star_core_ne_bot_of_plane_centralized
    (h : HigherRankHypothesis K T L V 3) (F : InvariantFlag T V 3)
    (hc : ⁅F.Vi 2, F.H.pCoreIn 2⁆ = ⊥) :
    pCore 2 (star F.H (F.Li L 1) ((F.Li_le L 1).trans inf_le_right)) ≠ ⊥ := by
  let := h.chosen.elementary
  let := IsElementaryAbelian.of_le (p := 2) (F.le_seed 2)
  have hVH : V ≤ F.H := (le_conjugateSpanBy V F.H).trans F.U_le_H
  let := IsElementaryAbelian.of_surjective (p := 2)
    (F.tildeMap V hVH) (F.tildeMap_surjective V hVH)
  have hpoint : F.Vi 1 ≠ ⊥ := by
    intro he
    have hcard := F.card 1 (by decide)
    simp [he] at hcard
  have hpointp : IsPGroup 2 (F.Vi 1) :=
    T.isPGroup'.to_le ((F.le_seed 1).trans h.chosen.le_sylow)
  have hH : F.H ∈ Chapter1.He G :=
    Chapter1.twoLocal_mem_He_of_sylow_le T (h.source.simpleQTKE.toIsQTKE.evenCharacteristic T)
      ⟨F.Vi 1, hpoint, hpointp, rfl⟩ (F.invariant 1)
  have hspan : F.Vi 3 = conjugateSpanBy (F.Vi 2) (F.Li L 1) := by
    rw [F.last]
    exact (F.seed_eq_plane_span L (by decide) h.chosen.normalizes
      (F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide))).symm
  exact linearThree_star_core_ne_bot_of_reduction_a h F
    (reduction_a (F.Vi 2) (F.Vi 3) (F.Li L 1) F.H
      ((F.le_seed 2).trans hVH)
      ((F.Li_le L 1).trans inf_le_right) hspan hH hc).2

end CFSG.Quasithin.Chapter13.Section03.Noncentrality
