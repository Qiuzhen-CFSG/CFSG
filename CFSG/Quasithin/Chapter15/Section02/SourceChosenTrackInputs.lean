module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCoreHyperplanes

/-!
# The proper core intersections at a noncommuting chosen pair

The partner-core hypothesis and plane uniqueness give the global weak-closure
bound. A conjugate of V contained in Q_H would then centralize the entire
H-span of V. Applying this also to the inverse conjugator proves that both
core intersections are proper. Plane overlap excludes a common nonidentity
point of the two endpoint planes.

This is the symmetry step on printed p.1120 of Aschbacher--Smith, using
15.2.26--27. Existence of a noncommuting pair remains a separate graph argument.
-/

public section

open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section02

open ChapterD ChapterD.UniqueFactor ChapterE

variable {G : Type*} [Group G] [Finite G]

/-- Zeroth weak closure excludes both endpoint core containments, while the
source overlap implication makes the two planes disjoint. The noncommuting
conjugator here must be supplied by the independent critical-track argument. -/
theorem source_chosen_opposite_core_escape
    (T : Sylow 2 G) {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (hm : letI := h.prepared.elementary
      moduleM (imageRepresentation M V h.prepared.normalized) = 2)
    (ha : letI := h.prepared.elementary
      moduleA (imageRepresentation M V h.prepared.normalized) = 1)
    (hcore : V ≤ twoCoreIn Mc)
    (g : G) (hmove : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ¬ V ≤ (twoCoreIn H).map (MulAut.conj g).toMonoidHom ∧
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ twoCoreIn H ∧
      ZS ⊓ ZS.map (MulAut.conj g).toMonoidHom = ⊥ := by
  have hr := source_chosen_globalR_gt_one_of_core h hg hu hcore
  obtain ⟨_, hWT, hWQ⟩ :=
    source_chosen_weakClosure_of_globalR T h H hg.outside hr hm ha
  have hoverlap := source_chosen_overlap_of_core T h hg hu (hWT.trans inf_le_right) hcore
  have hVU : V ≤ conjugateSpan H V := by
    rw [conjugateSpan_eq]
    exact le_conjugateSpanBy _ _
  have hzero (a : G) (hle : V.map (MulAut.conj a).toMonoidHom ≤ twoCoreIn H) :
      ⁅V, V.map (MulAut.conj a).toMonoidHom⁆ = ⊥ := by
    have hgen : V.map (MulAut.conj a).toMonoidHom ≤ indexedWeakClosure V (twoCoreIn H) 0 :=
      gamma_le_weakClosure ((mem_gamma_zero_iff _ _ _).mpr ⟨a, rfl, hle⟩)
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff.mp ((hgen.trans (hWQ.trans inf_le_right)).trans
        (centralizer_le hVU)))
  refine ⟨?_, fun hle => hmove (hzero g hle), ?_⟩
  · intro hle
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle
    rw [offender_map_conj_inverse] at hh
    have hc := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) (hzero g⁻¹ hh)
    have hi := offender_map_conj_inverse V g⁻¹
    simp only [inv_inv] at hi
    rw [map_commutator, hi, Subgroup.map_bot, commutator_comm] at hc
    exact hmove hc
  · by_contra hne
    apply hmove (hoverlap g ?_)
    intro he
    exact hne (bot_unique ((inf_le_inf_left ZS (map_mono hg.plane_le)).trans he.le))

end CFSG.Quasithin.Chapter15.Section02
