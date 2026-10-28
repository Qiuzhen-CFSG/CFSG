module

public import CFSG.Quasithin.Chapter15.Section02.SourceChosenCriticalPair
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenDisplacement
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenTrackInputs
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenChiefDisplacement
public import CFSG.Quasithin.Chapter15.Section02.SourceChosenOppositeTrack

/-!
# The numerical reduction at the two endpoints of the chosen critical track

The upper displacement bound uses only the actual wreath quotient and the
rank-one image of M. A lower bound from the two faithful natural chief
actions then gives both corank-one inequalities, using the inverse of the
same conjugator for the other endpoint. Weak closure rules out corank zero.

 The graph witness and the lower chief-action bound are supplied by the
 independent source branches `SourceChosenOppositeTrack` and
 `SourceChosenChiefDisplacement`; the final wrapper below discharges those
 premises using their literal source hypotheses.

Source: Aschbacher--Smith, the terminal argument of Section 15.2,
printed p.1120, with Notation 15.2.9 on p.1110.
-/

public section

open Subgroup Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section02

open ChapterD ChapterD.UniqueFactor ChapterE

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem chosen_seed_le_span (V H : Subgroup G) : V ≤ conjugateSpan H V := by
  rw [conjugateSpan_eq]
  exact le_conjugateSpanBy _ _

/-- The two quotient bounds follow from the opposite-stabilizer containments
and the genuine two-chief-action displacement inequality. This is a conditional
numerical reduction; the graph and chief-action premises remain to be proved. -/
theorem source_chosen_corank_bounds_of_opposite_spans
    (T : Sylow 2 G) {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hr : primeRank 2 (internalActionImage M V h.prepared.normalized) ≤ 1)
    (hchief : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ H →
      2 * subgroupCorank A (A ⊓ twoCoreIn H) ≤
        subgroupCorank (conjugateSpan H V)
          (conjugateSpan H V ⊓ centralizer (A : Set G)))
    (g : G)
    (hforward : conjugateSpan H V ≤ H.map (MulAut.conj g).toMonoidHom)
    (hbackward : (conjugateSpan H V).map (MulAut.conj g).toMonoidHom ≤ H) :
    subgroupCorank V (V ⊓ (twoCoreIn H).map (MulAut.conj g).toMonoidHom) ≤ 1 ∧
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom ⊓ twoCoreIn H) ≤ 1 := by
  let := h.prepared.elementary
  have hVU := chosen_seed_le_span V H
  have hreverse : conjugateSpan H V ≤ H.map (MulAut.conj g⁻¹).toMonoidHom := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hbackward
    rwa [offender_map_conj_inverse] at hh
  have hVgH := (map_mono (f := (MulAut.conj g).toMonoidHom) hVU).trans hbackward
  have hVgiH : V.map (MulAut.conj g⁻¹).toMonoidHom ≤ H := by
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) (hVU.trans hforward)
    rwa [offender_map_conj_inverse] at hh
  have hsecond := (hchief _ (IsElementaryAbelian.map _) hVgH).trans
    (chosen_span_displacement_le_three T h hg hr g hforward)
  have hfirst := (hchief _ (IsElementaryAbelian.map _) hVgiH).trans
    (chosen_span_displacement_le_three T h hg hr g⁻¹ hreverse)
  have he : subgroupCorank V
      (V ⊓ (twoCoreIn H).map (MulAut.conj g).toMonoidHom) =
      subgroupCorank (V.map (MulAut.conj g⁻¹).toMonoidHom)
        (V.map (MulAut.conj g⁻¹).toMonoidHom ⊓ twoCoreIn H) := by
    have hback := offender_map_conj_inverse V g⁻¹
    simp only [inv_inv] at hback
    unfold subgroupCorank
    rw [← relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g⁻¹).toMonoidHom ⊓ twoCoreIn H)
      (V.map (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g).injective,
      Subgroup.map_inf _ _ _ (MulAut.conj g).injective, hback]
  rw [he]
  constructor <;> omega

/-- Applying the conditional numerical reduction to an actual opposite pair
supplies the precise pair consumed by the existing terminal contradiction. -/
theorem source_chosen_pair_of_opposite_spans
    (T : Sylow 2 G) {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hr : primeRank 2 (internalActionImage M V h.prepared.normalized) ≤ 1)
    (hchief : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ H →
      2 * subgroupCorank A (A ⊓ twoCoreIn H) ≤
        subgroupCorank (conjugateSpan H V)
          (conjugateSpan H V ⊓ centralizer (A : Set G)))
    (htrack : ∃ g : G,
      conjugateSpan H V ≤ H.map (MulAut.conj g).toMonoidHom ∧
      (conjugateSpan H V).map (MulAut.conj g).toMonoidHom ≤ H ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ∃ g : G,
      subgroupCorank V (V ⊓ (twoCoreIn H).map (MulAut.conj g).toMonoidHom) ≤ 1 ∧
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom ⊓ twoCoreIn H) ≤ 1 ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
  obtain ⟨g, hforward, hbackward, hmove⟩ := htrack
  obtain ⟨hfirst, hsecond⟩ :=
    source_chosen_corank_bounds_of_opposite_spans T h hg hr hchief g hforward hbackward
  exact ⟨g, hfirst, hsecond, hmove⟩

/-- The actual terminal pair with both independent source obligations
discharged. This is the inequality form consumed by the final Section 15.2
contradiction; the equality-one strengthening is provided below. -/
theorem source_chosen_pair_of_source_track
    (T : Sylow 2 G) {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMH : M ⊓ H = (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hr : primeRank 2 (internalActionImage M V h.prepared.normalized) ≤ 1) :
    ∃ g : G,
      subgroupCorank V (V ⊓ (twoCoreIn H).map (MulAut.conj g).toMonoidHom) ≤ 1 ∧
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom ⊓ twoCoreIn H) ≤ 1 ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
  let := h.prepared.elementary
  have hchief : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ H →
      2 * subgroupCorank A (A ⊓ twoCoreIn H) ≤
        subgroupCorank (conjugateSpan H V)
          (conjugateSpan H V ⊓ centralizer (A : Set G)) := by
    intro A hA hAH
    exact chosen_span_chief_displacement_lower T h hg hunique A hA hAH
  exact source_chosen_pair_of_opposite_spans T h hg hr hchief
    (source_chosen_opposite_spans T h hg hMH)

/-- Under the preceding core and uniqueness conclusions, neither endpoint
can have corank zero. Thus the numerical bounds are the exact source equalities. -/
theorem source_chosen_corank_one_of_core_and_opposite_spans
    (T : Sylow 2 G) {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (hm : letI := h.prepared.elementary
      moduleM (imageRepresentation M V h.prepared.normalized) = 2)
    (ha : letI := h.prepared.elementary
      moduleA (imageRepresentation M V h.prepared.normalized) = 1)
    (hcore : V ≤ twoCoreIn Mc)
    (hr : primeRank 2 (internalActionImage M V h.prepared.normalized) ≤ 1)
    (hchief : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ H →
      2 * subgroupCorank A (A ⊓ twoCoreIn H) ≤
        subgroupCorank (conjugateSpan H V)
          (conjugateSpan H V ⊓ centralizer (A : Set G)))
    (htrack : ∃ g : G,
      conjugateSpan H V ≤ H.map (MulAut.conj g).toMonoidHom ∧
      (conjugateSpan H V).map (MulAut.conj g).toMonoidHom ≤ H ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ∃ g : G,
      subgroupCorank V (V ⊓ (twoCoreIn H).map (MulAut.conj g).toMonoidHom) = 1 ∧
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom ⊓ twoCoreIn H) = 1 ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ZS ⊓ ZS.map (MulAut.conj g).toMonoidHom = ⊥ := by
  let := h.prepared.elementary
  obtain ⟨g, hfirst, hsecond, hmove⟩ :=
    source_chosen_pair_of_opposite_spans T h hg hr hchief htrack
  let : IsElementaryAbelian 2 (V.map (MulAut.conj g).toMonoidHom) :=
    IsElementaryAbelian.map _
  obtain ⟨hfirstne, hsecondne, hplanes⟩ :=
    source_chosen_opposite_core_escape T h hg hu hm ha hcore g hmove
  have hfirstpos : subgroupCorank V
      (V ⊓ (twoCoreIn H).map (MulAut.conj g).toMonoidHom) ≠ 0 := by
    intro hz
    have he := subgroup_eq_of_corank_zero inf_le_left hz
    exact hfirstne (he.symm.le.trans inf_le_right)
  have hsecondpos : subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
      (V.map (MulAut.conj g).toMonoidHom ⊓ twoCoreIn H) ≠ 0 := by
    intro hz
    have he := subgroup_eq_of_corank_zero inf_le_left hz
    exact hsecondne (he.symm.le.trans inf_le_right)
  exact ⟨g, by omega, by omega, hmove, hplanes⟩

/-- The completed critical-track pair. The residual uniqueness and
intersection identity are the preceding 15.2.1--14/15.2.8 source inputs;
the graph and chief-action obligations are discharged here by their dedicated
source constructions. -/
theorem source_chosen_corank_one_of_source_track
    (T : Sylow 2 G) {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hMH : M ⊓ H = (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (h.residual ⊔ (T : Subgroup G)) = {M})
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (hm : letI := h.prepared.elementary
      moduleM (imageRepresentation M V h.prepared.normalized) = 2)
    (ha : letI := h.prepared.elementary
      moduleA (imageRepresentation M V h.prepared.normalized) = 1)
    (hcore : V ≤ twoCoreIn Mc)
    (hr : primeRank 2 (internalActionImage M V h.prepared.normalized) ≤ 1) :
    ∃ g : G,
      subgroupCorank V (V ⊓ (twoCoreIn H).map (MulAut.conj g).toMonoidHom) = 1 ∧
      subgroupCorank (V.map (MulAut.conj g).toMonoidHom)
        (V.map (MulAut.conj g).toMonoidHom ⊓ twoCoreIn H) = 1 ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ ∧
      ZS ⊓ ZS.map (MulAut.conj g).toMonoidHom = ⊥ := by
  let := h.prepared.elementary
  have hchief : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ H →
      2 * subgroupCorank A (A ⊓ twoCoreIn H) ≤
        subgroupCorank (conjugateSpan H V)
          (conjugateSpan H V ⊓ centralizer (A : Set G)) := by
    intro A hA hAH
    exact chosen_span_chief_displacement_lower T h hg hunique A hA hAH
  have htrack : ∃ g : G,
      conjugateSpan H V ≤ H.map (MulAut.conj g).toMonoidHom ∧
      (conjugateSpan H V).map (MulAut.conj g).toMonoidHom ≤ H ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ :=
    source_chosen_opposite_spans T h hg hMH
  exact source_chosen_corank_one_of_core_and_opposite_spans T h hg hu hm ha hcore hr
    hchief htrack

/-- The actual endgame consumer, retaining only the independent graph and
chief-action obligations in addition to the preceding source inputs. -/
theorem source_chosen_contradiction_of_opposite_spans
    (T : Sylow 2 G) {M Mc V H ZS : Subgroup G}
    (h : ChosenSmallSource T M Mc V) (hg : ChosenPlaneGeometry h H ZS)
    (hu : maximalTwoLocalOvergroups (Mc ⊓ centralizer (ZS : Set G)) = {Mc})
    (hm : letI := h.prepared.elementary
      moduleM (imageRepresentation M V h.prepared.normalized) = 2)
    (ha : letI := h.prepared.elementary
      moduleA (imageRepresentation M V h.prepared.normalized) = 1)
    (hcore : V ≤ twoCoreIn Mc)
    (hTS : ∀ x ∈ (T : Subgroup G), x ^ 2 = 1 →
      x ∈ (T : Subgroup G) ⊓ centralizer (ZS : Set G))
    (hcomm : ⁅V, (T : Subgroup G) ⊓ centralizer (ZS : Set G)⁆ ≤ ZS)
    (hr : primeRank 2 (internalActionImage M V h.prepared.normalized) ≤ 1)
    (hchief : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ H →
      2 * subgroupCorank A (A ⊓ twoCoreIn H) ≤
        subgroupCorank (conjugateSpan H V)
          (conjugateSpan H V ⊓ centralizer (A : Set G)))
    (htrack : ∃ g : G,
      conjugateSpan H V ≤ H.map (MulAut.conj g).toMonoidHom ∧
      (conjugateSpan H V).map (MulAut.conj g).toMonoidHom ≤ H ∧
      ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) : False := by
  obtain ⟨g, hfirst, hsecond, hmove, _⟩ :=
    source_chosen_corank_one_of_core_and_opposite_spans T h hg hu hm ha hcore hr hchief htrack
  exact source_chosen_contradiction_of_core_and_pair T h hg hu hm ha hcore hTS hcomm
    ⟨g, hfirst.le, hsecond.le, hmove⟩

end CFSG.Quasithin.Chapter15.Section02
