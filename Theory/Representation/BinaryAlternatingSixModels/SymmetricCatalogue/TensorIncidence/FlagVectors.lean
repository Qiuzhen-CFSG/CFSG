module

public import Theory.Representation.BinaryAlternatingSixModels.SymmetricCatalogue.Reduction

/-!
# Natural vectors attached to the two kinds of building vertices

The marked exceptional automorphism exchanges the point and line stabilizers.
Transport of the base point therefore identifies the synthemes equivariantly
with nonzero vectors in the second natural module. At the base point it reverses
incidence; transitivity transports the resulting three-vector sum relation to
every point. The corresponding relation on a syntheme holds in the first
natural module. These are the two relations needed to send a building flag to
the tensor of its endpoint vectors.

Source: the tensor realization in Aschbacher–Smith G.5.1, printed pp.342–343,
and the duad–syntheme geometry of I.5.4–9, printed pp.420–422.
-/

public section

open Theory.SpecificGroups.SymmetricSix BinaryPermutation Representation
open scoped TensorProduct
namespace BinaryAlternatingSix.SymmetricCatalogue

private noncomputable def lineTransport (s : Syntheme) : S6 := (syntheme_transitive 0 s).choose

private theorem lineTransport_spec (s : Syntheme) : synthemeAct (lineTransport s) 0 = s :=
  (syntheme_transitive 0 s).choose_spec

private noncomputable def lineToDuad (s : Syntheme) : Duad := diagramAut (lineTransport s) • 0

private theorem lineToDuad_of_transport (s : Syntheme) (g : S6)
    (hg : synthemeAct g 0 = s) : lineToDuad s = diagramAut g • 0 := by
  have hh : (lineTransport s)⁻¹ * g ∈ synthemeStabilizer := by
    rw [← syntheme_stabilizer_zero]
    change synthemeAct ((lineTransport s)⁻¹ * g) 0 = 0
    rw [synthemeAct_mul, hg]
    calc
      _ = synthemeAct (lineTransport s)⁻¹ (synthemeAct (lineTransport s) 0) :=
        congrArg _ (lineTransport_spec s).symm
      _ = 0 := by rw [← synthemeAct_mul, inv_mul_cancel, synthemeAct_one]
  have hk := (diagramAut_mem_duad _).mpr hh
  rw [← duad_stabilizer_zero] at hk
  change diagramAut ((lineTransport s)⁻¹ * g) • (0 : Duad) = 0 at hk
  rw [map_mul, map_inv, mul_smul] at hk
  exact ((inv_smul_eq_iff).mp hk).symm

private theorem lineToDuad_zero : lineToDuad 0 = 0 := by
  simpa using lineToDuad_of_transport 0 1 (synthemeAct_one 0)

private theorem lineToDuad_action (g : S6) (s : Syntheme) :
    lineToDuad (synthemeAct g s) = diagramAut g • lineToDuad s := by
  rw [lineToDuad_of_transport _ (g * lineTransport s) (by
    rw [synthemeAct_mul, lineTransport_spec]), map_mul, mul_smul]
  rfl

private theorem lineToDuad_bijective : Function.Bijective lineToDuad := by
  have hs : Function.Surjective lineToDuad := by
    intro d
    obtain ⟨g, hg⟩ := duad_transitive 0 d
    refine ⟨synthemeAct (diagramAut.symm g) 0, ?_⟩
    rw [lineToDuad_action, lineToDuad_zero, MulEquiv.apply_symm_apply, hg]
  exact ⟨(Finite.injective_iff_surjective).mpr hs, hs⟩

private theorem lineToDuad_base_incidence (s : Syntheme) :
    incident 0 s ↔ incident (lineToDuad s) 0 := by
  constructor
  · intro hs
    obtain ⟨g, hd, hl⟩ := flag_transitive 0 0 0 s (by decide) hs
    have hg : g ∈ duadStabilizer := by rw [← duad_stabilizer_zero]; exact hd
    have hh := (diagramAut_mem_syntheme g).mpr hg
    rw [← syntheme_stabilizer_zero] at hh
    change synthemeAct (diagramAut g) 0 = 0 at hh
    rw [lineToDuad_of_transport s g hl]
    simpa only [hh] using (incident_act_iff (diagramAut g) 0 0).mpr (by decide)
  · intro hs
    obtain ⟨g, hd, hl⟩ := flag_transitive 0 (lineToDuad s) 0 0 (by decide) hs
    have hg : g ∈ synthemeStabilizer := by rw [← syntheme_stabilizer_zero]; exact hl
    have hh : diagramAut.symm g ∈ duadStabilizer :=
      (diagramAut_mem_syntheme _).mp (by simpa using hg)
    rw [← duad_stabilizer_zero] at hh
    change diagramAut.symm g • (0 : Duad) = 0 at hh
    have he : synthemeAct (diagramAut.symm g) 0 = s := by
      apply lineToDuad_bijective.1
      rw [lineToDuad_action, lineToDuad_zero, MulEquiv.apply_symm_apply, hd]
    rw [← hh, ← he]
    exact (incident_act_iff (diagramAut.symm g) 0 0).mpr (by decide)

/-- The nonzero vector of the second natural module attached to a syntheme. -/
noncomputable def lineVector (s : Syntheme) : NaturalModule := (polarVector (lineToDuad s)).val

theorem lineVector_ne_zero (s : Syntheme) : lineVector s ≠ 0 :=
  (polarVector (lineToDuad s)).property

theorem lineVector_action (g : S6) (s : Syntheme) :
    lineVector (synthemeAct g s) = secondNatural g (lineVector s) := by
  change (polarVector (lineToDuad (synthemeAct g s))).val =
    polarAction (diagramAut g) (polarVector (lineToDuad s)).val
  rw [polarAction_vector, lineToDuad_action]

/-- The three point vectors on a syntheme sum to zero. -/
theorem point_line_sum (s : Syntheme) :
    (∑ d : Duad, if incident d s then (polarVector d).val else 0) = 0 := by
  fin_cases s <;> decide

private theorem line_point_sum_zero :
    (∑ s : Syntheme, if incident 0 s then lineVector s else 0) = 0 := by
  let e : Syntheme ≃ Duad := Equiv.ofBijective lineToDuad lineToDuad_bijective
  simp_rw [lineToDuad_base_incidence]
  exact (e.sum_comp (fun d => if incident d 0 then (polarVector d).val else 0)).trans
    (point_line_sum 0)

/-- The three second-natural vectors on the lines through a point sum to zero. -/
theorem line_point_sum (d : Duad) :
    (∑ s : Syntheme, if incident d s then lineVector s else 0) = 0 := by
  obtain ⟨g, rfl⟩ := duad_transitive 0 d
  rw [← Equiv.sum_comp (linePerm g) (fun s => if incident (g • (0 : Duad)) s then lineVector s else 0)]
  change (∑ s : Syntheme, if incident (g • (0 : Duad)) (synthemeAct g s)
    then lineVector (synthemeAct g s) else 0) = 0
  simp_rw [incident_act_iff, lineVector_action]
  have he (s : Syntheme) :
      (if incident 0 s then secondNatural g (lineVector s) else 0) =
      secondNatural g (if incident 0 s then lineVector s else 0) := by
    split_ifs <;> simp
  simp_rw [he]
  rw [← map_sum, line_point_sum_zero, map_zero]

end BinaryAlternatingSix.SymmetricCatalogue
