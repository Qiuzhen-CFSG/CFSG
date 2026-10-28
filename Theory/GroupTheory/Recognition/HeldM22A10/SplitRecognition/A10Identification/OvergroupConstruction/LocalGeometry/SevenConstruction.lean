module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.AmbientReduction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.PairModel
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.MarkingConstruction

/-!
# Held's marked seven-point geometry over the corrected six-point data

An internal A7 factor of the full centralizer of `uv`, its symmetric
extension, and a compatible labeling yield every field of the corrected
`Source.SevenLocalData`. The parity action follows from the internal factor;
the crossing centralizer is reduced by ambient conjugations and identified
with the concrete even centralizer of two disjoint transpositions in S7.

`exists_sevenLocalData` constructs both the root geometry and its compatible
marking from the finite simple local hypotheses and the supplied corrected
six-point data. No root factor, recognition or labeling premise remains.
The earlier conditional assembly is preserved. The image of the actual
alternating subgroup is identified with A7 by `alternatingImageEquiv`.

Construction of the six-point input, including Held's choice of the
centralizer marking, belongs to the separate six-point construction. This
theorem applies to any marking for which that corrected input is supplied;
it does not assert six-point existence for every fixed marking or use either
of the obstruction theorems for the older interfaces.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, 5.3–5.11, pp.236–239.
-/

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e)

/-- All seven-point clauses, conditional on constructing the root geometry
and its compatible labeling. In particular the last field is an equivalence
for the full ambient crossing centralizer, not an intersection inside S7. -/
public theorem exists_sevenLocalData_of_rootGeometry
    (R : RootGeometry D e L) (M : SevenMarking D e L R) :
    Nonempty (Source.SevenLocalData D e L) := by
  exact ⟨{
    embedding := M.embedding
    injective := M.injective
    six_range := M.six_range
    six_even_range := M.six_even_range
    mark_mu' := M.mark_mu'
    mark_v_mu' := M.mark_v_mu'
    mark_pi_mu_mu' := M.mark_pi_mu_mu'
    mark_xi := M.mark_xi
    root_action := root_action D e L R M
    crossingEquiv := (crossingToEvenPair D e L R M).trans evenPairEquiv
  }⟩

/-- Held 5.3–5.11: extend the supplied corrected six-point geometry to a
compatibly marked S7. This includes its parity action on the root and the
equivalence of the full ambient crossing centralizer with C2 × S3. -/
public theorem exists_sevenLocalData [Finite G] [IsSimpleGroup G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hcentralizer : Nat.card (Subgroup.centralizer
      ({D.a10NoncentralInvolution e} : Set G)) = 2880) :
    Nonempty (Source.SevenLocalData D e L) := by
  obtain ⟨R⟩ := exists_rootGeometry D e L hfusion hcentralizer
  obtain ⟨M⟩ := exists_sevenMarking D e L R
  exact exists_sevenLocalData_of_rootGeometry D e L R M

/-- The actual alternating subgroup image in the constructed S7 is A7. -/
public noncomputable def alternatingImageEquiv (K : Source.SevenLocalData D e L) :
    (alternatingGroup (Fin 7)).map K.embedding ≃* alternatingGroup (Fin 7) :=
  ((alternatingGroup (Fin 7)).equivMapOfInjective K.embedding K.injective).symm

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
