module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.MathieuModel
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.Degree21
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.LocalSubgroups.Assembly
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.ActionConstruction.NormalizerGenerators.Action
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.PermutationClassification

/-!
# Recognition from the Mathieu involution centralizer

The actual Case II local analysis gives the ambient order 443520. The Sylow
congruence removes the order-144 three-normalizer alternative. The resulting
degree-21 character and local subgroup configuration construct the faithful
degree-22 action, whose checked permutation classification identifies the
ambient group with the Steiner-design carrier of M22.

Every intermediate character, order, subgroup, action and generator premise
is supplied by the original finite simple group and its local centralizer
data. The concrete centralizer equivalence is transported to Case II using
the proved parity-twisted model comparison.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), 1--19, Sections 2--9,
DOI 10.1016/0021-8693(68)90002-1.
-/

namespace Theory.GroupTheory.HeldM22A10
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

namespace M22Identification

/-- Janko's Case II centralizer identifies the actual ambient simple group
with M22, with all local analysis, order and action inputs discharged. -/
public theorem m22Identification_of_caseII (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) := by
  have L := localAnalysisData_of_caseII D k
  have hcard := card_eq_443520_of_localAnalysis D k L
  have hN3 : ∀ P : Sylow 3 G, Nat.card (Subgroup.normalizer (P : Set G)) = 72 :=
    fun P => sylowThreeNormalizer_card_of_order hcard P (L.normalizer_three P)
  obtain ⟨C⟩ := ActionConstruction.Degree21.nonempty_of_local_analysis D k L hcard hN3
  obtain ⟨S⟩ := ActionConstruction.LocalSubgroups.exists_localConfiguration
    D k L hcard hN3 C.element_orders
  obtain ⟨R⟩ := ActionConstruction.nonempty_permutationData_of_character_and_localConfiguration
    hcard C S
  obtain ⟨p, hp⟩ := PermutationClassification.range_conjugacy R hcard hN3
  exact ⟨equivM22OfRangeConjugacy R.rho R.faithful p hp⟩

end M22Identification

/-- Recognition from the genuine M22 involution-centralizer carrier, without
additional marking, ambient-order or permutation-action hypotheses. -/
public theorem m22Identification_of_centralizer (D : LocalData G)
    (e : D.centralizer ≃* CentralizerModels.m22Centralizer) :
    Nonempty (G ≃* Sporadic.Mathieu.M22) :=
  M22Identification.m22Identification_of_caseII D
    (twistedModelEquivM22Centralizer.trans e.symm)

end Theory.GroupTheory.HeldM22A10
