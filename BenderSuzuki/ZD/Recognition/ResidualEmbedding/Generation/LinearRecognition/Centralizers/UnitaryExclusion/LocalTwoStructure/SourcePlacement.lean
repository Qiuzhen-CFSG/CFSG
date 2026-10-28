module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.Definitions
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.SourcePlacement.Foundations
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.SourcePlacement.Factors
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.SourcePlacement.Actions

/-!
# Assembly of the corrected source homocyclic placement

The source subgroup is U=N_V(A⟨u⟩), with the join formed in Subgroup G.
The proved local geometry supplies both Sylow images and the common
involution layer. The source commutator-core identity supplies U-invariance,
and T ∩ U=A gives the intersection for every constructed T₀ containing A.

The Hermitian coordinate construction supplies the two marked homocyclic
factors, and the root-group calculations supply the torus actions, including
the relative commutator-core identity. The final source theorem discharges
both inputs, constructs every field of the source placement record, and
connects it to the unchanged local consequences used by the endgame.
Generation and fixed-centralizer rigidity stay with their separate producers.

Source: GLS, Volume 4, Chapter 2, Lemma 13.4 and the following construction;
Chapter 4, Lemmas 3.4(d4–5) and 3.5(c).
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement
open Subgroup Theory.GroupTheory
universe v
variable {G : Type v} [Group G] [Finite G]
variable {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

/-- Assemble the actual source record from the two remaining independent pieces.
Both Sylow images, U-invariance, the intersection and all involution clauses
are proved here. The model construction and torus calculations remain explicit. -/
public def sourceHomocyclicLocalData_of_factors_and_actions
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hn : 2 ≤ n) (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (d : SecondCentralizerData Z M z t u n)
    (f : HomocyclicFactors Z M z t u n d) (a : TorusActionData Z M z t u n d) :
    SourceHomocyclicLocalData Z M z t u n d := by
  obtain ⟨hAL, hMA, hA, hZ⟩ := distinguishedClosure_data h r ha hz hzM ht htM hL heven
  have hAU := distinguishedClosure_le_sourceLocalU hAL hMA hA d
  have hTU := localT_inf_sourceLocalU h r ha hz hzM ht htM hL heven huD hu d e
  refine {
    sylow_T := sylow_T h.disconnected r htM huD hu hn hunitary
    sylow_V := sylow_V r hz hzM htM hn d
    U_normalizes_T := a.core_eq ▸ sourceLocalU_normalizes_commutatorCore d.torus
    torus_moves_T := a.torus_moves_T
    torus_fixes_frattini := a.torus_fixes_frattini
    pair_normalizes_U := a.pair_normalizes_U
    irreducible := a.irreducible
    U_homocyclic := f.U_homocyclic
    T₀ := f.T₀
    T₀_le := f.T₀_le
    T₀_homocyclic := f.T₀_homocyclic
    intersection := le_antisymm ((inf_le_inf f.T₀_le le_rfl).trans hTU.le)
      (le_inf f.A_le_T₀ hAU)
    T₀_involutions := ?_
    U_involutions := sourceLocalU_involutions h.disconnected r hz hzM htM d hZ }
  intro x
  have hi := localT_involutions h.disconnected r htM huD hu hZ ⟨x, f.T₀_le x.property⟩
  constructor
  · intro hx
    exact Subtype.ext (congrArg (fun y : localT Z M u => (y : G)) (hi.mp hx))
  · intro hx
    exact hi.mpr (Subtype.ext (congrArg (fun y : f.T₀ => (y : G)) hx))

/-- Apply the partial placement assembly to the unchanged local-consequences consumer.
Generation and fixed-centralizer rigidity retain their independent source producers. -/
public theorem local_consequences_of_factors_and_actions
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hn : 2 ≤ n) (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (d : SecondCentralizerData Z M z t u n)
    (f : HomocyclicFactors Z M z t u n d) (a : TorusActionData Z M z t u n d)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (hgen : centralizerClosure Z u ⊔ distinguishedCentralizer Z d.torus = ⊤)
    (hrigid : FixedCentralizerRigidity (secondInvolution d)) :
    CentralizerTwoBound Z u ∧ Nonempty (LargeAbelianData M n) :=
  local_consequences_of_generation_rigidity_and_source_placement h r hu (by omega) d
    hgen hrigid (sourceHomocyclicLocalData_of_factors_and_actions h r ha hz hzM ht htM hL
      heven huD hu hn e hunitary d f a) hcard

/-- Construct all source placement data from the original Section 13 inputs.
The two actual homocyclic isomorphisms, torus actions, relative core identity,
and quotient irreducibility are supplied by their source constructions;
neither factor nor action data is an additional hypothesis. -/
public theorem sourceHomocyclicLocalData_of_source
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hshear : ResidualCentralizerShearing Z M t)
    (hfusion : ∀ v : G, PFAppendixIII.IsInvolution v → v ∉ Z →
      ∃ w ∈ residualPairStabilizer M t, IsConj v w)
    (hn : 2 ≤ n) (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n) :
    Nonempty (SourceHomocyclicLocalData Z M z t u n d) := by
  obtain ⟨f⟩ := homocyclicFactors_of_source h r ha hz hzM ht htM hL heven
    hlocal hshear hfusion hn hcard e hunitary huD hu d
  have a := source_torusActionData h r ha hz hzM ht htM hL heven
    hlocal hshear hfusion hn hcard e hunitary huD hu d
  exact ⟨sourceHomocyclicLocalData_of_factors_and_actions h r ha hz hzM ht htM hL
    heven huD hu hn e hunitary d f a⟩

/-- Apply the completed source placement to the two unchanged endgame inputs.
Only the independent generation and fixed-centralizer rigidity premises remain
for the local-two-structure assembly owner to discharge. -/
public theorem local_consequences_of_source_and_generation_rigidity
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hshear : ResidualCentralizerShearing Z M t)
    (hfusion : ∀ v : G, PFAppendixIII.IsInvolution v → v ∉ Z →
      ∃ w ∈ residualPairStabilizer M t, IsConj v w)
    (hn : 2 ≤ n) (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n)
    (hgen : centralizerClosure Z u ⊔ distinguishedCentralizer Z d.torus = ⊤)
    (hrigid : FixedCentralizerRigidity (secondInvolution d)) :
    CentralizerTwoBound Z u ∧ Nonempty (LargeAbelianData M n) := by
  obtain ⟨hd⟩ := sourceHomocyclicLocalData_of_source h r ha hz hzM ht htM hL heven
    hlocal hshear hfusion hn hcard e hunitary huD hu d
  exact local_consequences_of_generation_rigidity_and_source_placement h r hu
    (by omega) d hgen hrigid hd hcard

end BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement
