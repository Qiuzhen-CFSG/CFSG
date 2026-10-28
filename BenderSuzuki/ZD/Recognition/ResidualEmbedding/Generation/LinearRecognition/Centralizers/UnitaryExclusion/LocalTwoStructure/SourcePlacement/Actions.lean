module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.SourcePlacement.Actions.RelativeCore
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.SourcePlacement.Actions.FixedTorus
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.SourcePlacement.Actions.RootQuotient

/-!+# Assembly of the source torus actions from the remaining root calculations

The relative core and pair-normalization arguments are proved in `RelativeCore`.
The intrinsic root calculations remain explicit: identify Φ(T) with A, show
that T centralizes A and that [B,T]=T, and prove the full two-point torus's
irreducibility on T/Φ(T). These are outstanding mathematical premises, not
asserted consequences of the source hypotheses. The assembly below derives
all other fields of `TorusActionData` from them and the original local setup.

Source: GLS, Volume 4, Chapter 2, Lemma 13.4; Chapter 4, Lemma 3.5(c).
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement
open Subgroup Theory.GroupTheory
universe v
variable {G : Type v} [Group G] [Finite G]
variable {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

/-- Conditional assembly of the actual source actions. The intrinsic root
calculations are still explicit and must be discharged by the source producer. -/
public theorem torusActionData_of_root_calculations
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hn : 2 ≤ n) (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n)
    (hPhi : (frattini (localT Z M u)).map (localT Z M u).subtype =
      closure (Z ∩ (M : Set G)))
    (hTA : localT Z M u ≤ centralizer (closure (Z ∩ (M : Set G)) : Set G))
    (hBT : ⁅d.torus, localT Z M u⁆ = localT Z M u)
    (hirreducible : ∀ W : Subgroup G, W ≤ localT Z M u →
      residualPairStabilizer M t ⊓ centralizerClosure Z u ≤ normalizer (W : Set G) →
      W ≤ (frattini (localT Z M u)).map (localT Z M u).subtype ∨
        W ⊔ (frattini (localT Z M u)).map (localT Z M u).subtype = localT Z M u) :
    TorusActionData Z M z t u n d := by
  obtain ⟨hAL, hMA, hA, _⟩ := distinguishedClosure_data h r ha hz hzM ht htM hL heven
  refine {
    core_eq := commutatorCore_eq_of_torus_generation h.disconnected r hz hzM htM
      hAL hn hunitary huD hu d hTA hBT
    torus_moves_T := ?_
    torus_fixes_frattini := ?_
    pair_normalizes_U := localPair_normalizes_sourceLocalU h r ha hz hzM ht htM hL
      heven hn hunitary huD hu d
    irreducible := hirreducible }
  · rw [Subgroup.commutator_comm, hBT]
    exact localT_ne_bot h.disconnected hz hzM hAL hMA hA d
  · rw [hPhi]
    exact le_centralizer_iff.mpr (d.torus_centralizes.trans (centralizer_le hAL))

end BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement

namespace BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement
open Subgroup Theory.GroupTheory
universe v
variable {G : Type v} [Group G] [Finite G]
variable {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

/-! The complete source application of the two independent unitary calculations. -/

/-- The source torus action data under the full hypotheses of GLS, Chapter 2,
Lemma 13.4. The Frattini-layer, quotient-irreducibility, and fixed-torus
calculations are discharged by their literal source-subgroup applications. -/
public theorem source_torusActionData
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M) (hz : z ∈ Z) (hzM : z ∈ M)
    (ht : t ∈ Z) (htM : t ∉ M) (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hshear : ResidualCentralizerShearing Z M t)
    (hfusion : ∀ v : G, PFAppendixIII.IsInvolution v → v ∉ Z →
      ∃ w ∈ residualPairStabilizer M t, IsConj v w)
    (hn : 2 ≤ n)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (e : residualGenerated M z t ≃* MatrixGroups.PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t)
    (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n) :
    TorusActionData Z M z t u n d := by
  obtain ⟨hPhi, hTA, hirreducible⟩ := rootQuotient_source h r ha hz hzM ht htM hL
    heven hlocal hshear hfusion hn hcard e hunitary huD hu d
  exact torusActionData_of_root_calculations h r ha hz hzM ht htM hL heven hn
    hunitary huD hu d hPhi hTA
    (source_fixedTorus_commutator_eq h r ha hz hzM ht htM hL heven hn hunitary
      huD hu d e hPhi)
    hirreducible

end BenderSuzuki.ZD.UnitaryExclusion.SourcePlacement
