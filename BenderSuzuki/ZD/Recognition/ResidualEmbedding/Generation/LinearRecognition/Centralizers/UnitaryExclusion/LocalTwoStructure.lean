module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.Inputs
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.Centralizer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.Abelian
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.Source
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.Generation
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.FixedAutomorphisms
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.LocalTwoStructure.SourcePlacement

/-!
# Local two-subgroup assembly for the unitary exclusion

Generation by the two distinguished centralizers makes the actual centralizer
action faithful. Intrinsic automorphism rigidity then gives the centralizer
Sylow bound. The coprime A×B and Frattini arguments make the specified
homocyclic subgroups commute; their square map gives the exact product rank
and order. These are precisely the two inputs consumed by the endgame.

The source assembly discharges generation, fixed-centralizer rigidity and
homocyclic placement from the original local hypotheses. Only the authorized
second-centralizer witness from Lemma 13.2 remains explicit. The construction
uses the subgroup-join normalizer in `Source` and the actual homocyclic
factors from `SourcePlacement`. The older conditional set-union interface
and its diagnostic statements remain preserved.
Source: GLS, volume 4, Chapter 2, Lemmas 13.3–13.4 and the next paragraph.
-/

namespace BenderSuzuki.ZD.UnitaryExclusion
open Subgroup
universe u
variable {G : Type u} [Group G] [Finite G]
variable {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

/-- The two actual endgame inputs, conditional on their remaining source
generation, intrinsic automorphism and local-placement prerequisites. -/
public theorem local_consequences_of_generation_rigidity_and_placement
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (hu : PFAppendixIII.IsInvolution u) (hn : 0 < n)
    (d : SecondCentralizerData Z M z t u n)
    (hgen : centralizerClosure Z u ⊔ distinguishedCentralizer Z d.torus = ⊤)
    (hrigid : FixedCentralizerRigidity (secondInvolution d))
    (hd : HomocyclicLocalData Z M z t u n d)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n) :
    CentralizerTwoBound Z u ∧ Nonempty (LargeAbelianData M n) :=
  ⟨(centralizer_sylow_and_bound_of_generation_and_rigidity h r hu d hgen hrigid).2,
    ⟨largeAbelianData_of_homocyclicLocalData hn d hd hcard⟩⟩

/-- Lemma 13.3 for the actual ambient centralizer. Generation proves that
its action on the second centralizer is faithful, and intrinsic rigidity
gives both the Sylow witness and the bound for every two-subgroup. -/
public theorem centralizer_sylow_and_bound_of_source
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (heven : Even (Nat.card (residualPairStabilizer M t)))
    (hn : 2 ≤ n) (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (d : SecondCentralizerData Z M z t u n) :
    (∃ S : Sylow 2 (centralizer (centralizerClosure Z u : Set G)),
      (S : Subgroup (centralizer (centralizerClosure Z u : Set G))).map
        (centralizer (centralizerClosure Z u : Set G)).subtype = zpowers u) ∧
      CentralizerTwoBound Z u :=
  centralizer_sylow_and_bound_of_generation_and_rigidity h r hu d
    (two_distinguished_centralizers_generate h r ha hz hzM ht htM hL heven
      hn hcard hunitary huD hu d)
    (secondInvolution_fixedCentralizerRigidity hn hu d)

/-- The local consequences of Lemmas 13.3–13.4 and the following construction,
with only the Lemma 13.2 witness explicit. The source placement constructs
T₀ and U, the coprime/Frattini argument proves [T,U]=1, and their actual join
in M supplies the abelian two-group of rank 2*n and order (2^n)^3. -/
public theorem local_consequences_of_source
    (h : MinimalCounterexample Z M) (r : SimpleReduction Z M)
    (ha : ResidualAction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
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
    CentralizerTwoBound Z u ∧ Nonempty (LargeAbelianData M n) := by
  obtain ⟨hd⟩ := SourcePlacement.sourceHomocyclicLocalData_of_source h r ha hz hzM ht htM
    hL heven hlocal hshear hfusion hn hcard e hunitary huD hu d
  exact ⟨(centralizer_sylow_and_bound_of_source h r ha hz hzM ht htM hL heven
      hn hcard hunitary huD hu d).2,
    ⟨largeAbelianData_of_sourceHomocyclicLocalData (by omega) d hd hcard⟩⟩

end BenderSuzuki.ZD.UnitaryExclusion
