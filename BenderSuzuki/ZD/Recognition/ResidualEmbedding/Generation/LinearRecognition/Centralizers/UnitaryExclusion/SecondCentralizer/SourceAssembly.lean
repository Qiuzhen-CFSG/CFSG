module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.AmbientAssembly
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.TorusCentralizer
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.CosetLinearWitness
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.FixedModel

/-!
# The second distinguished centralizer in the unitary case

This assembles GLS4, Chapter 2, Lemma 13.2 from the preceding local
centralizer and shearing conclusions and the unitary alternative. The torus
is the actual subgroup B = Lᵤ ∩ D ∩ C_G(t). Its intrinsic centralizer
calculation gives C_{Lᵤ}(B) = L ⊔ B and centralization of L by B.

The odd torus action on L_(zu) supplies an additional PSL₂(2ⁿ) subgroup.
The preceding element-centralizer alternative then recognizes the
distinguished centralizer of B as an actual SU₃ or PSU₃ cover, with the
same parameter. The involution-fixed model identifies its fixed subgroup
with L, giving the intersection, normalization, and noninner action.
All three geometric premises of `AmbientAssembly` are discharged here.

The earlier-source local data and shearing remain inputs, as in the
Section 13 consumer. No second-centralizer, torus, fixed-group, or
additional linear-subgroup witness is assumed.
Source: `refs/KGroup/GLS4/Chapter2.tex`, Lemmas 12.3, 12.7 and 13.2;
Chapter 4, Lemmas 3.4(b,c) and 3.6(c,d).
-/

namespace BenderSuzuki.ZD.UnitaryExclusion
open Subgroup Theory.GroupTheory _root_.BenderSuzuki.MatrixGroups

variable {G : Type*} [Group G] [Finite G]
  {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

/-- GLS4, Chapter 2, Lemma 13.2 in the supplied unitary branch.
The canonical ambient fixed torus satisfies every clause of the original
second-centralizer interface. The local centralizer identity, additional
linear subgroup and fixed-subgroup model are constructed, not assumed. -/
public theorem secondCentralizerData_of_unitary_centralizers
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hz : z ∈ Z) (hzM : z ∈ M) (ht : t ∈ Z) (htM : t ∉ M)
    (hL : residualGenerated M z t ≠ ⊤)
    (hlocal : ResidualCentralizerLocalData Z M z t)
    (hshear : ResidualCentralizerShearing Z M t) (hn : 2 ≤ n)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (eL : residualGenerated M z t ≃* PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u) :
    Nonempty (SecondCentralizerData Z M z t u n) := by
  have hCB := ambientFixedTorus_centralizer_eq h r hz hzM ht htM hn eL hunitary huD hu
  have hBL := ambientFixedTorus_centralizes_residualGenerated
    h r hz hzM ht htM hn eL hunitary huD hu
  obtain ⟨I, ⟨eI⟩, hzI, hIB, hIv⟩ := CosetLinearWitness.coset_linear_witness
    h r hz hzM ht htM hL hn eL hshear hunitary huD hu hBL
  exact secondCentralizerData_of_ambient_geometry h r hz ht htM hlocal hn hcard eL
    hunitary huD hu hCB I eI hzI hIB hIv
    (ambientFixedTorus_fixed_model h hz ht hn eL hunitary huD hu hCB)

end BenderSuzuki.ZD.UnitaryExclusion
