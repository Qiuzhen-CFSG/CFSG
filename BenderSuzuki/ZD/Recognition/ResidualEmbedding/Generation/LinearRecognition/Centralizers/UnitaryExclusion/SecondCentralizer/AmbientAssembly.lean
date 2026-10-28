module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.AmbientTorus
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.Centralizers.UnitaryExclusion.SecondCentralizer.LinearWitness

/-!
# Assembly using the actual ambient fixed torus

The torus is constructed from the literal intersection Lᵤ ∩ D ∩ C_G(t).
Its local centralizer identity implies centralization of L. A second linear
subgroup gives recognition of its distinguished centralizer, before the
fixed-group calculation is used. Thus these two independent recognition
arguments do not require each other's output as an assumption.

This is a conditional reduction of GLS4, Chapter 2, Lemma 13.2. The local
centralizer identity, second linear subgroup, and involution-fixed model
remain geometric inputs; the unconditional source assembly retains their
discharge. No torus construction, order, placement or normalization premise
remains in this reduction.
-/

noncomputable section
namespace BenderSuzuki.ZD.UnitaryExclusion
open Subgroup Theory.GroupTheory _root_.BenderSuzuki.MatrixGroups

variable {G : Type*} [Group G] [Finite G]
  {Z : Set G} {M : Subgroup G} {z t u : G} {n : ℕ}

/-- The remaining three geometric inputs suffice for the original
second-centralizer record. The fixed-group producer may assume the cover:
it is proved here from the independent linear witness before that producer
is applied. This does not assert the unconditional source lemma. -/
public theorem secondCentralizerData_of_ambient_geometry
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hz : z ∈ Z) (ht : t ∈ Z) (htM : t ∉ M)
    (hlocal : ResidualCentralizerLocalData Z M z t) (hn : 2 ≤ n)
    (hcard : Nat.card (closure (Z ∩ (M : Set G))) = 2 ^ n)
    (eL : residualGenerated M z t ≃* PSL2BinaryMatrixGroup n)
    (hunitary : ResidualUnitaryCentralizers Z M z t n)
    (huD : u ∈ residualPairStabilizer M t) (hu : PFAppendixIII.IsInvolution u)
    (hCB : centralizerClosure Z u ⊓ centralizer (ambientFixedTorus Z M t u : Set G) =
      residualGenerated M z t ⊔ ambientFixedTorus Z M t u)
    (I : Subgroup G) (eI : I ≃* PSL2BinaryMatrixGroup n) (hzI : z ∈ I)
    (hIB : I ≤ centralizer (ambientFixedTorus Z M t u : Set G))
    (hIv : I ≤ centralizer ({z * u} : Set G))
    (hfixed : IsUnitaryCentralizerCoverAt n
        (distinguishedCentralizer Z (ambientFixedTorus Z M t u)) →
      Nonempty ((distinguishedCentralizer Z (ambientFixedTorus Z M t u) ⊓
        centralizer ({u} : Set G) : Subgroup G) ≃* PSL2BinaryMatrixGroup n)) :
    Nonempty (SecondCentralizerData Z M z t u n) := by
  let B := ambientFixedTorus Z M t u
  obtain ⟨hcyclic, hBcard, _, hB⟩ :=
    ambientFixedTorus_properties h r ht htM hn hunitary huD hu
  have hBL : B ≤ centralizer (residualGenerated M z t : Set G) := by
    intro b hb x hx
    have hxC : x ∈ centralizer (B : Set G) :=
      (show x ∈ centralizerClosure Z u ⊓ centralizer (B : Set G) from
        hCB.symm ▸ (show x ∈ residualGenerated M z t ⊔ B from mem_sup_left hx)).2
    exact (mem_centralizer_iff.mp hxC b hb).symm
  have huL : u ∈ centralizer (residualGenerated M z t : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mp
      (centralizerClosure_le Z u ((hunitary u huD hu).1.le hx))
  have hcover := (second_cover_of_distinguished_linear_witness h hz hlocal hn hcard eL
    B hcyclic hB hBL huL I eI hzI hIB hIv).2
  obtain ⟨efixed⟩ := hfixed hcover
  exact secondCentralizerData_of_linear_and_fixed_models h hz hlocal hn hcard eL
    hunitary huD hu B hcyclic hB hBcard ambientFixedTorus_placement.1
    ambientFixedTorus_placement.2.1 hBL hCB I eI hzI hIB hIv efixed

end BenderSuzuki.ZD.UnitaryExclusion
