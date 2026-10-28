module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootGeometry
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootActions
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.Factor
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SymmetricExtension
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.Transpositions

/-!
# Assembly of Held's root geometry from its three source constructions

The root factor, its symmetric extension, and the transposition theorem give
`RootGeometry`. Containment of A6, normalization by mu-prime, and the exact
even subgroup follow from the intrinsic derived-subgroup argument in `Factor`.
`exists_rootGeometry` discharges all three constructions from the finite simple
local hypotheses and the corrected `Source.SixLocalData`. It gives the full
ambient centralizer splitting, an actual S7 equivalence, and all four marked
transpositions. The earlier conditional assembly remains available. Choosing
compatible seven-point labels is the separate `SevenMarking` construction.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemmas 5.4, 5.5 and 5.10, pp.236–238.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction

variable {G : Type*} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e)

/-- Assemble the root geometry after the actual A7 factor, S7 equivalence and
transposition theorem have been constructed. The source-theorem owner must
discharge all three premises before asserting existence from the local data. -/
public theorem exists_rootGeometry_of_factor
    (F : RootFactor D e L)
    (s : (F.W ⊔ zpowers (mu' D e) : Subgroup G) ≃* Perm (Fin 7))
    (htranspositions : ∀ x : (F.W ⊔ zpowers (mu' D e) : Subgroup G),
      (x : G) ∈ ({mu' D e, L.v * mu' D e, pi D e * mu D e * mu' D e, xi D e} : Set G) →
        (s x).IsSwap) :
    Nonempty (RootGeometry D e L) := by
  exact ⟨{
    W := F.W
    A_le := F.A_le D e L
    centralizer_root := F.centralizer_root
    root_disjoint := F.root_disjoint
    mu'_normalizes := F.mu'_normalizes D e L
    symmetricEquiv := s
    even_subgroup := F.even_subgroup D e L s
    transpositions := htranspositions
  }⟩

/-- Held 5.4, 5.5 and 5.10: construct the root-centralizer geometry from the
finite simple local hypotheses and the corrected six-point data. The A7
factor, its faithful S7 extension and the four transpositions are all proved;
no factor, recognition, actor or transposition premise remains. -/
public theorem exists_rootGeometry [Finite G] [IsSimpleGroup G]
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hcentralizer : Nat.card (centralizer
      ({D.a10NoncentralInvolution e} : Set G)) = 2880) :
    Nonempty (RootGeometry D e L) := by
  obtain ⟨F⟩ := exists_rootFactor D e L hfusion hcentralizer
  obtain ⟨s⟩ := F.exists_symmetricEquiv D e L hfusion hcentralizer
  exact exists_rootGeometry_of_factor D e L F s
    (marked_transpositions D e L F s hfusion hcentralizer)

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction
