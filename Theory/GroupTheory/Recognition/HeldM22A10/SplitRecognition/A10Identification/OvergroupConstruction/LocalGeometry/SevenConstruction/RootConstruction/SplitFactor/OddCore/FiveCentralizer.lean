module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.RootQuotient
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.OddCore.FiveCentralizer.CoreCalculation
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.OddCore.FiveCentralizer.LocalFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.OddCore.FiveCentralizer.Recognition

/-!
# Held's five-element centralizer: exclusion of a factor nine

The given A6 contains an element w of order five. The local product
calculation gives |C_G(mu) ∩ C_G(w)| = 20, and the marked four-group
action identifies O(C_G(w)) with <w>. The involution fusion and
centralizer exponent calculation then give quotient order twelve or
sixty, so nine does not divide |C_G(w)|.

This supplies the consequence of Held 5.3 needed for the root odd-core
identification. No root odd-core or root quotient recognition is assumed.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.3, printed p.236.
-/

open Subgroup

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.OddCore

variable {G : Type*} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)
  (L : Source.SixLocalData D e)

/-- The marked A6 supplies a five-element whose odd core is exactly its
central cyclic subgroup, conditional on the source intersection calculation. -/
public theorem exists_five_with_oddCore_of_intersections
    (h20 : ∀ w ∈ L.A, orderOf w = 5 →
      Nat.card (centralizer ({mu D e} : Set G) ⊓ FiveCentralizer.ambient w : Subgroup G) = 20) :
    ∃ w ∈ L.A, orderOf w = 5 ∧
      pPrimeCore 2 (FiveCentralizer.ambient w) = FiveCentralizer.kernel w := by
  obtain ⟨w, hwA, hw⟩ := FiveCentralizer.exists_five D e L
  exact ⟨w, hwA, hw, FiveCentralizer.oddCore_eq_kernel_of_intersection_card
    D e L w hwA hw (h20 w hwA hw)⟩

/-- Held 5.3 supplies a five-element of the marked A6 whose full ambient
centralizer has order not divisible by nine. The local intersection,
odd core and involution fusion premises are all discharged here. -/
public theorem exists_five_centralizer_not_nine [IsSimpleGroup G]
    (_hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hcentralizer : Nat.card (centralizer ({D.a10NoncentralInvolution e} : Set G)) = 2880) :
    ∃ w ∈ L.A, orderOf w = 5 ∧
      ¬ 9 ∣ Nat.card (centralizer ({w} : Set G)) := by
  obtain ⟨w, hwA, hw⟩ := FiveCentralizer.exists_five D e L
  refine ⟨w, hwA, hw, ?_⟩
  exact FiveCentralizer.not_nine_dvd_card_of_intersection_card D e L w hwA hw
    (FiveCentralizer.intersection_card D e L w hwA hcentralizer hw)
    (FiveCentralizer.firstCentralizer_pow_ten D e L w hwA hcentralizer hw)
    (FiveCentralizer.involution_isConj_first D e L w hwA hcentralizer hw)

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.OddCore
