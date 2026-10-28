module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.Candidates
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Setup
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.WordCalculus

/-!
# The complete literal outside-kernel catalogue

The finite six-coordinate classification is proved in `Coordinates`. Here it
is applied to membership of the original ascending words in an arbitrary
normal elementary subgroup. The candidate comparison uses the literal lists
in `Candidates`, so no carrier or subgroup is identified by its order.

The presentation calculations in `Localization` and `WordCalculus` place
every outside-kernel normal elementary subgroup in `[core,envelope]` and
supply its word identities, normal-form coverage, and kernel membership.
The theorem `outsideCatalogue_of_card` combines these results with the
coordinate classification under the sole hypothesis that the universal
presentation has order 2^21. The parent matrix assembly discharges that order
hypothesis through its actual realization and identifies the marked kernel.

Source context: Aschbacher–Smith A.3.12, pp.47–48; the literal presentation
and untrusted discovery provenance are described in the adjacent source files.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders
open Janko4.LocalStructure.SylowNormalEights Presentation
namespace AbstractCatalogue

private theorem mem_iff_of_difference {G : Type*} [Group G] (A : Subgroup G)
    {x y : G} (h : x * y⁻¹ ∈ A) : x ∈ A ↔ y ∈ A := by
  constructor
  · intro hx
    have hh := A.mul_mem (A.inv_mem h) hx
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hh
  · intro hy
    have hh := A.mul_mem h hy
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hh

/-- Multiplication modulo the literal core gives xor closure of membership. -/
theorem sliceValue_xor_mem (c : WordCalculus) (A : Subgroup Carrier) (hcore : core ≤ A)
    (a b : Code) (ha : sliceValue a ∈ A) (hb : sliceValue b ∈ A) :
    sliceValue (codeXor a b) ∈ A :=
  (mem_iff_of_difference A (hcore (c.mul a b))).mp (A.mul_mem ha hb)

/-- The five generator displacements and exponent two provide the exact finite input. -/
theorem closedCoordinates_of_subgroup (c : WordCalculus) (A : Subgroup Carrier)
    (hcore : core ≤ A) (hn : A.Normal) (he : IsElementaryAbelian 2 A) :
    ClosedCoordinates (fun n => sliceValue n ∈ A) := by
  let _ := he
  refine ⟨?_, sliceValue_xor_mem c A hcore, ?_, ?_⟩
  · exact A.one_mem
  · intro j n hmem
    have hconj : (generator (conjugatorIndex j))⁻¹ * sliceValue n *
        generator (conjugatorIndex j) ∈ A := by
      simpa only [inv_inv] using hn.conj_mem (sliceValue n) hmem
        (generator (conjugatorIndex j))⁻¹
    exact (mem_iff_of_difference A (hcore (c.conjugate j n))).mp
      (A.mul_mem hconj (A.inv_mem hmem))
  · intro n hmem
    exact c.square n (elemPow_eq_one_of_isElementaryAbelian (sliceValue n) hmem)

/-- Every listed coordinate sum is in the actual candidate subgroup. -/
theorem candidateCodes_mem_abstractFamily (c : WordCalculus) (i : Fin 9) :
    ∀ n ∈ candidateCodes i, sliceValue n ∈ abstractFamily i :=
  codeSpan_mem (show sliceValue 0 ∈ abstractFamily i from (abstractFamily i).one_mem)
    (sliceValue_xor_mem c (abstractFamily i) (core_le_abstractFamily i))
    (candidateBasis i) (sliceValue_mem_abstractFamily i)

private theorem candidateBasis_mem_codes (i : Fin 9) (n : Code)
    (hn : n ∈ candidateBasis i) : n ∈ candidateCodes i :=
  (by decide +kernel : ∀ (i : Fin 9) (n : Code),
    n ∈ candidateBasis i → n ∈ candidateCodes i) i n hn

/-- Coordinate equality reconstructs equality of the original generated subgroups. -/
theorem eq_abstractFamily_of_coordinates (c : WordCalculus) (A : Subgroup Carrier)
    (hcore : core ≤ A) (henv : A ≤ envelope) (i : Fin 9)
    (ht : ∀ n, sliceValue n ∈ A ↔ n ∈ candidateCodes i) : A = abstractFamily i := by
  apply le_antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := c.cover x (henv hx)
    have hmem : sliceValue n ∈ A := (mem_iff_of_difference A (hcore hn)).mp hx
    exact (mem_iff_of_difference (abstractFamily i) ((core_le_abstractFamily i) hn)).mpr
      (candidateCodes_mem_abstractFamily c i n ((ht n).mp hmem))
  · apply (abstractFamily_le_iff i A).mpr
    exact ⟨hcore, fun n hn => (ht n).mpr (candidateBasis_mem_codes i n hn)⟩

/-- The other finite branch really lies in the eleven-word marked kernel. -/
theorem le_abstractKernel_of_coordinates (c : WordCalculus) (A : Subgroup Carrier)
    (hcore : core ≤ A) (henv : A ≤ envelope)
    (ht : ∀ n, sliceValue n ∈ A → kernelCode n) : A ≤ abstractKernel := by
  intro x hx
  obtain ⟨n, hn⟩ := c.cover x (henv hx)
  have hmem : sliceValue n ∈ A := (mem_iff_of_difference A (hcore hn)).mp hx
  exact (mem_iff_of_difference abstractKernel (c.core_kernel hn)).mpr (c.kernel n (ht n hmem))

/-- The complete catalogue in the specified interval, conditional only on word calculus. -/
theorem catalogue_in_interval (c : WordCalculus) (A : Subgroup Carrier)
    (hcore : core ≤ A) (henv : A ≤ envelope) (hn : A.Normal)
    (he : IsElementaryAbelian 2 A) (hout : ¬ A ≤ abstractKernel) :
    ∃ i : Fin 9, A = abstractFamily i := by
  obtain h | ⟨i, h⟩ := coordinates_classify (fun n => sliceValue n ∈ A)
    (closedCoordinates_of_subgroup c A hcore hn he)
  · exact (hout (le_abstractKernel_of_coordinates c A hcore henv h)).elim
  · exact ⟨i, eq_abstractFamily_of_coordinates c A hcore henv i h⟩

end AbstractCatalogue
open AbstractCatalogue

/-- Final abstract assembly once its two independent presentation inputs are supplied. -/
theorem outsideCatalogue_of_interval_and_calculus
    (hloc : IntervalLocalization) (c : WordCalculus) : OutsideCatalogue := by
  intro A hn he hout
  obtain ⟨hcore, henv⟩ := hloc A hn he hout
  exact catalogue_in_interval c A hcore henv hn he hout

/-- Every normal elementary two-subgroup outside the eleven-word marked kernel
is one of the nine literal candidate subgroups. The cardinality premise gives
uniqueness of ascending normal forms in the universal presentation. -/
theorem outsideCatalogue_of_card (hcard : Nat.card Carrier = 2 ^ 21) :
    OutsideCatalogue :=
  outsideCatalogue_of_interval_and_calculus
    (intervalLocalization_of_card hcard) (wordCalculus_of_card hcard)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders
