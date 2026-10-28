module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.SeedFusion
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.KernelOrders.PureNormalizers

/-!
# Normalizers of the source four-group in J₄

A normal elementary four-group in the specified Sylow has no proper invariant
subgroup under its full normalizer in the source application. The existing
outside-kernel catalogue therefore puts it in the Mathieu kernel. If it
contains a 2B involution, the full normalizer lies in literal max1. Otherwise
the all-2A catalogue and its order force candidate 2, whose full normalizer
lies in the specified conjugate of literal max4.

This proves precisely the placement needed by the rank-one source consumer.
It does not require a cover of all maximal Sylow overgroups.

Source: Aschbacher--Smith, 15.3.43, printed p.1140; Kleidman--Wilson (1988),
pp.484--510, using the marked matrix comparisons in the imported catalogue.
-/

public section
open Subgroup Janko4 Janko4.LocalStructure.SymmetricLinear
open Janko4.OuterReduction.OddIndex
open Janko4.LocalStructure.SylowNormalEights
open CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open KernelOrders OutsideKernelOrders
open MatrixNormalizerBounds

namespace CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels.JankoFour

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB
  Janko4.Cardinality.max1Subgroup max4Subgroup

theorem normal_four_normalizer_placement (A : Subgroup Model)
    (hAS : A ≤ twoSubgroup) (hn : twoSubgroup ≤ normalizer (A : Set Model))
    (he : IsElementaryAbelian 2 A) (hi : ClosureNormalizerIrreducible A)
    (hc : Nat.card A = 4) :
    normalizer (A : Set Model) ≤
      Janko4.Cardinality.max1Subgroup Janko4.matrixA_mul_self Janko4.matrixB_pow_four ∨
    normalizer (A : Set Model) ≤
      max4Subgroup.map (MulAut.conj ThirdConjugacy.conjugator).toMonoidHom := by
  have hAK : A ≤ orderSpectrumKernel :=
    elementary_sylow_le_kernel_of_outside_certificates
      MatrixWords.pcGenerator_relations MatrixWords.pcGenerator_closure
      (outsideCatalogue_of_card (presentation_card_of_equiv
        (matrixEquivOfWords MatrixWords.pcGenerator_relations MatrixWords.pcGenerator_closure)))
      matrixKernel_eq_orderSpectrumKernel rankCertificates A hAS hn he hi
  by_cases hp : ∀ u ∈ A, ¬ IsConj u classSeed
  · right
    obtain ⟨i, rfl⟩ := pureKernelCatalogue.1 A hAK hn hp
    have hci := pureKernelCatalogue.2 i
    have hi : i = 2 := by
      fin_cases i <;> simp_all [candidateRows]
    subst i
    rw [← PureNormalizers.max4Plane_map_conjugator, ← map_equiv_normalizer_eq]
    exact map_mono (PureNormalizers.max4Plane_normalizer_lt_of_centralizer
      (PureNormalizers.max4Plane_centralizer_le_of_marking Max4EightCentralizer.marking)).le
  · left
    push Not at hp
    obtain ⟨u, hu, huc⟩ := hp
    exact normalizer_le_max1_of_seed_conjugate A hAK u hu huc

end CFSG.Quasithin.Chapter15.Section03.RankOne.SporadicModels.JankoFour
