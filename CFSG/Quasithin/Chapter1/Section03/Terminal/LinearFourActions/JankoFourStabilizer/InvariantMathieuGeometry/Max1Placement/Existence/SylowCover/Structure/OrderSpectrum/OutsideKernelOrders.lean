module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.Candidates
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates

/-!
# Excluding outside-kernel closures by their actual matrix action

An exhaustive catalogue of normal elementary subgroups in the specified
Sylow presentation reduces the outside-kernel branch to nine literal matrix
subgroups. In each candidate a rank fiber, or a fiber of a rank-pair count,
generates a proper nontrivial subgroup. Simultaneous matrix conjugation
preserves these fibers, contradicting full-normalizer irreducibility.

The transport uses the genuine presentation realization and a separate
identification of its marked kernel with the literal Mathieu kernel. Its
consistency premise is discharged from that realization. No ambient
simplicity, maximal-subgroup classification, or matching-order recognition is
used. The checked catalogue and matrix certificates discharge all finite
inputs. The resulting containment in the Mathieu kernel proves that the
outside-kernel branch is empty; maximality and the small-order bound are
unnecessary for this stronger conclusion.

The unconditional theorem `smallOutsideKernelClosureOrders` has exactly the
type consumed by `centralClosureOrderSpectrum_of_small_branches`. The
conditional transport interfaces remain available separately.

Source context: Aschbacher–Smith A.3.12 and its sporadic Sylow-overgroup
argument, printed pp.47–48; Kleidman–Wilson (1988), pp.484–510. The additional
matrix invariants supply a direct alternative to the ambient normalizer table.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
open Janko4 Subgroup Janko4.LocalStructure.SylowNormalEights
open Janko4.OuterReduction.OddIndex
open OutsideKernelOrders
attribute [local irreducible] modelGroup matrixA matrixB

/-- Cardinal certificates turn the normalizer-invariant rank span into an obstruction. -/
theorem outside_matrixFamily_not_irreducible (hcert : RankCertificates) (i : Fin 9) :
    ¬ ClosureNormalizerIrreducible (matrixFamily i) := by
  intro hi
  obtain ⟨hcard, hspan⟩ := hcert i
  obtain ⟨hpos, hlt⟩ := candidateSpanOrder_bounds i
  rcases hi _ (rankSpan_le _ _) (normalizer_le_rankSpan_normalizer _ _) with hb | he
  · have hc : Nat.card (rankSpan (matrixFamily i) (candidateTest i)) = 1 := by
      rw [hb, card_bot]
    omega
  · rw [he, hcard] at hspan
    omega

/-- Exhaustive abstract coverage transports to the actual subgroups through the literal realization. -/
theorem outside_matrixFamily_coverage
    (hr : Presentation.Relations MatrixWords.pcGenerator)
    (hg : closure (Set.range MatrixWords.pcGenerator) = ⊤)
    (hcover : OutsideCatalogue)
    (hk : matrixKernel = orderSpectrumKernel)
    (A : Subgroup Model) (hAS : A ≤ twoSubgroup)
    (hn : twoSubgroup ≤ normalizer (A : Set Model))
    (he : IsElementaryAbelian 2 A) (hout : ¬ A ≤ orderSpectrumKernel) :
    ∃ i : Fin 9, A = matrixFamily i := by
  let e := matrixEquivOfWords hr hg
  let H := A.subgroupOf twoSubgroup
  have hH : H.Normal := (normal_subgroupOf_iff_le_normalizer hAS).mpr hn
  let := hH
  let := he
  have hHe : IsElementaryAbelian 2 H := IsElementaryAbelian.subgroupOf hAS
  let := hHe
  let B := H.map e.symm.toMonoidHom
  have hB : B.Normal := Normal.map hH e.symm.toMonoidHom e.symm.surjective
  have hBe : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBH : B.map e.toMonoidHom = H := by
    simp [B, map_map]
  have hBA : B.map (ambientRealization hr hg) = A := by
    rw [ambientRealization, ← map_map]
    change (B.map e.toMonoidHom).map twoSubgroup.subtype = A
    rw [hBH, map_subgroupOf_eq_of_le hAS]
  have hBK : ¬ B ≤ abstractKernel := by
    intro h
    apply hout
    rw [← hBA, ← hk, ← map_abstractKernel hr hg]
    exact map_mono h
  obtain ⟨i, hi⟩ := hcover B hB hBe hBK
  refine ⟨i, hBA.symm.trans ?_⟩
  rw [hi, map_abstractFamily]

/-- Once the finite inputs are certified, every irreducible normal elementary Sylow subgroup
is in the Mathieu kernel. This does not require a maximal normalizer or an order bound. -/
theorem elementary_sylow_le_kernel_of_outside_certificates
    (hr : Presentation.Relations MatrixWords.pcGenerator)
    (hg : closure (Set.range MatrixWords.pcGenerator) = ⊤)
    (hcover : OutsideCatalogue)
    (hk : matrixKernel = orderSpectrumKernel) (hcert : RankCertificates)
    (A : Subgroup Model) (hAS : A ≤ twoSubgroup)
    (hn : twoSubgroup ≤ normalizer (A : Set Model))
    (he : IsElementaryAbelian 2 A) (hi : ClosureNormalizerIrreducible A) :
    A ≤ orderSpectrumKernel := by
  by_contra hout
  obtain ⟨i, rfl⟩ := outside_matrixFamily_coverage hr hg hcover hk A hAS hn he hout
  exact outside_matrixFamily_not_irreducible hcert i hi

/-- Application to the literal fixed-Sylow closure, with presentation consistency discharged. -/
theorem fixedSylowClosure_le_kernel_of_outside_certificates
    (hr : Presentation.Relations MatrixWords.pcGenerator)
    (hg : closure (Set.range MatrixWords.pcGenerator) = ⊤)
    (hcover : Nat.card Presentation.Carrier = 2 ^ 21 → OutsideCatalogue)
    (hk : matrixKernel = orderSpectrumKernel) (hcert : RankCertificates)
    (A : Subgroup Model) (hA : FixedSylowClosure A) : A ≤ orderSpectrumKernel :=
  elementary_sylow_le_kernel_of_outside_certificates hr hg
    (hcover (presentation_card_of_equiv (matrixEquivOfWords hr hg))) hk hcert
    A hA.le_sylow hA.sylow_normalizes hA.elementary hA.irreducible

/-- Exact consumer type for the independent outside-kernel branch.
All finite proof obligations remain explicit until their producers are supplied. -/
theorem smallOutsideKernelClosureOrders_of_presentation_certificates
    (hr : Presentation.Relations MatrixWords.pcGenerator)
    (hg : closure (Set.range MatrixWords.pcGenerator) = ⊤)
    (hcover : Nat.card Presentation.Carrier = 2 ^ 21 → OutsideCatalogue)
    (hk : matrixKernel = orderSpectrumKernel) (hcert : RankCertificates) :
    SmallOutsideKernelClosureOrders := by
  intro A hA hout _
  exact (hout (fixedSylowClosure_le_kernel_of_outside_certificates
    hr hg hcover hk hcert A hA)).elim

/-- Every fixed-Sylow closure lies in the literal Mathieu kernel: each of the
nine outside candidates has a proper nontrivial full-normalizer invariant span.
The actual matrix realization discharges the presentation's cardinal premise. -/
theorem fixedSylowClosure_le_kernel (A : Subgroup Model) (hA : FixedSylowClosure A) :
    A ≤ orderSpectrumKernel :=
  fixedSylowClosure_le_kernel_of_outside_certificates
    MatrixWords.pcGenerator_relations MatrixWords.pcGenerator_closure
    outsideCatalogue_of_card matrixKernel_eq_orderSpectrumKernel rankCertificates A hA

/-- The independent outside-kernel branch for the central-closure order spectrum,
with all catalogue, realization, kernel and rank-span premises discharged. -/
theorem smallOutsideKernelClosureOrders : SmallOutsideKernelClosureOrders := by
  intro A hA hout _
  exact (hout (fixedSylowClosure_le_kernel A hA)).elim

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover
