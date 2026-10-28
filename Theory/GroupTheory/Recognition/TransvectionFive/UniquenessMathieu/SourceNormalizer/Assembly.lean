module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Boundary
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Column
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.Row
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessMathieu.SourceNormalizer.ThreeSpace

/-!
# Assembly of the proved Mathieu normalizer clauses

The orientation now supplies the literal column-normalizer equality, all three
marked intersection orders, and both marked normalizer intersections. This
constructor inserts those six proved conclusions into the geometry's existing
`LocalData` boundary. The 21-point rectangle now supplies row movement and
its ambient quotient classification as well. The 45-point extension is also
constructed using the literal six-point action. `LocalData.ofInvolutionData` retains only source 40.4(2)
centralizer/four-subgroup data as an explicit input. Production of those data,
and hence existence of `SourceData`, is still outstanding.

Source: Aschbacher, *Sporadic Groups* (1994), 40.3–40.5 and 41.1–41.2,
printed pp.217–221.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
open UniquenessLinear
variable {G : Type*} [Group G] [Finite G] {z : G} (F : MarkedCentralizer z)

/-- Complete the existing local boundary using the proved column and
intersection clauses. The remaining source classifications are explicit
arguments; this constructor does not assert that they have been established. -/
def LocalData.ofNormalizerClassifications
    (hcounts : MathieuFusionOrientation F)
    (hrow : ∃ g : rowNormalizer F, (g : G) * z * (g : G)⁻¹ ≠ z)
    (hplane : Nonempty (planeQuotient F ≃*
      (((Fin 3 → ZMod 2) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)) × Equiv.Perm (Fin 3))))
    (C : Subgroup (threeSpaceQuotient F)) (hC : C.Normal) (hcard : Nat.card C = 3)
    (hquot : Nonempty ((threeSpaceQuotient F ⧸ C) ≃* Equiv.Perm (Fin 6)))
    (hinvolution : ∀ t ∈ F.plane ⊓ F.threeSpace,
      SecondInvolutionClass F t → Nonempty (InvolutionCentralizerData F t)) :
    LocalData F where
  orientation := hcounts
  row_moves_point := hrow
  column_normalizer := column_normalizer_eq F hcounts
  plane_equiv := hplane
  cubicKernel := C
  cubicKernel_normal := hC
  cubicKernel_card := hcard
  cubicKernel_quotient := hquot
  row_plane_card := SourceNormalizer.row_plane_card F
  row_threeSpace_card := SourceNormalizer.row_threeSpace_card F
  planes_intersection_card := SourceNormalizer.planes_intersection_card F
  row_plane_normalizer := SourceNormalizer.row_plane_normalizer F (Or.inl hcounts)
  row_threeSpace_normalizer := SourceNormalizer.row_threeSpace_normalizer F (Or.inl hcounts)
  involution_data := hinvolution

/-- Complete the corrected local boundary from the remaining 45-point
classification. The row and 21-point rectangle conclusions are now proved
from the orientation, with no additional source premises. -/
def LocalData.ofThreeSpaceClassification
    (hcounts : MathieuFusionOrientation F)
    (C : Subgroup (threeSpaceQuotient F)) (hC : C.Normal) (hcard : Nat.card C = 3)
    (hquot : Nonempty ((threeSpaceQuotient F ⧸ C) ≃* Equiv.Perm (Fin 6)))
    (hinvolution : ∀ t ∈ F.plane ⊓ F.threeSpace,
      SecondInvolutionClass F t → Nonempty (InvolutionCentralizerData F t)) :
    LocalData F :=
  LocalData.ofNormalizerClassifications F hcounts (row_point_mover F hcounts.1)
    (oriented_plane_quotient F hcounts) C hC hcard hquot hinvolution

/-- The original marking's checked orientation gives the source data as soon
as the remaining 45-point extension and centralizer assertions are supplied.
These explicit producer obligations remain with the source construction. -/
def SourceData.ofThreeSpaceClassification
    (hfusion : F.MathieuFusion)
    (C : Subgroup (threeSpaceQuotient (orient F hfusion).marking))
    (hC : C.Normal) (hcard : Nat.card C = 3)
    (hquot : Nonempty ((threeSpaceQuotient (orient F hfusion).marking ⧸ C) ≃*
      Equiv.Perm (Fin 6)))
    (hinvolution : ∀ t ∈ (orient F hfusion).marking.plane ⊓ (orient F hfusion).marking.threeSpace,
      SecondInvolutionClass (orient F hfusion).marking t →
      Nonempty (InvolutionCentralizerData (orient F hfusion).marking t)) :
    SourceData F where
  oriented := orient F hfusion
  localData := LocalData.ofThreeSpaceClassification _ (orient F hfusion).counts
    C hC hcard hquot hinvolution

/-- All ambient normalizer classifications are now supplied by the oriented
fusion counts. Only the source 40.4(2) involution/four-subgroup data remain. -/
def LocalData.ofInvolutionData
    (hcounts : MathieuFusionOrientation F)
    (hinvolution : ∀ t ∈ F.plane ⊓ F.threeSpace,
      SecondInvolutionClass F t → Nonempty (InvolutionCentralizerData F t)) :
    LocalData F :=
  LocalData.ofThreeSpaceClassification F hcounts (threeSpaceCubicKernel F hcounts)
    inferInstance (threeSpaceCubicKernel_card F hcounts)
    ⟨threeSpaceCubicQuotientEquiv F hcounts⟩ hinvolution

/-- The original marking is oriented and all 40.5(2) normalizer clauses are
constructed. The explicit 40.4(2) producer is still required for source data. -/
def SourceData.ofInvolutionData
    (hfusion : F.MathieuFusion)
    (hinvolution : ∀ t ∈ (orient F hfusion).marking.plane ⊓ (orient F hfusion).marking.threeSpace,
      SecondInvolutionClass (orient F hfusion).marking t →
      Nonempty (InvolutionCentralizerData (orient F hfusion).marking t)) :
    SourceData F where
  oriented := orient F hfusion
  localData := LocalData.ofInvolutionData _ (orient F hfusion).counts hinvolution

end Theory.GroupTheory.TransvectionFive.UniquenessMathieu.SourceNormalizer
