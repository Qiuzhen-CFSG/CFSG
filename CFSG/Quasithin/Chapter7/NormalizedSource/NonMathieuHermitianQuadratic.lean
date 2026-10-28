module

public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianCoordinates
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.SourceFF.TwistedExclusion.RootDimensions
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport

/-!
# The strict quadratic bound on the original Hermitian row

Descent and the original component quotient construct the source image.
Every inner involution has the computed root displacement, so the existing
Hermitian quadratic-actor argument applies there without a dimension premise.
Transport of the actual faithful action gives q > 2 on the original carrier.
This is the representation input used in the Hermitian branch of 8.2.2(1).
It does not exclude the tensor row by itself.

Source: Aschbacher–Smith, H.4.4, K.3.2.4 and 8.2.2(1),
printed pp.381, 455–456 and 714–715 (refs/quasithin.pdf).
-/

public noncomputable section
open Representation Representation.BinaryOffender Subgroup
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian
open ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
variable {A U : Type*} [Group A] [Finite A] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]
  {ρ : Representation (ZMod 2) A U} {Q : Subgroup A}

/-- The genuine family input has strict quadratic ratio on its original action. -/
theorem quadraticRatio_gt_two (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hrow : NonMathieuAssembly.HermitianRow hs) : 2 < quadraticRatio ρ := by
  obtain ⟨n, hn, d, hM⟩ := exists_source_coordinates hs hrow
  let : NeZero n := hn
  let e := sourceActionEquiv ρ Q n d hs.faithful
  have hbound := ChapterK.Linear.Tensor.quadraticRatio_gt_two_of_inner_source_dimensions
    n (sourceImage ρ Q n d) hM
    (TwistedExclusion.innerRootDimensions n (sourceImage ρ Q n d) hM)
  exact hbound.trans_le (quadraticRatio_le_of_injective_equivariant ρ
    (overgroupAction n (sourceImage ρ Q n d)) e.groupEquiv.toMonoidHom
    e.groupEquiv.injective e.linearEquiv e.intertwines)

end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian
