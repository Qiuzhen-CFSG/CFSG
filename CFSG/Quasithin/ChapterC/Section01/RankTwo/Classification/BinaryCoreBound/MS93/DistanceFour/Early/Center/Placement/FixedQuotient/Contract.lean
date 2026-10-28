module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.ModuleSection

/-!
# The finite local calculation used by the source assembly

This is the precise lemma contract, proved in `FixedQuotient.Calculation`.
The actor J has order-four image in the same marked SL3(2) quotient as the
split natural section. Its full relative normalizer preserves E, which is
fixed modulo N and has nonzero intersection with the moving quotient.
The conclusion identifies the literal quotient-fixed preimage.

The source adapter discharges all group-specific premises. The calculation
uses the normalizer action on fixed vectors of the marked natural factor
and lifts through its actual coordinate homomorphism.
Source: MS93 (1993), (4.6.7), printed p.904, with the convention on p.881.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement

/-- A universal finite-group calculation on the literal split natural section,
proved by `naturalFixedCalculation` in `FixedQuotient.Calculation`. -/
def NaturalFixedCalculation (A : Type*) [Group A] : Prop :=
  ∀ (π : A →* SL) (Q T H N E J : Subgroup A)
    (s : Escape.SingleNaturalSection π Q T H N),
    T ⊔ Q = ⊤ → ⁅H, Q⁆ ≤ N → Q ≤ J → Nat.card (J.map π) = 4 →
    N ≤ E → E ≤ H → ⁅E, J⁆ ≤ N →
    normalizer (J : Set A) ≤ normalizer (E : Set A) →
    (¬ E ⊓ (N ⊔ ⁅H, T⁆) ≤ N) →
    letI := s.normal_kernel
    centralizerModulo H J N = (E ⊓ ⁅H, T⁆) ⊔ centralizerModulo H ⊤ N

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Placement
