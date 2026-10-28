module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.OrbitCounts.Tables8.Block04

/-!
# Bounded row-eight check, left coordinates 80–95

The preceding batch is imported deliberately to bound simultaneous compilation.
Every assertion here is checked by kernel reduction of finite coordinate data.

Source: Aschbacher–Smith A.3.12, pp.47–48; Kleidman–Wilson (1988), pp.484–510.
-/

@[expose] public section
open Janko4
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
attribute [local irreducible] modelGroup matrixA matrixB pairRank point

theorem orbitCanonicalChecks8_block5 : ∀ k : Fin 16, ∀ b : Fin 256, orbitCanonical8 (⟨16*5+k.val, by omega⟩ : Fin 256) b = true := by
  simp only [orbitCanonical8_eq_fast]
  decide +kernel

theorem orbitNormalChecks8_block5 : ∀ k : Fin 16, ∀ b : Fin 256, orbitNormal8 (⟨16*5+k.val, by omega⟩ : Fin 256) b = true := by
  decide +kernel

theorem orbitCountsChecked8_block5 : ∀ k : Fin 16, orbitPartnerCount8 (⟨16*5+k.val, by omega⟩ : Fin 256) = orbitExpected8 (⟨16*5+k.val, by omega⟩ : Fin 256) := by
  decide +kernel

theorem orbitCountsChecked7_block5 : ∀ k : Fin 16, orbitPartnerCount7 (⟨16*5+k.val, by omega⟩ : Fin 128) = orbitExpected7 (⟨16*5+k.val, by omega⟩ : Fin 128) := by
  decide +kernel

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
