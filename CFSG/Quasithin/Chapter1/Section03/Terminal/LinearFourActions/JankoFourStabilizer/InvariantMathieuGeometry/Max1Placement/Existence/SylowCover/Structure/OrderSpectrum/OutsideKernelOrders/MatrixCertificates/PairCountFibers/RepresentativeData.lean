module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.Coordinates

/-!
# Explicit targets for the pair-count rank certificates

The displayed plane representatives are the least bases in the untrusted
Sylow-orbit discovery. Their rank labels are witness targets, not assertions.
Rows 5 and 7 embed in rows 6 and 8 respectively by shifting binary coordinates.
The remaining producers must prove these ranks and the conjugation coverage.
Source context: Aschbacher–Smith A.3.12, printed pp.47–48;
Kleidman–Wilson (1988), pp.484–510. Matrix provenance is in Janko4.Model.Data.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers

/-- Witness data only; see `RepresentativeRanks6` for the proof obligation. -/
def representativeLeft6 : Fin 51 → Fin 128 :=
  ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,4,4,4,4,4,4,4,5,5,5,5,5,8,8,8,10,10,10,12,12,12,16,16,24,24,32]

/-- Witness data only; see `RepresentativeRanks6` for the proof obligation. -/
def representativeRight6 : Fin 51 → Fin 128 :=
  ![2,4,6,8,10,12,16,18,20,22,24,26,28,30,32,64,4,8,12,16,17,24,25,32,64,8,10,16,19,24,32,64,8,25,26,32,64,16,32,64,16,32,64,16,32,64,32,64,32,64,64]

/-- Witness data only; see `RepresentativeRanks6` for the proof obligation. -/
def representativeRank6 : Fin 51 → ℕ :=
  ![20,24,16,22,22,22,22,22,22,22,20,20,16,24,16,16,22,24,22,16,24,20,20,16,16,20,28,20,28,20,20,20,28,24,28,20,20,20,20,20,24,20,20,20,16,16,16,16,16,16,16]

/-- All representative ranks in the literal candidate, with no orbit claim. -/
def RepresentativeRanks6 : Prop :=
  ∀ k : Fin 51, pairRank (point (6 : Fin 9) (representativeLeft6 k))
    (point (6 : Fin 9) (representativeRight6 k)) = representativeRank6 k

/-- Witness data only; see `RepresentativeRanks8` for the proof obligation. -/
def representativeLeft8 : Fin 118 → Fin 256 :=
  ![1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,4,4,4,4,4,4,4,4,4,4,4,5,5,5,5,5,5,5,5,5,5,5,5,5,5,5,6,6,6,6,6,6,6,6,6,6,8,8,8,8,8,8,8,9,9,9,9,9,9,9,9,9,9,9,10,10,10,10,10,10,10,16,16,16,16,16,20,20,20,24,24,24,27,27,27,27,32,32,32,34,34,48,48,64]

/-- Witness data only; see `RepresentativeRanks8` for the proof obligation. -/
def representativeRight8 : Fin 118 → Fin 256 :=
  ![2,4,6,8,10,16,20,24,26,32,34,48,56,64,128,136,160,192,4,5,8,9,16,20,24,25,32,48,57,64,80,96,112,128,8,9,10,16,24,27,32,34,48,64,128,8,10,11,16,24,25,27,32,34,48,57,64,128,160,192,8,16,24,26,32,48,64,82,96,128,16,20,32,34,48,64,128,16,32,34,48,64,82,128,144,160,176,192,16,32,48,64,82,96,128,32,43,64,66,128,32,64,128,32,64,128,32,34,43,192,64,82,128,82,128,64,128,128]

/-- Witness data only; see `RepresentativeRanks8` for the proof obligation. -/
def representativeRank8 : Fin 118 → ℕ :=
  ![20,22,25,20,20,20,25,20,20,16,20,20,20,16,20,20,20,20,24,28,20,20,20,28,20,20,20,20,20,20,20,20,20,20,22,24,22,24,22,20,16,20,20,16,16,28,25,28,28,25,28,24,20,24,24,24,20,24,24,24,28,28,25,25,24,24,24,24,20,20,20,28,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,20,16,16,20,20,20,20,20,24,20,20,20,16,16,16,16,16,16,16,16,16,16,16,16,16,16]

/-- All representative ranks in the literal candidate, with no orbit claim. -/
def RepresentativeRanks8 : Prop :=
  ∀ k : Fin 118, pairRank (point (8 : Fin 9) (representativeLeft8 k))
    (point (8 : Fin 9) (representativeRight8 k)) = representativeRank8 k

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
