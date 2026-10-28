module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.OrbitCounts.Data8
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.OrbitCounts.Actions
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.OrbitCounts.Normalization

/-!
# Row-eight finite verification definitions

A balanced numeric lookup is checked against the unchanged representative rank
list. The boolean predicates expose only finite coordinate arithmetic. Separate
bounded proof batches check them before the rank and count assembly.

Source: Aschbacher–Smith A.3.12, pp.47–48; Kleidman–Wilson (1988), pp.484–510.
-/

@[expose] public section
open Janko4
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
attribute [local irreducible] modelGroup matrixA matrixB pairRank point

def orbitValues8 (k : Fin 118) : ℕ := (if k.val < 59 then (if k.val < 29 then (if k.val < 14 then (if k.val < 7 then (if k.val < 3 then (if k.val < 1 then 20 else (if k.val < 2 then 22 else 25)) else (if k.val < 5 then 20 else (if k.val < 6 then 20 else 25))) else (if k.val < 10 then (if k.val < 8 then 20 else (if k.val < 9 then 20 else 16)) else (if k.val < 12 then 20 else (if k.val < 13 then 20 else 16)))) else (if k.val < 21 then (if k.val < 17 then 20 else (if k.val < 19 then (if k.val < 18 then 20 else 24) else (if k.val < 20 then 28 else 20))) else (if k.val < 25 then (if k.val < 23 then 20 else (if k.val < 24 then 28 else 20)) else 20))) else (if k.val < 44 then (if k.val < 36 then (if k.val < 32 then 20 else (if k.val < 34 then 20 else (if k.val < 35 then 22 else 24))) else (if k.val < 40 then (if k.val < 38 then (if k.val < 37 then 22 else 24) else (if k.val < 39 then 22 else 20)) else (if k.val < 42 then (if k.val < 41 then 16 else 20) else (if k.val < 43 then 20 else 16)))) else (if k.val < 51 then (if k.val < 47 then (if k.val < 45 then 16 else (if k.val < 46 then 28 else 25)) else (if k.val < 49 then 28 else (if k.val < 50 then 25 else 28))) else (if k.val < 55 then (if k.val < 53 then (if k.val < 52 then 24 else 20) else 24) else (if k.val < 57 then (if k.val < 56 then 24 else 20) else 24))))) else (if k.val < 88 then (if k.val < 73 then (if k.val < 66 then (if k.val < 62 then (if k.val < 60 then 24 else 28) else (if k.val < 64 then 25 else 24)) else (if k.val < 69 then (if k.val < 67 then 24 else (if k.val < 68 then 24 else 20)) else (if k.val < 71 then 20 else (if k.val < 72 then 28 else 20)))) else 20) else (if k.val < 103 then (if k.val < 95 then (if k.val < 91 then 20 else (if k.val < 93 then 20 else 16)) else (if k.val < 99 then 20 else (if k.val < 101 then (if k.val < 100 then 20 else 24) else 20))) else (if k.val < 110 then (if k.val < 106 then (if k.val < 104 then 20 else 16) else 16) else 16))))

theorem representativeRank8_eq_orbitValues8 (k : Fin 118) :
    representativeRank8 k = orbitValues8 k :=
  (by decide +kernel : ∀ k : Fin 118, representativeRank8 k = orbitValues8 k) k

def orbitRanks8 : Fin 256 → Fin 256 → ℕ := orbitTable 8 orbitValues8 orbitWitness8

def orbitCanonical8 (a b : Fin 256) : Bool :=
  orbitCanonicalCheck 8 representativeLeft8 representativeRight8 orbitValues8
    orbitAction8 orbitWitness8 a b

def orbitNormal8 (a b : Fin 256) : Bool := orbitNormalizationCheck 8 a b

def orbitExpected8 (a : Fin 256) : ℕ := expectedCount 3 a
def orbitExpected7 (a : Fin 128) : ℕ := expectedCount 2 a

def orbitPartnerCount8 (a : Fin 256) : ℕ :=
  (Finset.univ.filter (fun b : Fin 256 => orbitRanks8 a b = 16)).card

def orbitPartnerCount7 (a : Fin 128) : ℕ :=
  (Finset.univ.filter (fun b : Fin 128 =>
    orbitRanks8 ⟨2*a.val, by omega⟩ ⟨2*b.val, by omega⟩ = 16)).card

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
