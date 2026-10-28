module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.OrbitCounts.Tables8.Block15

/-!
# Complete row-eight and restricted row-seven pair counts

The bounded checks cover every coordinate. Canonical plane paths transfer the
literal representative ranks, and the two coordinate filters count all partners.

Source: Aschbacher–Smith A.3.12, pp.47–48; Kleidman–Wilson (1988), pp.484–510.
-/

@[expose] public section
open Janko4
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
attribute [local irreducible] modelGroup matrixA matrixB pairRank point

private theorem orbitCanonicalChecks8 (a : Fin 256) : ∀ b : Fin 256, orbitCanonical8 a b = true :=
  orbit_forall_blocks (q := 16) (fun a : Fin 256 => ∀ b : Fin 256, orbitCanonical8 a b = true) (by
    intro j
    fin_cases j
    · exact orbitCanonicalChecks8_block0
    · exact orbitCanonicalChecks8_block1
    · exact orbitCanonicalChecks8_block2
    · exact orbitCanonicalChecks8_block3
    · exact orbitCanonicalChecks8_block4
    · exact orbitCanonicalChecks8_block5
    · exact orbitCanonicalChecks8_block6
    · exact orbitCanonicalChecks8_block7
    · exact orbitCanonicalChecks8_block8
    · exact orbitCanonicalChecks8_block9
    · exact orbitCanonicalChecks8_block10
    · exact orbitCanonicalChecks8_block11
    · exact orbitCanonicalChecks8_block12
    · exact orbitCanonicalChecks8_block13
    · exact orbitCanonicalChecks8_block14
    · exact orbitCanonicalChecks8_block15
  ) a

private theorem orbitNormalChecks8 (a : Fin 256) : ∀ b : Fin 256, orbitNormal8 a b = true :=
  orbit_forall_blocks (q := 16) (fun a : Fin 256 => ∀ b : Fin 256, orbitNormal8 a b = true) (by
    intro j
    fin_cases j
    · exact orbitNormalChecks8_block0
    · exact orbitNormalChecks8_block1
    · exact orbitNormalChecks8_block2
    · exact orbitNormalChecks8_block3
    · exact orbitNormalChecks8_block4
    · exact orbitNormalChecks8_block5
    · exact orbitNormalChecks8_block6
    · exact orbitNormalChecks8_block7
    · exact orbitNormalChecks8_block8
    · exact orbitNormalChecks8_block9
    · exact orbitNormalChecks8_block10
    · exact orbitNormalChecks8_block11
    · exact orbitNormalChecks8_block12
    · exact orbitNormalChecks8_block13
    · exact orbitNormalChecks8_block14
    · exact orbitNormalChecks8_block15
  ) a

theorem orbitSteps8 (a b : Fin 256) :
    OrbitStep 8 representativeLeft8 representativeRight8 orbitValues8 orbitAction8 orbitWitness8 a b :=
  orbitStep_of_canonical_check 8 representativeLeft8 representativeRight8 orbitValues8
    orbitAction8 orbitWitness8 orbitCanonicalChecks8 a b (orbitNormalChecks8 a b)

theorem pairRank_eq_orbitRanks8 (h : RepresentativeRanks8) (a b : Fin 256) :
    pairRank (point 8 a) (point 8 b) = orbitRanks8 a b :=
  pairRank_eq_orbitTable 8 (by decide) representativeLeft8 representativeRight8
    orbitValues8 orbitAction8 orbitWitness8 orbitAction8_conjugate orbitSteps8
      (fun k => (h k).trans (representativeRank8_eq_orbitValues8 k)) a b

private theorem orbitCountsChecked8 (a : Fin 256) : orbitPartnerCount8 a = orbitExpected8 a :=
  orbit_forall_blocks (q := 16) (fun a : Fin 256 => orbitPartnerCount8 a = orbitExpected8 a) (by
    intro j
    fin_cases j
    · exact orbitCountsChecked8_block0
    · exact orbitCountsChecked8_block1
    · exact orbitCountsChecked8_block2
    · exact orbitCountsChecked8_block3
    · exact orbitCountsChecked8_block4
    · exact orbitCountsChecked8_block5
    · exact orbitCountsChecked8_block6
    · exact orbitCountsChecked8_block7
    · exact orbitCountsChecked8_block8
    · exact orbitCountsChecked8_block9
    · exact orbitCountsChecked8_block10
    · exact orbitCountsChecked8_block11
    · exact orbitCountsChecked8_block12
    · exact orbitCountsChecked8_block13
    · exact orbitCountsChecked8_block14
    · exact orbitCountsChecked8_block15
  ) a

private theorem orbitCountsChecked7 (a : Fin 128) : orbitPartnerCount7 a = orbitExpected7 a :=
  orbit_forall_blocks (q := 8) (fun a : Fin 128 => orbitPartnerCount7 a = orbitExpected7 a) (by
    intro j
    fin_cases j
    · exact orbitCountsChecked7_block0
    · exact orbitCountsChecked7_block1
    · exact orbitCountsChecked7_block2
    · exact orbitCountsChecked7_block3
    · exact orbitCountsChecked7_block4
    · exact orbitCountsChecked7_block5
    · exact orbitCountsChecked7_block6
    · exact orbitCountsChecked7_block7
  ) a

theorem orbitCount8 (a : Fin 256) :
    (Finset.univ.filter (fun b : Fin 256 => orbitRanks8 a b = 16)).card =
      expectedCount 3 a := orbitCountsChecked8 a

theorem orbitCount7 (a : Fin 128) :
    (Finset.univ.filter (fun b : Fin 128 =>
      orbitRanks8 ⟨2*a.val, by omega⟩ ⟨2*b.val, by omega⟩ = 16)).card =
      expectedCount 2 a := orbitCountsChecked7 a

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
