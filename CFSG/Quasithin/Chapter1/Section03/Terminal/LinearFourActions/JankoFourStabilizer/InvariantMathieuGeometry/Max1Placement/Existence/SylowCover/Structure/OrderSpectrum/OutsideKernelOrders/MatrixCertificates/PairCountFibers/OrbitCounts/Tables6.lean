module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.OrbitCounts.Data6
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.OrbitCounts.Actions
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.OrbitCounts.Normalization

/-!
# Checked plane coverage and partner counts

Every independent pair is reduced, by actual conjugation steps and plane basis
changes, to a specified representative. Numeric counts run through the full
coordinate domain, with dependent pairs assigned zero. Restricting both inputs
to even coordinates also counts the literal index-two candidate.
Source: Aschbacher–Smith A.3.12, pp.47–48; Kleidman–Wilson (1988), pp.484–510.
-/

@[expose] public section
open Janko4
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
attribute [local irreducible] modelGroup matrixA matrixB pairRank point

/-- Complete proposed ranks; the following finite checks certify their routes. -/
def orbitRanks6 : Fin 128 → Fin 128 → ℕ :=
  orbitTable 6 representativeRank6 orbitWitness6

private def orbitCanonical6 (a b : Fin 128) : Bool :=
  orbitCanonicalCheck 6 representativeLeft6 representativeRight6 representativeRank6
    orbitAction6 orbitWitness6 a b

private def orbitNormal6 (a b : Fin 128) : Bool := orbitNormalizationCheck 6 a b

private theorem orbitCanonicalChecks6_block0 : ∀ k : Fin 16, ∀ b : Fin 128, orbitCanonical6 (⟨16*0+k.val, by omega⟩ : Fin 128) b = true := by
  decide +kernel

private theorem orbitCanonicalChecks6_block1 : ∀ k : Fin 16, ∀ b : Fin 128, orbitCanonical6 (⟨16*1+k.val, by omega⟩ : Fin 128) b = true := by
  decide +kernel

private theorem orbitCanonicalChecks6_block2 : ∀ k : Fin 16, ∀ b : Fin 128, orbitCanonical6 (⟨16*2+k.val, by omega⟩ : Fin 128) b = true := by
  decide +kernel

private theorem orbitCanonicalChecks6_block3 : ∀ k : Fin 16, ∀ b : Fin 128, orbitCanonical6 (⟨16*3+k.val, by omega⟩ : Fin 128) b = true := by
  decide +kernel

private theorem orbitCanonicalChecks6_block4 : ∀ k : Fin 16, ∀ b : Fin 128, orbitCanonical6 (⟨16*4+k.val, by omega⟩ : Fin 128) b = true := by
  decide +kernel

private theorem orbitCanonicalChecks6_block5 : ∀ k : Fin 16, ∀ b : Fin 128, orbitCanonical6 (⟨16*5+k.val, by omega⟩ : Fin 128) b = true := by
  decide +kernel

private theorem orbitCanonicalChecks6_block6 : ∀ k : Fin 16, ∀ b : Fin 128, orbitCanonical6 (⟨16*6+k.val, by omega⟩ : Fin 128) b = true := by
  decide +kernel

private theorem orbitCanonicalChecks6_block7 : ∀ k : Fin 16, ∀ b : Fin 128, orbitCanonical6 (⟨16*7+k.val, by omega⟩ : Fin 128) b = true := by
  decide +kernel

private theorem orbitCanonicalChecks6 (a : Fin 128) : ∀ b : Fin 128, orbitCanonical6 a b = true :=
  orbit_forall_blocks (q := 8) (fun a : Fin 128 => ∀ b : Fin 128, orbitCanonical6 a b = true) (by
    intro j
    fin_cases j
    · exact orbitCanonicalChecks6_block0
    · exact orbitCanonicalChecks6_block1
    · exact orbitCanonicalChecks6_block2
    · exact orbitCanonicalChecks6_block3
    · exact orbitCanonicalChecks6_block4
    · exact orbitCanonicalChecks6_block5
    · exact orbitCanonicalChecks6_block6
    · exact orbitCanonicalChecks6_block7
  ) a

private theorem orbitNormalChecks6_block0 : ∀ k : Fin 16, ∀ b : Fin 128, orbitNormal6 (⟨16*0+k.val, by omega⟩ : Fin 128) b = true := by
  decide +kernel

private theorem orbitNormalChecks6_block1 : ∀ k : Fin 16, ∀ b : Fin 128, orbitNormal6 (⟨16*1+k.val, by omega⟩ : Fin 128) b = true := by
  decide +kernel

private theorem orbitNormalChecks6_block2 : ∀ k : Fin 16, ∀ b : Fin 128, orbitNormal6 (⟨16*2+k.val, by omega⟩ : Fin 128) b = true := by
  decide +kernel

private theorem orbitNormalChecks6_block3 : ∀ k : Fin 16, ∀ b : Fin 128, orbitNormal6 (⟨16*3+k.val, by omega⟩ : Fin 128) b = true := by
  decide +kernel

private theorem orbitNormalChecks6_block4 : ∀ k : Fin 16, ∀ b : Fin 128, orbitNormal6 (⟨16*4+k.val, by omega⟩ : Fin 128) b = true := by
  decide +kernel

private theorem orbitNormalChecks6_block5 : ∀ k : Fin 16, ∀ b : Fin 128, orbitNormal6 (⟨16*5+k.val, by omega⟩ : Fin 128) b = true := by
  decide +kernel

private theorem orbitNormalChecks6_block6 : ∀ k : Fin 16, ∀ b : Fin 128, orbitNormal6 (⟨16*6+k.val, by omega⟩ : Fin 128) b = true := by
  decide +kernel

private theorem orbitNormalChecks6_block7 : ∀ k : Fin 16, ∀ b : Fin 128, orbitNormal6 (⟨16*7+k.val, by omega⟩ : Fin 128) b = true := by
  decide +kernel

private theorem orbitNormalChecks6 (a : Fin 128) : ∀ b : Fin 128, orbitNormal6 a b = true :=
  orbit_forall_blocks (q := 8) (fun a : Fin 128 => ∀ b : Fin 128, orbitNormal6 a b = true) (by
    intro j
    fin_cases j
    · exact orbitNormalChecks6_block0
    · exact orbitNormalChecks6_block1
    · exact orbitNormalChecks6_block2
    · exact orbitNormalChecks6_block3
    · exact orbitNormalChecks6_block4
    · exact orbitNormalChecks6_block5
    · exact orbitNormalChecks6_block6
    · exact orbitNormalChecks6_block7
  ) a

/-- Every ordered pair is covered by a checked plane path. -/
theorem orbitSteps6 (a b : Fin 128) :
    OrbitStep 6 representativeLeft6 representativeRight6 representativeRank6
      orbitAction6 orbitWitness6 a b :=
  orbitStep_of_canonical_check 6 representativeLeft6 representativeRight6 representativeRank6
    orbitAction6 orbitWitness6 orbitCanonicalChecks6 a b (orbitNormalChecks6 a b)

/-- Only the literal representative ranks remain as hypotheses. -/
theorem pairRank_eq_orbitRanks6 (h : RepresentativeRanks6) (a b : Fin 128) :
    pairRank (point 6 a) (point 6 b) = orbitRanks6 a b :=
  pairRank_eq_orbitTable 6 (by decide) representativeLeft6 representativeRight6
    representativeRank6 orbitAction6 orbitWitness6 orbitAction6_conjugate orbitSteps6 h a b

private def orbitExpected6 (a : Fin 128) : ℕ := expectedCount 1 a
private def orbitExpected5 (a : Fin 64) : ℕ := expectedCount 0 a

private def orbitPartnerCount6 (a : Fin 128) : ℕ :=
  (Finset.univ.filter (fun b : Fin 128 => orbitRanks6 a b = 16)).card

private def orbitPartnerCount5 (a : Fin 64) : ℕ :=
  (Finset.univ.filter (fun b : Fin 64 =>
    orbitRanks6 ⟨2*a.val, by omega⟩ ⟨2*b.val, by omega⟩ = 16)).card

private theorem orbitCountsChecked6_block0 : ∀ k : Fin 16, orbitPartnerCount6 (⟨16*0+k.val, by omega⟩ : Fin 128) = orbitExpected6 (⟨16*0+k.val, by omega⟩ : Fin 128) := by
  decide +kernel

private theorem orbitCountsChecked6_block1 : ∀ k : Fin 16, orbitPartnerCount6 (⟨16*1+k.val, by omega⟩ : Fin 128) = orbitExpected6 (⟨16*1+k.val, by omega⟩ : Fin 128) := by
  decide +kernel

private theorem orbitCountsChecked6_block2 : ∀ k : Fin 16, orbitPartnerCount6 (⟨16*2+k.val, by omega⟩ : Fin 128) = orbitExpected6 (⟨16*2+k.val, by omega⟩ : Fin 128) := by
  decide +kernel

private theorem orbitCountsChecked6_block3 : ∀ k : Fin 16, orbitPartnerCount6 (⟨16*3+k.val, by omega⟩ : Fin 128) = orbitExpected6 (⟨16*3+k.val, by omega⟩ : Fin 128) := by
  decide +kernel

private theorem orbitCountsChecked6_block4 : ∀ k : Fin 16, orbitPartnerCount6 (⟨16*4+k.val, by omega⟩ : Fin 128) = orbitExpected6 (⟨16*4+k.val, by omega⟩ : Fin 128) := by
  decide +kernel

private theorem orbitCountsChecked6_block5 : ∀ k : Fin 16, orbitPartnerCount6 (⟨16*5+k.val, by omega⟩ : Fin 128) = orbitExpected6 (⟨16*5+k.val, by omega⟩ : Fin 128) := by
  decide +kernel

private theorem orbitCountsChecked6_block6 : ∀ k : Fin 16, orbitPartnerCount6 (⟨16*6+k.val, by omega⟩ : Fin 128) = orbitExpected6 (⟨16*6+k.val, by omega⟩ : Fin 128) := by
  decide +kernel

private theorem orbitCountsChecked6_block7 : ∀ k : Fin 16, orbitPartnerCount6 (⟨16*7+k.val, by omega⟩ : Fin 128) = orbitExpected6 (⟨16*7+k.val, by omega⟩ : Fin 128) := by
  decide +kernel

private theorem orbitCountsChecked6 (a : Fin 128) : orbitPartnerCount6 a = orbitExpected6 a :=
  orbit_forall_blocks (q := 8) (fun a : Fin 128 => orbitPartnerCount6 a = orbitExpected6 a) (by
    intro j
    fin_cases j
    · exact orbitCountsChecked6_block0
    · exact orbitCountsChecked6_block1
    · exact orbitCountsChecked6_block2
    · exact orbitCountsChecked6_block3
    · exact orbitCountsChecked6_block4
    · exact orbitCountsChecked6_block5
    · exact orbitCountsChecked6_block6
    · exact orbitCountsChecked6_block7
  ) a

private theorem orbitCountsChecked5_block0 : ∀ k : Fin 16, orbitPartnerCount5 (⟨16*0+k.val, by omega⟩ : Fin 64) = orbitExpected5 (⟨16*0+k.val, by omega⟩ : Fin 64) := by
  decide +kernel

private theorem orbitCountsChecked5_block1 : ∀ k : Fin 16, orbitPartnerCount5 (⟨16*1+k.val, by omega⟩ : Fin 64) = orbitExpected5 (⟨16*1+k.val, by omega⟩ : Fin 64) := by
  decide +kernel

private theorem orbitCountsChecked5_block2 : ∀ k : Fin 16, orbitPartnerCount5 (⟨16*2+k.val, by omega⟩ : Fin 64) = orbitExpected5 (⟨16*2+k.val, by omega⟩ : Fin 64) := by
  decide +kernel

private theorem orbitCountsChecked5_block3 : ∀ k : Fin 16, orbitPartnerCount5 (⟨16*3+k.val, by omega⟩ : Fin 64) = orbitExpected5 (⟨16*3+k.val, by omega⟩ : Fin 64) := by
  decide +kernel

private theorem orbitCountsChecked5 (a : Fin 64) : orbitPartnerCount5 a = orbitExpected5 a :=
  orbit_forall_blocks (q := 4) (fun a : Fin 64 => orbitPartnerCount5 a = orbitExpected5 a) (by
    intro j
    fin_cases j
    · exact orbitCountsChecked5_block0
    · exact orbitCountsChecked5_block1
    · exact orbitCountsChecked5_block2
    · exact orbitCountsChecked5_block3
  ) a

/-- The complete partner count in the larger candidate, including identity. -/
theorem orbitCount6 (a : Fin 128) :
    (Finset.univ.filter (fun b : Fin 128 => orbitRanks6 a b = 16)).card =
      expectedCount 1 a := orbitCountsChecked6 a

/-- Restriction of both coordinates along the literal smaller-row inclusion. -/
theorem orbitCount5 (a : Fin 64) :
    (Finset.univ.filter (fun b : Fin 64 =>
      orbitRanks6 ⟨2*a.val, by omega⟩ ⟨2*b.val, by omega⟩ = 16)).card =
      expectedCount 0 a := orbitCountsChecked5 a

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
