module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PositiveSixFourFactor

/-!
# Literal quotient application of the positive (6.4) factor step

The preceding theorem is stated on the same finite marked quotient as the
source equations.  This leaf applies it to the generated carrier through the
literal map `Q.q`; the two source membership premises remain visible so a
later source assembly can discharge them from the actual commutator
calculation.  No endpoint is replaced by a derived or model carrier.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits)
  (m : ℕ)
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (n : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤
    pCore 2 (Endpoint Q 1))

include μ hB ν T hC hc in
/-- The positive factor step at the literal generated quotient map. -/
theorem source_six_four_positive_factor_quotient
    (hm : rotationOrder Q = 8) (hij : (1 : Fin 2) ≠ 0)
    (hsize : (Nat.card (BinaryGaloisField n))^4 < (2^(2*m+1))^6)
    (hmpos : 0 < m)
    (z : generated L S)
    (hzD : Q.q z ∈ ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆)
    (hz : Q.q z ∈ ⁅simpleRoot Q split 1,
      rootAt Q split 0 (Q.simple 1*Q.simple 0*Q.simple 1)⁆) :
    ∃ a ∈ omegaOneAmbient (rootAt Q split 1 (Q.simple 0*Q.simple 1)),
      ∃ b ∈ rootAt Q split 0 (Q.simple 1),
        b ∈ ⁅simpleRemainder Q split 1,simpleRemainder Q split 1⁆ ∧
        a*b = Q.q z := by
  exact source_six_four_positive_factor Q split 1 0 m μ hB ν T hC
    hc hm hij hsize hmpos (Q.q z) hzD hz

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
