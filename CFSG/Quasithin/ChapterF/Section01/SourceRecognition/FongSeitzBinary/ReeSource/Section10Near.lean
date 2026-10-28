module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.PositiveNearEquality
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Section10OmegaClauses

/-!
# The complete near-root clause at the Section 10 interface

The completed near-commutator equality and the existing Omega centralizer
clause give both parts of (10.2)(ii), conjugated by every actual element
of N on the same quotient. This includes q=2 and keeps the natural panel
markings, odd linear degree and faithful Borel explicit.

Source: Fong--Seitz I (6H)(b), pp.53--54, and II (10.2)(ii), p.221.
The remaining (6H) clauses and Section 10 coordinate construction are not
asserted here; this supplies one precise premise at their literal interface.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup m : Set _))

include hn ν hC μ hB in
/-- Both parts of (10.2)(ii), for all parameters and every actual N-conjugate. -/
theorem source_ten_two_ii
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    ⁅nConj (U Q split 1) w,nConj (Uat Q split 1 (Q.simple 0*Q.simple 1)) w⁆ =
        nConj (Uat Q split 0 (Q.simple 1)) w ∧
      ⁅nConj (omega (U Q split 1)) w,nConj (Uat Q split 1 (Q.simple 0*Q.simple 1)) w⁆ = ⊥ := by
  have hnear := source_near_eq_of_odd_degree Q split n hn m ν T hC μ hB hm hcore hc
  have hw := congrArg (fun A : Subgroup (X ⧸ Q.D) => rightConjugate A (w : X ⧸ Q.D)) hnear
  have hmap (A B : Subgroup (X ⧸ Q.D)) : rightConjugate ⁅A,B⁆ (w : X ⧸ Q.D) =
      ⁅rightConjugate A (w : X ⧸ Q.D),rightConjugate B (w : X ⧸ Q.D)⁆ := by
    simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
  rw [hmap] at hw
  exact ⟨hw,source_ten_two_ii_right Q split n m ν T hC μ hB hm w⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
