module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.Section10OmegaClauses
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.BinaryTerminal

/-!
# The full binary near-root clause at the Section 10 interface

The completed binary near-commutator argument gives the whole intervening
linear root. Common-field recognition discharges its size bound from the
preceding odd-degree and faithful-Borel premises. Conjugation by each actual
element of N gives both clauses of (10.2)(ii) in exactly the Section 10
notation, on the same marked quotient.

Source: Fong--Seitz I (6H)(b), pp.53--54, and II (10.2)(ii), p.221.
This includes the full q=2 row; it does not substitute the derived Tits
group or assert the remaining (6H) or Section 10 relations.
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
  (n : ℕ) (hn : Odd n)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup 0)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom = normalizer (SuzukiRootSubgroup 0 : Set _))

include hn ν hC μ hB in
/-- Both parts of Section 10 (10.2)(ii) in the full binary row, with every actual N-conjugate. -/
theorem source_ten_two_ii_binary
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤ pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) (w : Q.tits.N) :
    ⁅nConj (U Q split 1) w,nConj (Uat Q split 1 (Q.simple 0*Q.simple 1)) w⁆ =
        nConj (Uat Q split 0 (Q.simple 1)) w ∧
      ⁅nConj (omega (U Q split 1)) w,nConj (Uat Q split 1 (Q.simple 0*Q.simple 1)) w⁆ = ⊥ := by
  let : NeZero n := ⟨hn.pos.ne'⟩
  have he := ree_common_field_exponent Q split hm n hn 0 ν T hC μ hB
    (UnitarySource.actorReflection Q split) hcore
  have hsize : Nat.card (BinaryGaloisField n) ≤ 2 := by
    rw [GaloisField.card 2 n hn.pos.ne',he]
    norm_num
  have hnear := source_binary_near_eq Q split 1 0 μ hB n hn.pos ν T hC hc hm (by decide) hsize
  have hw := congrArg (fun A : Subgroup (X ⧸ Q.D) => rightConjugate A (w : X ⧸ Q.D)) hnear
  have hmap (A B : Subgroup (X ⧸ Q.D)) : rightConjugate ⁅A,B⁆ (w : X ⧸ Q.D) =
      ⁅rightConjugate A (w : X ⧸ Q.D),rightConjugate B (w : X ⧸ Q.D)⁆ := by
    simp only [rightConjugate,comap_equiv_eq_map_symm',map_commutator]
  rw [hmap] at hw
  exact ⟨hw,source_ten_two_ii_right Q split n 0 ν T hC μ hB hm w⟩
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
