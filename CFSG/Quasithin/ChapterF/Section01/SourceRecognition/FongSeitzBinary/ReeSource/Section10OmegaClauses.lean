module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.SixFourSupport
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10.Input

/-!
# The proved Omega-centralizer clauses for Section 10

The source (6.3) and (6.4) arguments already establish the two right-hand
centralizer clauses in (10.2), on the literal marked quotient.  This leaf
transports them through every actual element of `N`, using the same right
conjugation as `ReeSection10.SixHRelations`.  It deliberately leaves the
unresolved whole-root commutator equalities and perpendicular-normalization
branches explicit; no presentation relation is manufactured here.

Source: Fong--Seitz I (6H), pp.52--53, and II (10.2), p.221.
-/

@[expose] public noncomputable section
open Subgroup
open scoped Pointwise MatrixGroups commutatorElement
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSection10
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (n : ℕ) (hn : Odd n) (m : ℕ)
  (ν : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hC : (quotientBorel Q 0).map ν.toMonoidHom = normalizer (T : Set _))
  (μ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q 1).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

private theorem rightConjugate_bot (w : Q.tits.N) :
    rightConjugate (⊥ : Subgroup (X ⧸ Q.D)) (w : X ⧸ Q.D) = ⊥ := by
  simp only [rightConjugate, comap_equiv_eq_map_symm', Subgroup.map_bot]

private theorem rightConjugate_commutator (A B : Subgroup (X ⧸ Q.D))
    (w : Q.tits.N) :
    rightConjugate ⁅A, B⁆ (w : X ⧸ Q.D) =
      ⁅rightConjugate A (w : X ⧸ Q.D),
        rightConjugate B (w : X ⧸ Q.D)⁆ := by
  simp only [rightConjugate, comap_equiv_eq_map_symm', map_commutator]

omit hn in
include ν hC μ hB in
/-- The first Omega-centralizer clause of (10.2), with every literal N-conjugate. -/
theorem source_ten_two_ii_right (hm : rotationOrder Q = 8)
    (w : Q.tits.N) :
    ⁅nConj (omega (U Q split 1)) w,
      nConj (Uat Q split 1 (Q.simple 0 * Q.simple 1)) w⁆ = ⊥ := by
  have h := (source_six_three Q split 1 0 m μ hB ν T hC hm (by decide)).2
  have hw := congrArg (fun A : Subgroup (X ⧸ Q.D) =>
      rightConjugate A (w : X ⧸ Q.D)) h
  rw [rightConjugate_commutator, rightConjugate_bot] at hw
  exact hw

include hn ν hC μ hB in
/-- The (6.4) Omega-centralizer clause of (10.2), with every literal N-conjugate. -/
theorem source_ten_two_iii_right
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤
      pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥)
    (w : Q.tits.N) :
    ⁅nConj (omega (U Q split 1)) w,
      nConj (Uat Q split 0 (Q.simple 1 * Q.simple 0 * Q.simple 1)) w⁆ = ⊥ := by
  have h := (source_six_four_support_of_odd_degree Q split hc hm n hn m ν T hC μ hB
    hcore).2
  have hw := congrArg (fun A : Subgroup (X ⧸ Q.D) =>
      rightConjugate A (w : X ⧸ Q.D)) h
  rw [rightConjugate_commutator, rightConjugate_bot] at hw
  exact hw

include hn ν hC μ hB in
/-- The two proved Omega clauses packaged in the order used by Section 10. -/
theorem source_ten_two_omega_right
    (hc : centralizer (pCore 2 (Endpoint Q 1) : Set (Endpoint Q 1)) ≤
      pCore 2 (Endpoint Q 1))
    (hm : rotationOrder Q = 8) (hcore : Q.tits.B.normalCore = ⊥) :
    (∀ w : Q.tits.N,
      ⁅nConj (omega (U Q split 1)) w,
        nConj (Uat Q split 1 (Q.simple 0 * Q.simple 1)) w⁆ = ⊥) ∧
    (∀ w : Q.tits.N,
      ⁅nConj (omega (U Q split 1)) w,
        nConj (Uat Q split 0 (Q.simple 1 * Q.simple 0 * Q.simple 1)) w⁆ = ⊥) := by
  exact ⟨source_ten_two_ii_right Q split n m ν T hC μ hB hm,
    source_ten_two_iii_right Q split n hn m ν T hC μ hB hc hm hcore⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
