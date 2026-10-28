module

public import Theory.SpecificGroups.Rudvalis.Multiplier.TwoPrimary.LocalCoverBounds.CentralIdentities.Chunk04
import Mathlib.Tactic.Module

/-!
# The four central collection identities for Rudvalis max4

In the literal quotient F/[F,R], checked word equations give six relations
between the seven central relators. Four integral combinations give C=A,
D=A, E=AB and B²=1 for the five cycles of `CentralKernel`.
The calculation uses only centrality of the seven relators; it does not
assume presentation faithfulness, quotient finiteness or a multiplier bound.

This supplies the collection premise of `max4CoverBounds_of_presentation`.
The application, retaining only its independent faithfulness premise, is in
`CentralIdentities.Consumer`. Source: Aschbacher–Smith I.1.3(1), printed p.407,
and the literal words of `Presentation`. See `CentralIdentities/source/README.md`
for the certificate calculus, provenance and reproducibility.
-/

public section
namespace Rudvalis.Multiplier.TwoPrimary.LocalPresentation.CentralKernel
open IdentityReplay
open scoped IsMulCommutative

private theorem relation6 : collect ![-8, 0, 2, 0, 0, 0, 0] = 1 :=
  eqn_cycle Certificate.eq_6

private theorem relation268 : collect ![6, 4, -8, 0, 2, 0, 0] = 1 :=
  eqn_cycle Certificate.eq_268

private theorem relation340 : collect ![-39, -6, 3, 0, 0, 2, 0] = 1 :=
  eqn_cycle Certificate.eq_340

private theorem relation431 : collect ![22, -4, -19, -2, 4, 0, 1] = 1 :=
  eqn_cycle Certificate.eq_431

private theorem relation442 : collect ![47, -22, -11, -6, 3, 0, 0] = 1 :=
  eqn_cycle Certificate.eq_442

private theorem relation563 : collect ![-120, 16, 6, 6, 0, 4, 0] = 1 :=
  eqn_cycle Certificate.eq_563

/-- The fourth-power commutator cycle equals the square of the marked lift. -/
theorem commutatorCycle_eq_markedSquare : commutatorCycle = markedSquare := by
  have hv : (![-31, -6, 1, 0, 0, 2, 0] : Fin 7 → ℤ) =
      ![-39, -6, 3, 0, 0, 2, 0] + - ![-8, 0, 2, 0, 0, 0, 0] := by decide
  have ht : collect ![-31, -6, 1, 0, 0, 2, 0] = 1 := by
    rw [hv, collect_add, collect_neg, relation340, relation6]
    simp
  apply mul_inv_eq_one.mp
  calc
    commutatorCycle * markedSquare⁻¹ = collect ![-31, -6, 1, 0, 0, 2, 0] := by
      dsimp [commutatorCycle, markedSquare, collect]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module
    _ = 1 := ht

/-- The fifth-relator cycle also equals the square of the marked lift. -/
theorem fourthCycle_eq_markedSquare : fourthCycle = markedSquare := by
  have hv : (![-40, -4, 0, 0, 1, 2, 0] : Fin 7 → ℤ) =
      - ![6, 4, -8, 0, 2, 0, 0] + - ![-39, -6, 3, 0, 0, 2, 0] +
        ![47, -22, -11, -6, 3, 0, 0] + ![-120, 16, 6, 6, 0, 4, 0] := by decide
  have ht : collect ![-40, -4, 0, 0, 1, 2, 0] = 1 := by
    rw [hv, collect_add, collect_add, collect_add, collect_neg, collect_neg,
      relation268, relation340, relation442, relation563]
    simp
  apply mul_inv_eq_one.mp
  calc
    fourthCycle * markedSquare⁻¹ = collect ![-40, -4, 0, 0, 1, 2, 0] := by
      dsimp [fourthCycle, markedSquare, collect]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module
    _ = 1 := ht

/-- The last cycle is the product of the two remaining kernel generators. -/
theorem lastCycle_eq_markedSquare_mul_secondCycle : lastCycle = markedSquare * secondCycle := by
  have hv : (![-29, -18, 0, -2, 0, 2, 1] : Fin 7 → ℤ) =
      - ![6, 4, -8, 0, 2, 0, 0] + - ![6, 4, -8, 0, 2, 0, 0] +
        ![-39, -6, 3, 0, 0, 2, 0] + ![22, -4, -19, -2, 4, 0, 1] := by decide
  have ht : collect ![-29, -18, 0, -2, 0, 2, 1] = 1 := by
    rw [hv, collect_add, collect_add, collect_add, collect_neg,
      relation268, relation340, relation431]
    simp
  apply mul_inv_eq_one.mp
  calc
    lastCycle * (markedSquare * secondCycle)⁻¹ = collect ![-29, -18, 0, -2, 0, 2, 1] := by
      dsimp [lastCycle, markedSquare, secondCycle, collect]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
      module
    _ = 1 := ht

/-- The second kernel generator has order dividing two. -/
theorem secondCycle_sq : secondCycle ^ 2 = 1 := by
  have hv : (![-42, 28, 0, 6, 0, 0, 0] : Fin 7 → ℤ) =
      - ![-39, -6, 3, 0, 0, 2, 0] + - ![-39, -6, 3, 0, 0, 2, 0] +
        ![-120, 16, 6, 6, 0, 4, 0] := by decide
  have ht : collect ![-42, 28, 0, 6, 0, 0, 0] = 1 := by
    rw [hv, collect_add, collect_add, collect_neg, relation340, relation563]
    simp
  calc
    secondCycle ^ 2 = collect ![-42, 28, 0, 6, 0, 0, 0] := by
      dsimp [secondCycle, collect]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_pow, ofMul_zpow]
      module
    _ = 1 := ht

/-- Unconditional collection identities in the literal free central extension. -/
theorem collectionIdentities : CollectionIdentities where
  commutator_eq := commutatorCycle_eq_markedSquare
  fourth_eq := fourthCycle_eq_markedSquare
  last_eq := lastCycle_eq_markedSquare_mul_secondCycle
  second_sq := secondCycle_sq

end Rudvalis.Multiplier.TwoPrimary.LocalPresentation.CentralKernel
