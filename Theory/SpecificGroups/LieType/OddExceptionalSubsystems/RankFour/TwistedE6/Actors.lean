module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.TwistedE6.Lifts
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.Coroots

/-!
# Actual folded sign actors for the twisted E6 signed chart

On each orthogonal diagram pair, the folded three-factor Weyl word separates
into the two ordinary Weyl words. Their squares therefore give exactly the
products of native minus-one coroots. For the singleton orbits the identity
is immediate. Thus the four residual words constructed in `Lifts` have
ambient images h₀h₅, h₁h₄, h₂ and h₃, respectively.

This is the explicit residual-membership bridge for the involution and the
three coordinate detectors. The coroot identities are supplied by the shared
native `Coroots` module. Source: GLS3 §§2.3–2.4 and Aschbacher–Smith A.2.17.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem RootPairing.IntegralGeckConstruction
open TwistedE6 TwistedE6.FoldedSubsystem
namespace TwistedE6.RankFour
attribute [local instance] Classical.decEq

section Native
variable (F : Type*) [Field F]

def simpleWeyl (i : Fin 6) : splitCarrier F :=
  simpleRoot F true i 1 * simpleRoot F false i (-1) * simpleRoot F true i 1

theorem simple_cross_commute (i j : Fin 6) (hij : i ≠ j)
    (hc : typeE6CartanMatrix j i = 0) (s d : Bool) (a b : F) :
    Commute (simpleRoot F s i a) (simpleRoot F d j b) := by
  cases s <;> cases d
  · exact simpleRoot_commute F false i j hij hc _ _
  · exact (simpleRoot_opposite_commute F j i hij.symm _ _).symm
  · exact simpleRoot_opposite_commute F i j hij _ _
  · exact simpleRoot_commute F true i j hij hc _ _

theorem simpleWeyl_commute (i j : Fin 6) (hij : i ≠ j)
    (hc : typeE6CartanMatrix j i = 0) : Commute (simpleWeyl F i) (simpleWeyl F j) := by
  unfold simpleWeyl
  apply Commute.mul_left
  · apply Commute.mul_left
    · exact ((simple_cross_commute F i j hij hc true true _ _).mul_right
        (simple_cross_commute F i j hij hc true false _ _)).mul_right
          (simple_cross_commute F i j hij hc true true _ _)
    · exact ((simple_cross_commute F i j hij hc false true _ _).mul_right
        (simple_cross_commute F i j hij hc false false _ _)).mul_right
          (simple_cross_commute F i j hij hc false true _ _)
  · exact ((simple_cross_commute F i j hij hc true true _ _).mul_right
      (simple_cross_commute F i j hij hc true false _ _)).mul_right
        (simple_cross_commute F i j hij hc true true _ _)

theorem simpleWeyl_pair (i j : Fin 6) (hij : i ≠ j)
    (hc : typeE6CartanMatrix j i = 0) :
    (simpleRoot F true i 1 * simpleRoot F true j 1) *
      (simpleRoot F false i (-1) * simpleRoot F false j (-1)) *
        (simpleRoot F true i 1 * simpleRoot F true j 1) =
          simpleWeyl F i * simpleWeyl F j := by
  rw [((simple_cross_commute F i j hij hc false true _ _).symm).mul_mul_mul_comm]
  rw [(((simple_cross_commute F i j hij hc true true _ _).symm).mul_left
    (simple_cross_commute F i j hij hc true false _ _).symm).mul_mul_mul_comm]
  simp only [simpleWeyl,mul_assoc]

def nativeCoroot (i : Fin 6) : splitCarrier F :=
  ExceptionalSplit.OddRankFour.elementaryCoroot (F := F) (simpleIndex i)

theorem nativeCoroot_eq (i : Fin 6) : nativeCoroot F i = simpleWeyl F i ^ 2 := by
  apply Subtype.ext
  simp only [nativeCoroot,ExceptionalSplit.OddRankFour.elementaryCoroot,
    Subgroup.coe_pow,Subgroup.coe_mul,
    TwistedE6.FoldedSubsystem.HigherRealizations.signedSimple_val,simpleWeyl,simpleRoot_val]

theorem folded_word_square (i : Fin 4) :
    (foldedSimple F true i 1 * foldedSimple F false i (-1) * foldedSimple F true i 1)^2 =
      ![nativeCoroot F 0 * nativeCoroot F 5,nativeCoroot F 1 * nativeCoroot F 4,
        nativeCoroot F 2,nativeCoroot F 3] i := by
  have hpair (j k : Fin 6) (hne : j≠k) (hc : typeE6CartanMatrix k j=0) :
      ((simpleRoot F true j 1 * simpleRoot F true k 1) *
      (simpleRoot F false j (-1) * simpleRoot F false k (-1)) *
        (simpleRoot F true j 1 * simpleRoot F true k 1))^2 =
          nativeCoroot F j * nativeCoroot F k := by
    rw [simpleWeyl_pair F j k hne hc,(simpleWeyl_commute F j k hne hc).mul_pow,
      nativeCoroot_eq,nativeCoroot_eq]
  fin_cases i
  · exact hpair 0 5 (by decide) (by decide)
  · exact hpair 1 4 (by decide) (by decide)
  · exact (nativeCoroot_eq F 2).symm
  · exact (nativeCoroot_eq F 3).symm

end Native

variable (p : ℕ) [Fact p.Prime] (m : ℕ)

theorem foldedSignActor_coroot (i : Fin 4) :
    ambientInclusion p m (foldedSignActor p m i) =
      (![nativeCoroot (CoefficientField p m) 0 * nativeCoroot (CoefficientField p m) 5,
        nativeCoroot (CoefficientField p m) 1 * nativeCoroot (CoefficientField p m) 4,
        nativeCoroot (CoefficientField p m) 2,nativeCoroot (CoefficientField p m) 3] i).val := by
  rw [foldedSignActor_ambient,folded_word_square]

end TwistedE6.RankFour
