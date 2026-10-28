module
public import Theory.GroupTheory.IndependentInvolutionsRank
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.RankFour.Coroots
public import Theory.SpecificGroups.LieType.ExceptionalSplit.RootFaithfulness
/-!
# An elementary eight in every odd-characteristic F4 carrier

Three native minus-one coroots commute and act independently on the simple
root elements at nodes 1,3,2. Each root witness has odd prime order, so these
three projective involutions are independent. No order formula or subsystem
identification is needed.
Source: GLS3 §2.6; Aschbacher--Smith A.2.12, printed p.36.
-/
public noncomputable section
namespace Theory.SpecificGroups.LieType.TwoRank.F4Odd
open ExceptionalSplit ExceptionalSplit.OddRankFour
open Theory.AlgebraicGroup.StandardRootSystem
local instance : Fintype typeF4Roots := Fintype.ofFinite _
attribute [local instance] Classical.decEq
variable (F : Type*) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]
private def node : Fin 3 → Fin 4 := ![0,2,3]
private def witnessNode : Fin 3 → Fin 4 := ![1,3,2]
private def d (i : Fin 3) : ExceptionalSplit.F4 F := projection _ _ F
  (elementaryCoroot (F := F) (typeF4RootPairing_baseEquiv (node i)))
private def x (i : Fin 3) : ExceptionalSplit.F4 F := rootElement typeF4RootPairing typeF4RootPairing_base F
  (typeF4RootPairing_baseEquiv (witnessNode i)) 1
omit [Finite F] in
private theorem act (i j : Fin 3) :
    MulAut.conj (d F i) (x F j) = if i=j then (x F j)⁻¹ else x F j := by
  have h := elementaryCoroot_conjugate_root (F := F)
    (typeF4RootPairing_baseEquiv (node i))
    (typeF4RootPairing_baseEquiv (witnessNode j)) 1
  have hm := congrArg (projection typeF4RootPairing typeF4RootPairing_base F) h
  change MulAut.conj (d F i) (x F j) = _ at hm
  rw [hm]
  have hinv (j : Fin 3) : (x F j)⁻¹ = rootElement typeF4RootPairing typeF4RootPairing_base F
      (typeF4RootPairing_baseEquiv (witnessNode j)) (-1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [x, ← ExceptionalSplit.rootElement_add, add_neg_cancel, ExceptionalSplit.rootElement_zero]
  simp only [hinv]
  have hc (i j : Fin 4) : typeF4RootPairing.pairingIn ℤ
      (typeF4RootPairing_baseEquiv i) (typeF4RootPairing_baseEquiv j) =
      typeF4CartanMatrix i j := typeF4RootPairing_base_cartan_apply i j
  rw [hc]
  fin_cases i <;> fin_cases j <;> norm_num [node,witnessNode,typeF4CartanMatrix,Fin.ext_iff,x]
  all_goals rfl

/-- The actual odd-characteristic F4 central quotient contains an elementary eight. -/
theorem three_le (hp : p ≠ 2) : 3 ≤ primeRank 2 (ExceptionalSplit.F4 F) := by
  refine IndependentInvolutions.three_le (d F) ?_ ?_ (x F) ?_ ?_
  · intro i
    change (projection typeF4RootPairing typeF4RootPairing_base F
      (elementaryCoroot (F := F) (typeF4RootPairing_baseEquiv (node i)))) ^ 2 = 1
    rw [← map_pow, elementaryCoroot_square, map_one]
  · intro i j
    exact (elementaryCoroot_commute (F := F) (typeF4RootPairing_baseEquiv (node i))
      (typeF4RootPairing_baseEquiv (node j))).map (projection _ _ F)
  · intro i he
    have ho : orderOf (x F i) = p := orderOf_eq_prime
      (rootElement_pow_char p _ _) (rootElement_simple_one_ne_one _)
    have hs : (x F i)^2=1 := by
      calc
        (x F i)^2 = x F i * x F i := pow_two _
        _ = x F i * (x F i)⁻¹ := congrArg (fun z => x F i * z) he.symm
        _ = 1 := mul_inv_cancel _
    have hd := orderOf_dvd_of_pow_eq_one hs
    rw [ho] at hd
    exact hp (((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (Fact.out : p.Prime).ne_one)
  · exact act F
end Theory.SpecificGroups.LieType.TwoRank.F4Odd
