module

public import Theory.GroupTheory.CubicRankOneCoreQuotientNormalizer
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup
public import GorensteinWalter.PSL2Center

/-!
# Rank-one Cartan normalization in prime-field PSL₂ containers

The source three-rank-one bound on J descends to J/O₂(J). For an odd
prime-field PSL₂ quotient, the proved outer automorphism group is a
two-group. Thus the elementary cubic Cartan has image of order at most
three. Its specified cubic B inside K fills that image, and the perfect
core-kernel theorem proves that the Cartan normalizes the original K.

This is the prime-field row of Aschbacher–Smith 9.3.1, printed p.732.
The source application retains the original old residual and tensor line.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.PSL2
variable {G : Type*} [_root_.Group G] [Finite G]
variable {F : Type*} [Field F] [Finite F]

/-- The exact prime-field model discharges the center and outer-group inputs
for any isomorphic core quotient. -/
theorem primeField_center_outer_of_equiv
    {X : Type*} [_root_.Group X]
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (e : X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    center X = ⊥ ∧ IsPGroup 2 (MulAut.Outer X) := by
  constructor
  · apply eq_bot_iff.mpr
    intro z hz
    have hez : e z ∈ center (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      (centerCongr e ⟨z,hz⟩).property
    rw [GorensteinWalter.psl2_center_eq_bot F,mem_bot] at hez
    exact e.injective (hez.trans e.map_one.symm)
  · exact (OuterSolvable.SmallDegreeSquares.outer_isPGroup_two hp ho
      (by decide : 1 ≤ 2)
      (show Nat.card F = p ^ 1 by simpa only [pow_one] using hF)).of_equiv
        (MulAut.outerCongr e).symm

/-- An elementary cubic Cartan normalizes the original perfect subgroup
in the rank-one odd prime-field PSL₂ core-quotient row. -/
theorem primeField_cartan_normalizes_perfect_subgroup
    (K J A B : Subgroup G) [Group.IsPerfect K] [IsElementaryAbelian 3 A]
    (hKJ : K ≤ J) (hAJ : A ≤ normalizer (J : Set G))
    (hBA : B ≤ A) (hBK : B ≤ K)
    (hQK : J.pCoreIn 2 ≤ normalizer (K : Set G)) (hB : Nat.card B = 3)
    (hr : primeRank 3 J ≤ 1)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hF : Nat.card F = p)
    (e : (J ⧸ pCore 2 J) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :
    A ≤ normalizer (K : Set G) := by
  obtain ⟨hz,hout⟩ := primeField_center_outer_of_equiv hp ho hF e
  exact CubicCoreQuotientNormalizer.normalizes_of_rank_one K J A B
    hKJ hAJ hBA hBK hQK hB hz hout hr

end Theory.PSL2
