module

public import Stellmacher.Recognition.MinimalSimpleStrong
public import Stellmacher.Recognition.MinimalSimpleDihedral
public import Stellmacher.Recognition.SimpleReduction
public import Stellmacher.Recognition.Sp4TwoExclusion

/-!
# The proved local reduction for minimal simple groups

Minimal simplicity supplies the N2 condition, even order, and trivial two-core
required by Stellmacher. The proved simple-group reduction applies the
Bender--Suzuki and Gorenstein--Walter recognition theorems, including the
recognition of the local L3(2) type via its dihedral Sylow subgroup.

Here minimal simplicity removes A7 using its proper A5 subgroup and removes
the even PSU3 family using the all-prime N obstruction. The local Sp4(2) type
is excluded by the existing transfer theorem. The recognized alternatives are
actual binary PSL2, Suzuki, and odd-field PSL2 isomorphisms.

The G2 and twisted F4 local types, semidihedral Sylow subgroup, order-32 local
configuration, and nontrivial odd core of an involution centralizer remain
explicit. This is a proved reduction toward Thompson's classification, not
its five-family endpoint; in particular the odd-core branch is not asserted
to be impossible. Field-exponent and prime congruence restrictions also remain
to be proved.

Source: Stellmacher Theorem 2 and the simple-group reductions in
Stellmacher.Recognition.SimpleReduction, specialized to the GLS1 §28
minimal-simple hypothesis.
-/

namespace Stellmacher.Recognition

universe u

/-- Recognized rank-one models or an explicit remaining local recognition case. -/
public theorem minimalSimple_local_reduction
    {G : Type u} [Group G] [Finite G] (hG : IsMinimalSimple G) (S : Sylow 2 G) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (G ≃* PSL2Model n)) ∨
    (∃ n : ℕ, 1 ≤ n ∧ Nonempty (G ≃* SzModel n)) ∨
    (∃ (K : Type u) (instK : Field K) (_ : Finite K),
      let : Field K := instK
      Odd (Nat.card K) ∧ 3 < Nat.card K ∧
        Nonempty (G ≃* GorensteinWalter.PSL2 K)) ∨
    (IsOfGTwoTwoDerivedType G ∨ IsOfTwistedF4TwoDerivedType G) ∨
    IsSemidihedralGroup S ∨
    (Nat.card S = 2 ^ 5 ∧ ∃ U : Subgroup G, IsMaximalTwoLocal U ∧
      Nonempty (U ≃* (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)))) ∨
    (∃ t : G, orderOf t = 2 ∧
      pPrimeCore 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥) := by
  let _ := hG.isSimpleGroup
  rcases simple_nTwo_recognition_reduction hG.not_isSolvable hG.isNTwoGroup S with
    hB | hGW | htype | hsd | h32 | hodd
  · rcases minimalSimple_bender_recognition hG hB with hPSL | hSz
    · exact Or.inl hPSL
    · exact Or.inr (Or.inl hSz)
  · exact Or.inr (Or.inr (Or.inl (minimalSimple_gorensteinWalter_recognition hG hGW)))
  · rcases htype with hSp4 | hrest
    · exact (not_sp4Two_type_of_simple_nonsolvable hG.not_isSolvable hSp4).elim
    · exact Or.inr (Or.inr (Or.inr (Or.inl hrest)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hsd))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h32)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hodd)))))

end Stellmacher.Recognition
