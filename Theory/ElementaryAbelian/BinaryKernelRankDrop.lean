module

public import Theory.ElementaryAbelian.EightQuotientRank

/-!
# Rank drop after killing a nonidentity binary actor

An image of an elementary abelian two-group of rank at most n+1 has rank
at most n if its kernel is nontrivial. The kernel-image order formula and
the exponent bound for a finitely generated abelian group prove this without
choosing a basis. The application to E.1.5 kills a central actor element in
the literal local solvable-radical quotient.
-/

public section
open Subgroup
open scoped IsMulCommutative

namespace IsElementaryAbelian
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

/-- A nontrivial kernel removes one from an elementary binary rank bound. -/
theorem rank_map_le_of_nontrivial_kernel (A : Subgroup G)
    [IsElementaryAbelian 2 A] (f : G →* H) {n : ℕ}
    (hrank : Group.rank A ≤ n + 1) (z : G)
    (hzA : z ∈ A) (hz : z ≠ 1) (hfz : f z = 1) :
    Group.rank (A.map f) ≤ n := by
  let : CommGroup A := IsMulCommutative.instCommGroup
  have hcard : Nat.card A ≤ 2 ^ (n + 1) :=
    (Nat.le_of_dvd (by positivity) (card_dvd_exponent_pow_rank' A
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A)))).trans
      (pow_le_pow_right' (by decide) hrank)
  have hker : A ⊓ f.ker ≠ ⊥ := by
    intro h
    exact hz (mem_bot.mp (h ▸ (show z ∈ A ⊓ f.ker from ⟨hzA, hfz⟩)))
  let : Nontrivial (A ⊓ f.ker : Subgroup G) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hker
  have hkerCard : 2 ≤ Nat.card (A ⊓ f.ker : Subgroup G) := Finite.one_lt_card
  have hprod := card_inf_ker_mul_card_map A f
  let : IsElementaryAbelian 2 (A.map f) := IsElementaryAbelian.map f
  apply IsElementaryAbelian.rank_le_of_card_le (p := 2)
  rw [pow_succ] at hcard
  nlinarith

end IsElementaryAbelian
