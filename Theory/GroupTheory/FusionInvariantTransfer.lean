module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.GroupTheory.Solvable

/-!
# Transfer of a character invariant under fusion

A character on a subgroup which takes equal values on ambient conjugates
evaluates under transfer as its value raised to the subgroup index. For a
binary character on a Sylow two-subgroup this is the original value, since
the index is odd. Consequently a nonsolvable finite simple group admits no
nontrivial such character on its Sylow two-subgroups.

The proof uses the orbit-product formula for ordinary transfer: every orbit
contributes the character of a conjugate power, and the orbit lengths sum
to the index. No involution outside the character kernel is required.
This supplies the transfer step of a simple-group exclusion based on
van Beek, *Fusion Systems and Rank 2 Simple Groups of Lie Type* (2024),
Proposition 3.1; the finite fusion classification itself is not asserted here.
-/

namespace MonoidHom

/-- Transfer on an element whose conjugate powers have the same character values. -/
public theorem transfer_apply_eq_pow_of_conjugate_powers
    {G A : Type*} [Group G] [CommGroup A] [Finite G]
    {H : Subgroup G} (character : H →* A) (element : H)
    (hrespect : ∀ (power : ℕ) (other : H),
      IsConj (((element ^ power) : H) : G) (other : G) →
        character other = character (element ^ power)) :
    character.transfer (element : G) = character element ^ H.index := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  let := Fintype.ofFinite
    (Quotient (MulAction.orbitRel (Subgroup.zpowers (element : G)) (G ⧸ H)))
  rw [transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  calc
    _ = ∏ orbit : Quotient
        (MulAction.orbitRel (Subgroup.zpowers (element : G)) (G ⧸ H)),
        character element ^ Function.minimalPeriod ((element : G) • ·) orbit.out := by
      apply Finset.prod_congr rfl
      intro orbit _
      rw [← map_pow]
      apply hrespect
      apply isConj_iff.mpr
      refine ⟨orbit.out.out⁻¹, ?_⟩
      simp
    _ = character element ^ H.index := by
      rw [Finset.prod_pow_eq_pow_sum, Subgroup.index_eq_sum_minimalPeriod H (element : G)]

/-- A character constant on ambient conjugacy classes transfers by the index power. -/
public theorem transfer_apply_eq_pow_of_fusion_invariant
    {G A : Type*} [Group G] [CommGroup A] [Finite G]
    {H : Subgroup G} (character : H →* A)
    (hrespect : ∀ x y : H, IsConj (x : G) (y : G) → character x = character y)
    (element : H) :
    character.transfer (element : G) = character element ^ H.index :=
  character.transfer_apply_eq_pow_of_conjugate_powers element
    (fun power other hconj => (hrespect (element ^ power) other hconj).symm)

end MonoidHom

namespace Sylow

/-- Transfer extends every fusion-invariant binary character of a Sylow two-subgroup. -/
public theorem transfer_apply_eq_of_fusion_invariant
    {G A : Type*} [Group G] [CommGroup A] [Finite G] [Finite A]
    (S : Sylow 2 G) (character : S →* A) (hcard : Nat.card A = 2)
    (hrespect : ∀ x y : S, IsConj (x : G) (y : G) → character x = character y)
    (element : S) : character.transfer (element : G) = character element := by
  rw [character.transfer_apply_eq_pow_of_fusion_invariant hrespect]
  have hodd : (S : Subgroup G).index % 2 = 1 := by
    have h := S.not_dvd_index
    omega
  have h := pow_mod_natCard (character element) (S : Subgroup G).index
  simpa only [hcard, hodd, pow_one] using h.symm

/-- A nonsolvable finite simple group has no nontrivial fusion-invariant
binary character on a Sylow two-subgroup. -/
public theorem fusion_invariant_eq_one_of_simple
    {G A : Type*} [Group G] [CommGroup A] [Finite G] [Finite A]
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (S : Sylow 2 G) (character : S →* A) (hcard : Nat.card A = 2)
    (hrespect : ∀ x y : S, IsConj (x : G) (y : G) → character x = character y)
    (element : S) : character element = 1 := by
  have hker : character.transfer.ker = ⊤ := by
    rcases (inferInstance : character.transfer.ker.Normal).eq_bot_or_eq_top with hbot | htop
    · exact (hns (Group.isSolvable_of_isSolvable_injective
        ((MonoidHom.ker_eq_bot_iff _).mp hbot))).elim
    · exact htop
  have hzero : character.transfer (element : G) = 1 := by
    change (element : G) ∈ character.transfer.ker
    rw [hker]
    trivial
  rwa [S.transfer_apply_eq_of_fusion_invariant character hcard hrespect] at hzero

end Sylow
