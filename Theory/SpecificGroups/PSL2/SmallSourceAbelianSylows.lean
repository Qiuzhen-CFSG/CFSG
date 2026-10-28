module
public import Theory.GroupTheory.AbelianSylowSections
public import Theory.SpecificGroups.SL2.BinaryOddRank
public import Theory.SpecificGroups.SL2.PrimeFieldOddSubgroups
public import Theory.GroupTheory.OddPrimeRankOneSylow
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Abelian Sylow three-subgroups in the original partner models

The order formula makes Sylow three-subgroups of PSL₄(2) and PSL₅(2)
have order nine. Odd Sylows of binary SL₂ and prime-field SL₂ are cyclic;
projection and field transport give abelian Sylows for the corresponding
projective models. All models use their actual group carriers.

Source: Aschbacher--Smith 15.2.12(2) and proof of 15.2.15, pp.1111,1118.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Matrix.ProjectiveSpecialLinearGroup
variable {F : Type*} [Field F] [Finite F]

/-- The binary rank-four and rank-five models have Sylow three-subgroups of order nine. -/
theorem abelianSylow_three_binary_small_rank {n : ℕ} (hn : n=4 ∨ n=5)
    (hF : Nat.card F=2) : HasAbelianSylow 3 PSL(n,F) := by
  intro P
  have hc : Nat.card P = 3^2 := by
    rcases hn with rfl | rfl
    · have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
      rw [hF] at hh
      norm_num [Fin.prod_univ_succ] at hh
      rw [Sylow.card_eq_multiplicity,hh]
      decide +kernel
    · have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
      rw [hF] at hh
      norm_num [Fin.prod_univ_succ] at hh
      rw [Sylow.card_eq_multiplicity,hh]
      decide +kernel
  exact IsPGroup.isMulCommutative_of_card_eq_prime_sq hc

/-- Every Sylow three-subgroup of an even-field rank-one model is abelian. -/
theorem abelianSylow_three_even_rank_two {n : ℕ} (hF : Nat.card F=2^n) :
    HasAbelianSylow 3 PSL(2,F) := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hsl : HasAbelianSylow 3 SL(2,F) := by
    intro P
    let := P.isCyclic_of_odd_of_primeRank_le_one (by decide : Odd 3)
      (Matrix.SL2.binary_odd_primeRank_le_one (by decide : Odd 3))
    infer_instance
  exact hsl.of_surjective (QuotientGroup.mk' (center SL(2,F)))
    (QuotientGroup.mk'_surjective _)

/-- Every Sylow three-subgroup of a prime-field rank-one model is abelian. -/
theorem abelianSylow_three_prime_rank_two {p : ℕ} (hp : p.Prime)
    (hF : Nat.card F=p) : HasAbelianSylow 3 PSL(2,F) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let ef : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  have hsl : HasAbelianSylow 3 SL(2,ZMod p) := by
    intro P
    let := Matrix.SpecialLinearGroup.isCyclic_of_odd_pGroup_injective_primeField
      P.isPGroup' (by decide : (3:ℕ)≠2) (P : Subgroup SL(2,ZMod p)).subtype
      (P : Subgroup SL(2,ZMod p)).subtype_injective
    infer_instance
  have hpsl : HasAbelianSylow 3 PSL(2,ZMod p) :=
    hsl.of_surjective (QuotientGroup.mk' (center SL(2,ZMod p))) (QuotientGroup.mk'_surjective _)
  exact hpsl.of_injective (Atlas.fieldEquivPSL 2 ef).toMonoidHom (Atlas.fieldEquivPSL 2 ef).injective
end Matrix.ProjectiveSpecialLinearGroup
