module

public import Theory.SpecificGroups.ClassicalOrthogonal.OddSevenTernaryCover.Blocks
public import Theory.SpecificGroups.ClassicalOrthogonal.OddSevenTernaryCover.HigherGeometry

/-!
# Rank-four local obstructions in all higher ternary orthogonal families

The genuine minus-six subgroup acts trivially on the nonzero complements
constructed in `HigherGeometry`. Its central negation is therefore an actual
projective involution, and its elementary subgroup of order 3⁴ remains faithful
in the involution centralizer. This covers odd rank at least three and both
even orthogonal types in rank at least four, on their literal carriers.

The final marked-center-quotient applications rule out quasithinness of every
finite odd central cover. They retain no multiplier, simplicity, perfectness,
or quotient-quasithinness premise. Source: Aschbacher–Smith A.2.17, printed p.39,
and the orthogonal geometry accompanying I.2.1, printed p.409; GLS3 §2.7.
-/

public noncomputable section
open Subgroup
namespace ClassicalOrthogonal.OddSevenTernaryCover
variable {F : Type} [Field F] [Finite F]

theorem exists_odd_elementary_four_centralizer {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card F = 3) :
    ∃ z : POmegaOdd n F, orderOf z = 2 ∧
      ∃ (A : Type) (_ : Group A) (_ : Finite A) (_ : IsElementaryAbelian 3 A),
        Nat.card A = 3^4 ∧ ∃ j : A →* centralizer ({z} : Set (POmegaOdd n F)),
          Function.Injective j := by
  let := Fintype.ofFinite F
  let : CharP F 3 := charP_of_card_eq_prime_pow (f := 1)
    (by simpa only [pow_one,Nat.card_eq_fintype_card] using hcard)
  obtain ⟨k,rfl⟩ : ∃ k, n=k+3 := ⟨n-3,by omega⟩
  let Q := negativeLine.prod (formD k F)
  exact exists_elementary_four_centralizer_of_embedding hcard
    ((projectiveElementaryMap _).comp (sixBlock Q _ (oddHigherIsometry hcard k)))
    (sixBlock_projective_injective Q _ (oddHigherIsometry hcard k))

theorem exists_plus_elementary_four_centralizer {n : ℕ} (hn : 4 ≤ n)
    (hcard : Nat.card F = 3) :
    ∃ z : POmegaPlus n F, orderOf z = 2 ∧
      ∃ (A : Type) (_ : Group A) (_ : Finite A) (_ : IsElementaryAbelian 3 A),
        Nat.card A = 3^4 ∧ ∃ j : A →* centralizer ({z} : Set (POmegaPlus n F)),
          Function.Injective j := by
  let := Fintype.ofFinite F
  let : CharP F 3 := charP_of_card_eq_prime_pow (f := 1)
    (by simpa only [pow_one,Nat.card_eq_fintype_card] using hcard)
  obtain ⟨k,rfl⟩ : ∃ k, n=k+4 := ⟨n-4,by omega⟩
  let Q := (negativeLine.prod negativeLine).prod (formD k F)
  exact exists_elementary_four_centralizer_of_embedding hcard
    ((projectiveElementaryMap _).comp (sixBlock Q _ (plusHigherIsometry hcard k)))
    (sixBlock_projective_injective Q _ (plusHigherIsometry hcard k))

theorem exists_minus_elementary_four_centralizer {n : ℕ} (hn : 4 ≤ n)
    (hcard : Nat.card F = 3) :
    ∃ z : ClassicalGroup.POmegaMinus n F, orderOf z = 2 ∧
      ∃ (A : Type) (_ : Group A) (_ : Finite A) (_ : IsElementaryAbelian 3 A),
        Nat.card A = 3^4 ∧
          ∃ j : A →* centralizer ({z} : Set (ClassicalGroup.POmegaMinus n F)),
            Function.Injective j := by
  obtain ⟨k,rfl⟩ : ∃ k, n=k+4 := ⟨n-4,by omega⟩
  exact exists_elementary_four_centralizer_of_embedding hcard
    (sixProjectiveOmegaBlock (formD (k+1) F) _ (minusHigherIsometry k))
    (sixProjectiveOmegaBlock_injective (formD (k+1) F) _ (minusHigherIsometry k))

variable {E : Type*} [Group E] [Finite E]

theorem not_isQuasithin_of_odd_quotient_equiv {n : ℕ} (hn : 3 ≤ n)
    (hcard : Nat.card F = 3) (e : (E ⧸ center E) ≃* POmegaOdd n F)
    (ho : Odd (Nat.card (center E))) : ¬ IsQuasithin E := by
  obtain ⟨z,hz,A,hG,hfin,hA,hAc,j,hj⟩ := exists_odd_elementary_four_centralizer hn hcard
  let := hG
  let := hfin
  let := hA
  exact CentralExtension.not_isQuasithin_of_center_quotient_model e ho
    (by decide : 3 ≠ 2) hz j hj hAc.ge

theorem not_isQuasithin_of_plus_quotient_equiv {n : ℕ} (hn : 4 ≤ n)
    (hcard : Nat.card F = 3) (e : (E ⧸ center E) ≃* POmegaPlus n F)
    (ho : Odd (Nat.card (center E))) : ¬ IsQuasithin E := by
  obtain ⟨z,hz,A,hG,hfin,hA,hAc,j,hj⟩ := exists_plus_elementary_four_centralizer hn hcard
  let := hG
  let := hfin
  let := hA
  exact CentralExtension.not_isQuasithin_of_center_quotient_model e ho
    (by decide : 3 ≠ 2) hz j hj hAc.ge

theorem not_isQuasithin_of_minus_quotient_equiv {n : ℕ} (hn : 4 ≤ n)
    (hcard : Nat.card F = 3) (e : (E ⧸ center E) ≃* ClassicalGroup.POmegaMinus n F)
    (ho : Odd (Nat.card (center E))) : ¬ IsQuasithin E := by
  obtain ⟨z,hz,A,hG,hfin,hA,hAc,j,hj⟩ := exists_minus_elementary_four_centralizer hn hcard
  let := hG
  let := hfin
  let := hA
  exact CentralExtension.not_isQuasithin_of_center_quotient_model e ho
    (by decide : 3 ≠ 2) hz j hj hAc.ge

end ClassicalOrthogonal.OddSevenTernaryCover
