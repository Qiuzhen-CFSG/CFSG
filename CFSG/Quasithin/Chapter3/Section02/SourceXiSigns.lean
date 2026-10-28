module

public import CFSG.Quasithin.Chapter1.Section03.Basic

/-!
# The source signs on the solvable uniqueness family

Definition 3.2.12 of Aschbacher--Smith, *The Classification of Quasithin
Groups*, combined manuscript of 1 March 2004, printed p.584.
The automizer is the image of the full ambient normalizer on the intrinsic
quotient Y/O₂(Y). In particular it is not the inner action of Y.
The two prime-divisor conditions below encode precisely the source
{2,3}- and {2,5}-group conditions. No assertion of Lemma 3.2.13 is made.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter3
open Subgroup
variable {G : Type*} [Group G]

/-- The action of N_G(Y) on Y/O₂(Y). -/
def xiQuotientNormalizerAction (Y : Subgroup G) :
    normalizer (Y : Set G) →* MulAut (Chapter1.XiQuotient Y) :=
  (quotientAut (pCore 2 Y)).comp Y.normalizerMonoidHom

/-- The literal ambient automizer Aut_G(Y/O₂(Y)). -/
def xiQuotientAutomizer (Y : Subgroup G) : Subgroup (MulAut (Chapter1.XiQuotient Y)) :=
  (xiQuotientNormalizerAction Y).range

/-- Definition 3.2.12: the negative part of the uppercase Ξ family. -/
def XiMinus (G : Type*) [Group G] (T : Subgroup G) : Set (Subgroup G) :=
  {Y | Y ∈ Chapter1.Xi G T ∧
    ((∀ p : ℕ, p.Prime → p ∣ Nat.card Y → p = 2 ∨ p = 3) ∨
      (IsPGroup 5 (Chapter1.XiQuotient Y) ∧
        ∀ p : ℕ, p.Prime → p ∣ Nat.card (xiQuotientAutomizer Y) → p = 2 ∨ p = 5))}

/-- Definition 3.2.12: the complementary positive family. -/
def XiPlus (G : Type*) [Group G] (T : Subgroup G) : Set (Subgroup G) :=
  Chapter1.Xi G T \ XiMinus G T

/-- A five-divisible member with a cubic ambient automizer is positive.
Both alternatives in the source definition are ruled out separately. -/
theorem mem_XiPlus_of_five_dvd_of_three_dvd_automizer {T Y : Subgroup G}
    (hY : Y ∈ Chapter1.Xi G T) (h5 : 5 ∣ Nat.card Y)
    (h3 : 3 ∣ Nat.card (xiQuotientAutomizer Y)) : Y ∈ XiPlus G T := by
  refine ⟨hY, ?_⟩
  rintro ⟨_, ha | ⟨_, hb⟩⟩
  · rcases ha 5 (by decide) h5 with h | h <;> omega
  · rcases hb 3 Nat.prime_three h3 with h | h <;> omega

/-- The actual normalizer actor supplies cubic divisibility of its image,
without replacing that image by the full abstract automorphism group. -/
theorem three_dvd_xiQuotientAutomizer_of_actor [Finite G] (Y : Subgroup G)
    (x : normalizer (Y : Set G))
    (hx : orderOf (xiQuotientNormalizerAction Y x) = 3) :
    3 ∣ Nat.card (xiQuotientAutomizer Y) := by
  let a : xiQuotientAutomizer Y := (xiQuotientNormalizerAction Y).rangeRestrict x
  have ha : orderOf a = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hx
  exact ha ▸ orderOf_dvd_natCard a

/-- The prime-five exclusion test with the literal quotient action and an
actual ambient normalizer element, as used in 15.4.10. -/
theorem mem_XiPlus_of_five_quotient_of_cubic_actor [Finite G] {T Y : Subgroup G}
    (hY : Y ∈ Chapter1.Xi G T) (h5 : 5 ∣ Nat.card (Chapter1.XiQuotient Y))
    (x : normalizer (Y : Set G))
    (hx : orderOf (xiQuotientNormalizerAction Y x) = 3) : Y ∈ XiPlus G T :=
  mem_XiPlus_of_five_dvd_of_three_dvd_automizer hY
    (h5.trans (card_quotient_dvd_card (pCore 2 Y)))
    (three_dvd_xiQuotientAutomizer_of_actor Y x hx)

end CFSG.Quasithin.Chapter3
