module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.Contracts
public import Theory.GroupTheory.PGroup.Omega
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The elementary odd subgroup needed by E.6.27

For an abelian odd Hall subgroup Y, its fixed subgroup X = C_Y(V) is
preserved by N_S(Y) whenever S normalizes V. A prime omega subgroup of X
is therefore preserved by N_S(Y) too. The Frattini factorization
S = Q N_S(Y), with Y normalizing Q, makes this elementary subgroup permute
with S. This supplies the precise kind of subgroup used by 4.4.13(1).

The Hall and Frattini data must still be constructed from the marked
E.2.2 models. No such construction or normalizer escape is assumed here.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.6.27,
printed p.257, and the Frattini argument in 4.4.13, printed pp.623--624.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

/-- The set-product calculation behind the Hall-subgroup Frattini argument. -/
theorem permutes_of_factorization {A S Q D : Subgroup G}
    (hS : (S : Set G) = (Q : Set G) * (D : Set G))
    (hAQ : A ≤ normalizer (Q : Set G))
    (hDA : D ≤ normalizer (A : Set G)) :
    (A : Set G) * (S : Set G) = (S : Set G) * (A : Set G) := by
  rw [hS, ← mul_assoc, set_mul_normalizer_comm _ Q hAQ, mul_assoc,
    ← set_mul_normalizer_comm _ A hDA, ← mul_assoc]

/-- The Hall fixed subgroup is preserved by the Hall normalizer in S.
Only normalization of V by S is used; centralization of V by S is unnecessary. -/
theorem hallNormalizer_le_fixedNormalizer {Y S V : Subgroup G}
    (hSV : S ≤ normalizer (V : Set G)) :
    S ⊓ normalizer (Y : Set G) ≤
      normalizer (Y ⊓ centralizer (V : Set G) : Set G) :=
  (le_inf inf_le_right
    ((inf_le_left.trans hSV).trans (normalizer_le_normalizer_centralizer V))).trans
      inf_normalizer_le_normalizer_inf

/-- Select a prime omega subgroup of the Hall fixed subgroup. The output
retains full normalizer invariance, not merely normality inside the abelian Y. -/
theorem exists_elementary_odd_in_intersection [Finite G] {Y C : Subgroup G}
    (hY : IsMulCommutative Y) (hodd : Odd (Nat.card Y))
    (hne : Y ⊓ C ≠ ⊥) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ Y ⊓ C ∧
      Odd (Nat.card A) ∧
      normalizer (Y ⊓ C : Set G) ≤ normalizer (A : Set G) := by
  let X := Y ⊓ C
  let := hY
  let : IsMulCommutative X := by
    apply IsMulCommutative.of_comm
    intro a b
    apply Subtype.ext
    exact setLike_mul_comm (s := Y) a.property.1 b.property.1
  have hXodd : Odd (Nat.card X) := hodd.of_dvd_nat (card_dvd_of_le inf_le_left)
  obtain ⟨p, hp, hdiv⟩ := Nat.exists_prime_and_dvd
    (ne_of_gt ((one_lt_card_iff_ne_bot X).mpr hne))
  let : Fact p.Prime := ⟨hp⟩
  let E := omega₁ X (p := p)
  let : E.Characteristic := omega₁_characteristic X
  let : IsElementaryAbelian p E := IsElementaryAbelian.omega₁_of_isMulCommutative X
  refine ⟨p, E.map X.subtype, hp, hXodd.of_dvd_nat hdiv,
    omega₁_map_subtype_ne_bot X p hdiv, IsElementaryAbelian.map X.subtype,
    map_subtype_le E, ?_, normalizer_le_normalizer_characteristic_image X E⟩
  exact hXodd.of_dvd_nat (card_dvd_of_le (map_subtype_le E))

/-- A version for a pulled-back fixed subgroup, retaining the original group
rather than replacing it by an isomorphic ambient image. -/
theorem exists_elementary_odd_invariant_permuting [Finite G] {Y S C Q : Subgroup G}
    (hY : IsMulCommutative Y) (hodd : Odd (Nat.card Y))
    (hne : Y ⊓ C ≠ ⊥) (hSC : S ≤ normalizer (C : Set G))
    (hS : (S : Set G) = (Q : Set G) * (S ⊓ normalizer (Y : Set G) : Set G))
    (hYQ : Y ≤ normalizer (Q : Set G)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ Y ⊓ C ∧ Odd (Nat.card A) ∧
      (A : Set G) * (S : Set G) = (S : Set G) * (A : Set G) := by
  obtain ⟨p, A, hp, ho, hA, he, hAX, hAo, hNA⟩ :=
    exists_elementary_odd_in_intersection hY hodd hne
  have hNX : S ⊓ normalizer (Y : Set G) ≤ normalizer (Y ⊓ C : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans hSC)).trans inf_normalizer_le_normalizer_inf
  exact ⟨p, A, hp, ho, hA, he, hAX, hAo,
    permutes_of_factorization hS (hAX.trans (inf_le_left.trans hYQ)) (hNX.trans hNA)⟩

/-- The nonfaithful Hall branch supplies an actual elementary abelian odd-prime
subgroup permuting with the specified Sylow image. The normality needed for
permutation is expressed by the literal normalizer containment Y ≤ N_G(Q). -/
theorem exists_elementary_odd_fixed_permuting [Finite G] {Y S V Q : Subgroup G}
    (hY : IsMulCommutative Y) (hodd : Odd (Nat.card Y))
    (hne : Y ⊓ centralizer (V : Set G) ≠ ⊥)
    (hSV : S ≤ normalizer (V : Set G))
    (hS : (S : Set G) = (Q : Set G) * (S ⊓ normalizer (Y : Set G) : Set G))
    (hYQ : Y ≤ normalizer (Q : Set G)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
      IsElementaryAbelian p A ∧ A ≤ Y ⊓ centralizer (V : Set G) ∧
      Odd (Nat.card A) ∧ (A : Set G) * (S : Set G) = (S : Set G) * (A : Set G) := by
  obtain ⟨p, A, hp, ho, hA, he, hAX, hAo, hNA⟩ :=
    exists_elementary_odd_in_intersection hY hodd hne
  exact ⟨p, A, hp, ho, hA, he, hAX, hAo,
    permutes_of_factorization hS (hAX.trans (inf_le_left.trans hYQ))
      ((hallNormalizer_le_fixedNormalizer hSV).trans hNA)⟩

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan

end
