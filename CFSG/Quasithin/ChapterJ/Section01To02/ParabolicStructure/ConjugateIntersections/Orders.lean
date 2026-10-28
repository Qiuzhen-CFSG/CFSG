module
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Basic

/-!
# The two strict intersections in J.2.2(5)

The literal star image of A ≤ H has order |A|/|A ∩ Q|, for the actual
Ru2 quotient map. For A an L-conjugate of U, the subgroup chain
V ≤ A ∩ HC < A ∩ Q < A and the orders |V| = 8, |A| = 32 force
|A ∩ Q| = 16 and A ∩ HC = V. Thus the star image has order two.

The strict inclusions are inputs to this order calculation; the hyperplane
argument and the orbit-generation argument discharge them in the owner.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
J.2.2(5), printed pp.432–433 (PDF pp.443–444).
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.ConjugateIntersections
open Subgroup Representation
variable {G : Type*} [Group G] [Finite G]

private theorem card_lt_of_lt {A B : Subgroup G} (h : A < B) :
    Nat.card A < Nat.card B := by
  have hl := card_le_of_le h.le
  have hn : Nat.card A ≠ Nat.card B := by
    intro he
    exact h.ne (eq_of_le_of_card_ge h.le he.ge)
  omega

/-- The literal quotient marking gives the usual kernel-image order formula. -/
theorem card_star_mul_card_inf_Q (d : LocalSetup G) (A : Subgroup G)
    (hA : A ≤ d.toTypeRuSetup.H) :
    Nat.card ((A.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap) *
      Nat.card (A ⊓ d.toTypeRuSetup.Q : Subgroup G) = Nat.card A := by
  let f : A →* S5 := d.ru2.quotientMap.comp (inclusion hA)
  have hr : f.range = (A.subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact mem_map.mpr ⟨⟨a, hA a.property⟩, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hk : f.ker = (A ⊓ d.toTypeRuSetup.Q).subgroupOf A := by
    ext a
    change d.ru2.quotientMap ⟨a, hA a.property⟩ = 1 ↔ _
    rw [← MonoidHom.mem_ker, d.ru2.quotient_kernel]
    change (a : G) ∈ d.toTypeRuSetup.Q ↔ (a : G) ∈ A ∧ (a : G) ∈ d.toTypeRuSetup.Q
    exact ⟨fun h => ⟨a.property, h⟩, And.right⟩
  have hh := f.ker.index_mul_card
  rw [index_ker, hr, hk,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : A ⊓ d.toTypeRuSetup.Q ≤ A)).toEquiv] at hh
  exact hh

/-- Once the two strict inclusions are known, the order-32 group has only
room for the chain V < Uα∩Q < Uα. This gives both conclusions of J.2.2(5). -/
theorem conclusions_of_strict_intersections (d : LocalSetup G) (l : G) (hl : l ∈ d.L)
    (hQ : ¬ conjugateU d l ≤ d.toTypeRuSetup.Q)
    (hC : ¬ conjugateU d l ⊓ d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.HC) :
    Nat.card (((conjugateU d l).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap) = 2 ∧
      conjugateU d l ⊓ d.toTypeRuSetup.HC = d.V := by
  let A := conjugateU d l
  have hVA : d.V ≤ A := V_le_conjugateU d l hl
  have hVC : d.V ≤ d.toTypeRuSetup.HC := V_le_HC d
  have hCQ : d.toTypeRuSetup.HC ≤ d.toTypeRuSetup.Q := d.toTypeRuSetup.HC_le_Q
  have hC_lt_Q : A ⊓ d.toTypeRuSetup.HC < A ⊓ d.toTypeRuSetup.Q := by
    refine lt_of_le_of_ne (inf_le_inf_left A hCQ) ?_
    intro he
    exact hC (he.ge.trans inf_le_right)
  have hQ_lt_A : A ⊓ d.toTypeRuSetup.Q < A := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro he
    exact hQ (he.ge.trans inf_le_right)
  have hlt32 : Nat.card (A ⊓ d.toTypeRuSetup.Q : Subgroup G) < 32 := by
    simpa only [A, card_conjugateU] using card_lt_of_lt hQ_lt_A
  have hlt := card_lt_of_lt hC_lt_Q
  have hge8 : 8 ≤ Nat.card (A ⊓ d.toTypeRuSetup.HC : Subgroup G) := by
    simpa only [d.ru1.card_V] using card_le_of_le (le_inf hVA hVC)
  have hdvd : Nat.card (A ⊓ d.toTypeRuSetup.Q : Subgroup G) ∣ 2 ^ 5 := by
    simpa only [A, card_conjugateU, show 2 ^ 5 = 32 by decide] using
      card_dvd_of_le (inf_le_left : A ⊓ d.toTypeRuSetup.Q ≤ A)
  obtain ⟨n, hn, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hcardQ : Nat.card (A ⊓ d.toTypeRuSetup.Q : Subgroup G) = 16 := by
    interval_cases n <;> norm_num only [pow_zero, pow_succ, Nat.reduceMul] at he <;> omega
  have hdvdC : Nat.card (A ⊓ d.toTypeRuSetup.HC : Subgroup G) ∣ 2 ^ 4 := by
    have hh := card_dvd_of_le (inf_le_inf_left A hCQ)
    rw [hcardQ] at hh
    exact hh
  obtain ⟨m, hm, heC⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvdC
  have hcardC : Nat.card (A ⊓ d.toTypeRuSetup.HC : Subgroup G) = 8 := by
    interval_cases m <;> norm_num only [pow_zero, pow_succ, Nat.reduceMul] at heC <;> omega
  refine ⟨?_, ?_⟩
  · have hh := card_star_mul_card_inf_Q d A (conjugateU_le_H d l hl)
    rw [hcardQ, card_conjugateU] at hh
    change Nat.card (((conjugateU d l).subgroupOf d.toTypeRuSetup.H).map d.ru2.quotientMap) * 16 = 32 at hh
    omega
  · apply (eq_of_le_of_card_ge (le_inf hVA hVC) ?_).symm
    rw [hcardC, d.ru1.card_V]

end CFSG.Quasithin.ChapterJ.ConjugateIntersections
