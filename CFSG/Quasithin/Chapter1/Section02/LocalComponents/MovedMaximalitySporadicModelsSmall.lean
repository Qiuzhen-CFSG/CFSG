module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximalitySmallModels
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.SmallSylow
public import Theory.GroupTheory.CComponent.RadicalPairOrder
public import Theory.GroupTheory.Commutator.PerfectSmallIndex
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.Mathieu.M11.Properties.Order
public import Theory.Mathieu.M12.SylowOvergroups.RankTwoCoverage
public import Theory.GroupTheory.TwoPrimeSolvable

/-!
# J₁, M₁₁ and M₁₂ in the moved-component obstruction

Two distinct C-components give two independent nonabelian simple radical
quotients. Each quotient has order divisible by four, so sixteen divides
the ambient order. The actual J₁ order has two-part eight, excluding this
in every subgroup. Each simple quotient has order at least sixty by
Burnside's two-prime theorem. Two such factors cannot fit in a proper
subgroup of M₁₁: perfectness gives index at least five. For M₁₂ the checked
Sylow overgroup calculation bounds
each proper overgroup's order by a divisor of 192; Burnside's two-prime
theorem makes these overgroups solvable.

These calculations apply to the literal radical quotient of a normalized
overcomponent in the original Chapter 1 configuration. The other named
sporadic carriers remain separate model calculations.

Source: Aschbacher--Smith, A.3.12 and 1.2.8(1), printed pp.47--48 and 506.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02.MovedMaximality
variable {G : Type*} [Group G] [Finite G]

private theorem four_dvd_card_simple_perfect [IsSimpleGroup G] [Group.IsPerfect G] :
    4 ∣ Nat.card G := by
  let S : Sylow 2 G := Classical.choice inferInstance
  have hlarge := IndexTwo.two_lt_card_sylow_of_simple_perfect S
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
  have htwo : 2 ≤ n := by
    by_contra! h
    have hsmall := Nat.pow_le_pow_right (by decide : 0 < 2) (show n ≤ 1 by omega)
    rw [← hn] at hsmall
    norm_num at hsmall
    omega
  exact (show 4 ∣ Nat.card S by rw [hn]; exact pow_dvd_pow 2 htwo).trans
    (card_subgroup_dvd_card _)

private theorem components_equal_of_not_sixteen_dvd (h16 : ¬ 16 ∣ Nat.card G)
    (B C : Subgroup G) (hB : B.IsCComponent) (hC : C.IsCComponent) : B = C := by
  by_contra hne
  let := hB.perfect
  let := hC.perfect
  let := hB.isSimpleGroup_quotient_solvableRadical
  let := hC.isSimpleGroup_quotient_solvableRadical
  exact h16 ((Nat.mul_dvd_mul
    (four_dvd_card_simple_perfect (G := B ⧸ solvableRadical B))
    (four_dvd_card_simple_perfect (G := C ⧸ solvableRadical C))).trans
      (hB.radical_quotient_card_mul_dvd hC hne))

/-- The actual J₁ carrier has at most one C-component in every Sylow overgroup. -/
theorem janko_one_sylow_overgroup_component_unique
    (hm : Nonempty (G ≃* Janko1.Model)) : SylowOvergroupComponentUnique G := by
  obtain ⟨e⟩ := hm
  intro S P _ B C hB hC
  apply components_equal_of_not_sixteen_dvd _ B C hB hC
  intro hd
  have hh := hd.trans P.card_subgroup_dvd_card
  rw [Nat.card_congr e.toEquiv, Janko1.card_model] at hh
  norm_num at hh

private theorem small_prime_support : ∀ n : Fin 60, 0 < (n : ℕ) → 4 ∣ (n : ℕ) →
    ∃ q : Fin 14, (q : ℕ).Prime ∧
      ∀ p ∈ (n : ℕ).primeFactors, p = 2 ∨ p = (q : ℕ) := by
  decide +kernel

private theorem sixty_le_card_simple_perfect [IsSimpleGroup G] [Group.IsPerfect G] :
    60 ≤ Nat.card G := by
  by_contra! hsmall
  obtain ⟨q, hq, hprimes⟩ := small_prime_support ⟨Nat.card G, hsmall⟩ Nat.card_pos
    four_dvd_card_simple_perfect
  apply Group.IsPerfect.not_isSolvable G
  apply isSolvable_of_prime_dvd_card_eq_two_or_prime G hq
  intro p hp hd
  exact hprimes p (Nat.mem_primeFactors.mpr ⟨hp, hd, Nat.card_pos.ne'⟩)

/-- A proper subgroup of M₁₁ is too small to have two C-components. -/
theorem mathieu_eleven_sylow_overgroup_component_unique
    [IsSimpleGroup G] [Group.IsPerfect G]
    (hm : Nonempty (G ≃* Sporadic.Mathieu.M11)) : SylowOvergroupComponentUnique G := by
  obtain ⟨e⟩ := hm
  have hc : Nat.card G = 7920 := (Nat.card_congr e.toEquiv).trans Sporadic.Mathieu.m11_order
  apply SylowOvergroupComponentUnique.of_proper_overgroups
  intro S P _ hP B C hB hC
  by_contra hne
  let := hB.perfect
  let := hC.perfect
  let := hB.isSimpleGroup_quotient_solvableRadical
  let := hC.isSimpleGroup_quotient_solvableRadical
  have h60B := sixty_le_card_simple_perfect (G := B ⧸ solvableRadical B)
  have h60C := sixty_le_card_simple_perfect (G := C ⧸ solvableRadical C)
  have hprod := Nat.le_of_dvd (Nat.card_pos (α := P))
    (hB.radical_quotient_card_mul_dvd hC hne)
  have hsize : 3600 ≤ Nat.card P := by nlinarith
  have hi : 5 ≤ P.index := by
    by_contra! hsmall
    exact hP (top_le_iff.mp (le_of_isPerfect_of_index_le_four ⊤ P (by omega)))
  have hcard := P.card_mul_index
  rw [hc] at hcard
  nlinarith

private theorem mathieu_twelve_proper_sylow_overgroup_solvable
    (S : Sylow 2 Sporadic.Mathieu.M12) (P : Subgroup Sporadic.Mathieu.M12)
    (hSP : (S : Subgroup Sporadic.Mathieu.M12) ≤ P) (hP : P ≠ ⊤) :
    Group.IsSolvable P := by
  have hd := Sporadic.Mathieu.M12SmallPair.SylowOvergroups.card_dvd_192_of_ne_top
    P hP ⟨S, hSP⟩
  apply isSolvable_of_prime_dvd_card_eq_two_or_prime P Nat.prime_three
  intro p hp hpP
  have h : p ∣ 2 ^ 6 * 3 := hpP.trans hd
  rcases hp.dvd_mul.mp h with htwo | hthree
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow htwo))
  · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hthree)

/-- Every proper full-Sylow overgroup in M₁₂ is solvable, so its component is unique. -/
theorem mathieu_twelve_sylow_overgroup_component_unique
    [IsSimpleGroup G] [Group.IsPerfect G]
    (hm : Nonempty (G ≃* Sporadic.Mathieu.M12)) : SylowOvergroupComponentUnique G := by
  obtain ⟨e⟩ := hm
  exact SylowOvergroupComponentUnique.of_solvable_proper_overgroups
    (SolvableSylowOvergroups.of_equiv e mathieu_twelve_proper_sylow_overgroup_solvable)

/-- The full Theorem C sporadic predicate, after excluding these three carriers.
All eight other named rows retain their actual carrier equivalences. -/
theorem sporadic_model_remaining_of_not_unique
    [IsSimpleGroup G] [Group.IsPerfect G]
    (hspor : ChapterA.Section02.IsTheoremCSporadicModel G)
    (hu : ¬ SylowOvergroupComponentUnique G) :
    ∃ name : ClassificationModels.SporadicName,
      name ≠ .j3 ∧ name ≠ .m11 ∧ name ≠ .m12 ∧ Nonempty (G ≃* name.Carrier) := by
  rcases hspor with ⟨name, hj, iso⟩ | hj
  · refine ⟨name, hj, ?_, ?_, iso⟩
    · rintro rfl
      exact hu (mathieu_eleven_sylow_overgroup_component_unique iso)
    · rintro rfl
      exact hu (mathieu_twelve_sylow_overgroup_component_unique iso)
  · exact (hu (janko_one_sylow_overgroup_component_unique hj)).elim

/-- The J₁ alternative is impossible for the original normalized overcomponent's
literal radical quotient. -/
theorem moved_normalized_not_janko_one_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    let Q := C ⧸ solvableRadical C
    ¬ Nonempty (Q ≃* Janko1.Model) := by
  dsimp only
  intro hmodel
  obtain ⟨_, _, _, hu⟩ := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
  exact hu (janko_one_sylow_overgroup_component_unique hmodel)

/-- The M₁₁ alternative is impossible for the same literal radical quotient. -/
theorem moved_normalized_not_mathieu_eleven_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    let Q := C ⧸ solvableRadical C
    ¬ Nonempty (Q ≃* Sporadic.Mathieu.M11) := by
  dsimp only
  intro hmodel
  obtain ⟨hs, _, _, hu⟩ := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
  let := hs
  let := hK.1.perfect
  exact hu (mathieu_eleven_sylow_overgroup_component_unique hmodel)

/-- The M₁₂ alternative is impossible for the same literal radical quotient. -/
theorem moved_normalized_not_mathieu_twelve_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    let Q := C ⧸ solvableRadical C
    ¬ Nonempty (Q ≃* Sporadic.Mathieu.M12) := by
  dsimp only
  intro hmodel
  obtain ⟨hs, _, _, hu⟩ := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
  let := hs
  let := hK.1.perfect
  exact hu (mathieu_twelve_sylow_overgroup_component_unique hmodel)

/-- Applying the exclusions to the original normalized overcomponent leaves
exactly the eight outstanding named sporadic carriers. -/
theorem moved_normalized_remaining_sporadic_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ L G (T : Subgroup G)) (hK : K ∈ L G (T : Subgroup G))
    (hBK : B ≤ K) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hm : B < conjugateSpanBy B (T : Subgroup G)) :
    let C := K.subgroupOf (K ⊔ (T : Subgroup G))
    let Q := C ⧸ solvableRadical C
    ChapterA.Section02.IsTheoremCSporadicModel Q →
      ∃ name : ClassificationModels.SporadicName,
        name ≠ .j3 ∧ name ≠ .m11 ∧ name ≠ .m12 ∧ Nonempty (Q ≃* name.Carrier) := by
  dsimp only
  intro hmodel
  obtain ⟨hs, _, _, hu⟩ := moved_normalized_remaining_simple_quotient hG T hB hK hBK hTK hm
  let := hs
  let := hK.1.perfect
  exact sporadic_model_remaining_of_not_unique hmodel hu

end CFSG.Quasithin.Chapter1.Section02.MovedMaximality
