module
public import Theory.SpecificGroups.Rudvalis.SylowLowerCentral.Level5
public import Theory.GroupTheory.Commutator.GeneratedNormalBound

/-!
# The sixth lower-central term of the actual Rudvalis Sylow group

The five checked commutator families bound successive lower-central terms.
Each family consists of actual commutators in the preceding term, and its
conjugation certificate proves normality in the original Sylow. The final
three generators generate precisely the marked elementary eight-group.
Thus the sixth term is normalized by max4 and contains the Sylow center.

Source: GLS3 Table 5.3r; Aschbacher--Smith 15.1.22, printed p.1100.
All finite identities are checked on the original ATLAS permutation carrier.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace Rudvalis.SylowLowerCentral
open Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover

private theorem normalized_closure {G I J : Type*} [Group G] [Finite G]
    (a : I → G) (b : J → G)
    (hc : ∀ i j, b j * a i * (b j)⁻¹ ∈ closure (Set.range a)) :
    closure (Set.range b) ≤ normalizer (closure (Set.range a) : Set G) := by
  apply (closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  apply mem_normalizer_fintype
  intro x hx
  have he : closure (Set.range a) ≤ (closure (Set.range a)).comap
      (MulAut.conj (b j)).toMonoidHom := by
    apply (closure_le _).mpr
    rintro _ ⟨i,rfl⟩
    exact hc i j
  exact he hx

private theorem commutator_closures_le_relative {G I J : Type*} [Group G]
    (a : I → G) (b : J → G) (N : Subgroup G)
    (ha : ∀ i, a i ∈ closure (Set.range b))
    (hN : N ≤ closure (Set.range b))
    (hn : closure (Set.range b) ≤ normalizer (N : Set G))
    (hc : ∀ i j, ⁅a i,b j⁆ ∈ N) :
    ⁅closure (Set.range a),closure (Set.range b)⁆ ≤ N := by
  let P := closure (Set.range b)
  let a' : I → P := fun i => ⟨a i,ha i⟩
  let b' : J → P := fun j => ⟨b j,subset_closure ⟨j,rfl⟩⟩
  let : (N.subgroupOf P).Normal := (normal_subgroupOf_iff_le_normalizer hN).mpr hn
  have hh := commutator_closures_le_normal a' b' (N.subgroupOf P)
    (fun i j => hc i j)
  have he (c : I → P) : (closure (Set.range c)).map P.subtype =
      closure (Set.range (fun i => (c i : G))) := by
    rw [MonoidHom.map_closure,←Set.range_comp]
    rfl
  have he' : (closure (Set.range b')).map P.subtype = P := by
    rw [MonoidHom.map_closure,←Set.range_comp]
    rfl
  have hm := map_mono (f := P.subtype) hh
  rw [map_commutator,he,he',map_subgroupOf_eq_of_le hN] at hm
  exact hm
private def H1 : Subgroup Model := closure (Set.range gen1)
private theorem gen1_mem (j : Fin 5) : gen1 j ∈ H1 := subset_closure ⟨j,rfl⟩
private theorem H1_le : H1 ≤ localP := by
  apply (closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (Subgroup.lowerCentralSeries_antitone localP (Nat.zero_le 1)) (gen1_mem_lower j)
private theorem H1_normalizer : localP ≤ normalizer (H1 : Set Model) := by
  apply normalized_closure gen1 localGenerators
  intro j k
  fin_cases j <;> fin_cases k
  · change localGenerators 0 * gen1 0 * (localGenerators 0)⁻¹ ∈ H1
    rw [conjugate1_0_0]
    exact (H1.inv_mem (gen1_mem 0))
  · change localGenerators 1 * gen1 0 * (localGenerators 1)⁻¹ ∈ H1
    rw [conjugate1_0_1]
    exact (H1.mul_mem (H1.mul_mem (gen1_mem 0) (gen1_mem 2)) (gen1_mem 2))
  · change localGenerators 2 * gen1 0 * (localGenerators 2)⁻¹ ∈ H1
    rw [conjugate1_0_2]
    exact (H1.mul_mem (H1.mul_mem (H1.inv_mem (gen1_mem 0)) (H1.inv_mem (gen1_mem 3))) (H1.inv_mem (gen1_mem 3)))
  · change localGenerators 3 * gen1 0 * (localGenerators 3)⁻¹ ∈ H1
    rw [conjugate1_0_3]
    exact (H1.mul_mem (H1.mul_mem (H1.mul_mem (H1.mul_mem (gen1_mem 4) (gen1_mem 4)) (gen1_mem 3)) (gen1_mem 3)) (gen1_mem 0))
  · change localGenerators 0 * gen1 1 * (localGenerators 0)⁻¹ ∈ H1
    rw [conjugate1_1_0]
    exact (H1.inv_mem (gen1_mem 1))
  · change localGenerators 1 * gen1 1 * (localGenerators 1)⁻¹ ∈ H1
    rw [conjugate1_1_1]
    exact (H1.inv_mem (gen1_mem 1))
  · change localGenerators 2 * gen1 1 * (localGenerators 2)⁻¹ ∈ H1
    rw [conjugate1_1_2]
    exact (H1.inv_mem (gen1_mem 1))
  · change localGenerators 3 * gen1 1 * (localGenerators 3)⁻¹ ∈ H1
    rw [conjugate1_1_3]
    exact (H1.mul_mem (H1.mul_mem (H1.mul_mem (H1.inv_mem (gen1_mem 0)) (H1.inv_mem (gen1_mem 2))) (H1.inv_mem (gen1_mem 1))) (H1.inv_mem (gen1_mem 2)))
  · change localGenerators 0 * gen1 2 * (localGenerators 0)⁻¹ ∈ H1
    rw [conjugate1_2_0]
    exact (H1.mul_mem (H1.mul_mem (H1.mul_mem (H1.mul_mem (H1.inv_mem (gen1_mem 0)) (H1.inv_mem (gen1_mem 0))) (H1.inv_mem (gen1_mem 0))) (H1.inv_mem (gen1_mem 2))) (H1.inv_mem (gen1_mem 0)))
  · change localGenerators 1 * gen1 2 * (localGenerators 1)⁻¹ ∈ H1
    rw [conjugate1_2_1]
    exact (H1.inv_mem (gen1_mem 2))
  · change localGenerators 2 * gen1 2 * (localGenerators 2)⁻¹ ∈ H1
    rw [conjugate1_2_2]
    exact (gen1_mem 4)
  · change localGenerators 3 * gen1 2 * (localGenerators 3)⁻¹ ∈ H1
    rw [conjugate1_2_3]
    exact (H1.mul_mem (H1.inv_mem (gen1_mem 0)) (gen1_mem 4))
  · change localGenerators 0 * gen1 3 * (localGenerators 0)⁻¹ ∈ H1
    rw [conjugate1_3_0]
    exact (H1.inv_mem (gen1_mem 3))
  · change localGenerators 1 * gen1 3 * (localGenerators 1)⁻¹ ∈ H1
    rw [conjugate1_3_1]
    exact (H1.mul_mem (H1.mul_mem (H1.mul_mem (H1.mul_mem (H1.mul_mem (H1.inv_mem (gen1_mem 0)) (H1.inv_mem (gen1_mem 0))) (H1.inv_mem (gen1_mem 0))) (gen1_mem 3)) (gen1_mem 4)) (H1.inv_mem (gen1_mem 2)))
  · change localGenerators 2 * gen1 3 * (localGenerators 2)⁻¹ ∈ H1
    rw [conjugate1_3_2]
    exact (H1.inv_mem (gen1_mem 3))
  · change localGenerators 3 * gen1 3 * (localGenerators 3)⁻¹ ∈ H1
    rw [conjugate1_3_3]
    exact (H1.mul_mem (H1.mul_mem (H1.mul_mem (H1.mul_mem (H1.inv_mem (gen1_mem 0)) (H1.inv_mem (gen1_mem 0))) (H1.inv_mem (gen1_mem 3))) (H1.inv_mem (gen1_mem 2))) (gen1_mem 4))
  · change localGenerators 0 * gen1 4 * (localGenerators 0)⁻¹ ∈ H1
    rw [conjugate1_4_0]
    exact (H1.mul_mem (H1.mul_mem (H1.mul_mem (H1.mul_mem (H1.inv_mem (gen1_mem 0)) (H1.inv_mem (gen1_mem 3))) (gen1_mem 4)) (H1.inv_mem (gen1_mem 3))) (H1.inv_mem (gen1_mem 0)))
  · change localGenerators 1 * gen1 4 * (localGenerators 1)⁻¹ ∈ H1
    rw [conjugate1_4_1]
    exact (H1.mul_mem (H1.mul_mem (H1.mul_mem (H1.mul_mem (H1.inv_mem (gen1_mem 0)) (gen1_mem 3)) (H1.inv_mem (gen1_mem 4))) (gen1_mem 3)) (H1.inv_mem (gen1_mem 0)))
  · change localGenerators 2 * gen1 4 * (localGenerators 2)⁻¹ ∈ H1
    rw [conjugate1_4_2]
    exact (gen1_mem 2)
  · change localGenerators 3 * gen1 4 * (localGenerators 3)⁻¹ ∈ H1
    rw [conjugate1_4_3]
    exact (H1.mul_mem (H1.mul_mem (H1.mul_mem (H1.inv_mem (gen1_mem 0)) (gen1_mem 3)) (gen1_mem 2)) (gen1_mem 3))

private theorem step1 : ⁅localP,localP⁆ ≤ H1 := by
  apply commutator_closures_le_relative localGenerators localGenerators H1
  · intro j
    exact localGenerators_mem j
  · exact H1_le
  · exact H1_normalizer
  · intro j k
    fin_cases j <;> fin_cases k
    · change ⁅localGenerators 0,localGenerators 0⁆ ∈ H1
      rw [commutator1_0_0]
      exact H1.one_mem
    · change ⁅localGenerators 0,localGenerators 1⁆ ∈ H1
      rw [commutator1_0_1]
      exact H1.one_mem
    · change ⁅localGenerators 0,localGenerators 2⁆ ∈ H1
      rw [commutator1_0_2]
      exact H1.one_mem
    · change ⁅localGenerators 0,localGenerators 3⁆ ∈ H1
      rw [commutator1_0_3]
      exact (gen1_mem 0)
    · change ⁅localGenerators 1,localGenerators 0⁆ ∈ H1
      rw [commutator1_1_0]
      exact H1.one_mem
    · change ⁅localGenerators 1,localGenerators 1⁆ ∈ H1
      rw [commutator1_1_1]
      exact H1.one_mem
    · change ⁅localGenerators 1,localGenerators 2⁆ ∈ H1
      rw [commutator1_1_2]
      exact (H1.inv_mem (gen1_mem 1))
    · change ⁅localGenerators 1,localGenerators 3⁆ ∈ H1
      rw [commutator1_1_3]
      exact (gen1_mem 2)
    · change ⁅localGenerators 2,localGenerators 0⁆ ∈ H1
      rw [commutator1_2_0]
      exact H1.one_mem
    · change ⁅localGenerators 2,localGenerators 1⁆ ∈ H1
      rw [commutator1_2_1]
      exact (H1.inv_mem (gen1_mem 1))
    · change ⁅localGenerators 2,localGenerators 2⁆ ∈ H1
      rw [commutator1_2_2]
      exact H1.one_mem
    · change ⁅localGenerators 2,localGenerators 3⁆ ∈ H1
      rw [commutator1_2_3]
      exact (gen1_mem 3)
    · change ⁅localGenerators 3,localGenerators 0⁆ ∈ H1
      rw [commutator1_3_0]
      exact (H1.inv_mem (gen1_mem 0))
    · change ⁅localGenerators 3,localGenerators 1⁆ ∈ H1
      rw [commutator1_3_1]
      exact (H1.inv_mem (gen1_mem 2))
    · change ⁅localGenerators 3,localGenerators 2⁆ ∈ H1
      rw [commutator1_3_2]
      exact (H1.inv_mem (gen1_mem 3))
    · change ⁅localGenerators 3,localGenerators 3⁆ ∈ H1
      rw [commutator1_3_3]
      exact H1.one_mem

private def H2 : Subgroup Model := closure (Set.range gen2)
private theorem gen2_mem (j : Fin 5) : gen2 j ∈ H2 := subset_closure ⟨j,rfl⟩
private theorem H2_le : H2 ≤ localP := by
  apply (closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (Subgroup.lowerCentralSeries_antitone localP (Nat.zero_le 2)) (gen2_mem_lower j)
private theorem H2_normalizer : localP ≤ normalizer (H2 : Set Model) := by
  apply normalized_closure gen2 localGenerators
  intro j k
  fin_cases j <;> fin_cases k
  · change localGenerators 0 * gen2 0 * (localGenerators 0)⁻¹ ∈ H2
    rw [conjugate2_0_0]
    exact (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 1)) (gen2_mem 0)) (gen2_mem 1))
  · change localGenerators 1 * gen2 0 * (localGenerators 1)⁻¹ ∈ H2
    rw [conjugate2_0_1]
    exact (H2.inv_mem (gen2_mem 0))
  · change localGenerators 2 * gen2 0 * (localGenerators 2)⁻¹ ∈ H2
    rw [conjugate2_0_2]
    exact (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 3)) (H2.inv_mem (gen2_mem 3))) (H2.inv_mem (gen2_mem 1))) (H2.inv_mem (gen2_mem 2)))
  · change localGenerators 3 * gen2 0 * (localGenerators 3)⁻¹ ∈ H2
    rw [conjugate2_0_3]
    exact (H2.mul_mem (H2.inv_mem (gen2_mem 1)) (gen2_mem 2))
  · change localGenerators 0 * gen2 1 * (localGenerators 0)⁻¹ ∈ H2
    rw [conjugate2_1_0]
    exact (H2.inv_mem (gen2_mem 1))
  · change localGenerators 1 * gen2 1 * (localGenerators 1)⁻¹ ∈ H2
    rw [conjugate2_1_1]
    exact (H2.mul_mem (gen2_mem 2) (H2.inv_mem (gen2_mem 0)))
  · change localGenerators 2 * gen2 1 * (localGenerators 2)⁻¹ ∈ H2
    rw [conjugate2_1_2]
    exact (H2.inv_mem (gen2_mem 1))
  · change localGenerators 3 * gen2 1 * (localGenerators 3)⁻¹ ∈ H2
    rw [conjugate2_1_3]
    exact (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 3)) (H2.inv_mem (gen2_mem 3))) (H2.inv_mem (gen2_mem 3))) (gen2_mem 2)) (H2.inv_mem (gen2_mem 0))) (H2.inv_mem (gen2_mem 4))) (H2.inv_mem (gen2_mem 3))) (H2.inv_mem (gen2_mem 4)))
  · change localGenerators 0 * gen2 2 * (localGenerators 0)⁻¹ ∈ H2
    rw [conjugate2_2_0]
    exact (H2.inv_mem (gen2_mem 2))
  · change localGenerators 1 * gen2 2 * (localGenerators 1)⁻¹ ∈ H2
    rw [conjugate2_2_1]
    exact (H2.mul_mem (H2.inv_mem (gen2_mem 1)) (H2.inv_mem (gen2_mem 0)))
  · change localGenerators 2 * gen2 2 * (localGenerators 2)⁻¹ ∈ H2
    rw [conjugate2_2_2]
    exact (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 3)) (H2.inv_mem (gen2_mem 3))) (gen2_mem 0)) (gen2_mem 1))
  · change localGenerators 3 * gen2 2 * (localGenerators 3)⁻¹ ∈ H2
    rw [conjugate2_2_3]
    exact (H2.inv_mem (gen2_mem 2))
  · change localGenerators 0 * gen2 3 * (localGenerators 0)⁻¹ ∈ H2
    rw [conjugate2_3_0]
    exact (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 3)) (H2.inv_mem (gen2_mem 2))) (H2.inv_mem (gen2_mem 2)))
  · change localGenerators 1 * gen2 3 * (localGenerators 1)⁻¹ ∈ H2
    rw [conjugate2_3_1]
    exact (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 3)) (H2.inv_mem (gen2_mem 3))) (H2.inv_mem (gen2_mem 3))) (H2.inv_mem (gen2_mem 0)))
  · change localGenerators 2 * gen2 3 * (localGenerators 2)⁻¹ ∈ H2
    rw [conjugate2_3_2]
    exact (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 3)) (H2.inv_mem (gen2_mem 1))) (H2.inv_mem (gen2_mem 2))) (H2.inv_mem (gen2_mem 2)))
  · change localGenerators 3 * gen2 3 * (localGenerators 3)⁻¹ ∈ H2
    rw [conjugate2_3_3]
    exact (H2.mul_mem (H2.inv_mem (gen2_mem 3)) (gen2_mem 2))
  · change localGenerators 0 * gen2 4 * (localGenerators 0)⁻¹ ∈ H2
    rw [conjugate2_4_0]
    exact (H2.mul_mem (H2.mul_mem (H2.mul_mem (gen2_mem 4) (gen2_mem 0)) (H2.inv_mem (gen2_mem 2))) (gen2_mem 1))
  · change localGenerators 1 * gen2 4 * (localGenerators 1)⁻¹ ∈ H2
    rw [conjugate2_4_1]
    exact (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 3)) (H2.inv_mem (gen2_mem 4))) (H2.inv_mem (gen2_mem 3))) (H2.inv_mem (gen2_mem 0)))
  · change localGenerators 2 * gen2 4 * (localGenerators 2)⁻¹ ∈ H2
    rw [conjugate2_4_2]
    exact (H2.inv_mem (gen2_mem 4))
  · change localGenerators 3 * gen2 4 * (localGenerators 3)⁻¹ ∈ H2
    rw [conjugate2_4_3]
    exact (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 3)) (H2.inv_mem (gen2_mem 3))) (gen2_mem 0)) (gen2_mem 4))

private theorem step2 : ⁅H1,localP⁆ ≤ H2 := by
  apply commutator_closures_le_relative gen1 localGenerators H2
  · intro j
    exact H1_le (gen1_mem j)
  · exact H2_le
  · exact H2_normalizer
  · intro j k
    fin_cases j <;> fin_cases k
    · change ⁅gen1 0,localGenerators 0⁆ ∈ H2
      rw [commutator2_0_0]
      exact (H2.mul_mem (H2.inv_mem (gen2_mem 3)) (H2.inv_mem (gen2_mem 3)))
    · change ⁅gen1 0,localGenerators 1⁆ ∈ H2
      rw [commutator2_0_1]
      exact (H2.inv_mem (gen2_mem 0))
    · change ⁅gen1 0,localGenerators 2⁆ ∈ H2
      rw [commutator2_0_2]
      exact (H2.inv_mem (gen2_mem 1))
    · change ⁅gen1 0,localGenerators 3⁆ ∈ H2
      rw [commutator2_0_3]
      exact (gen2_mem 2)
    · change ⁅gen1 1,localGenerators 0⁆ ∈ H2
      rw [commutator2_1_0]
      exact H2.one_mem
    · change ⁅gen1 1,localGenerators 1⁆ ∈ H2
      rw [commutator2_1_1]
      exact H2.one_mem
    · change ⁅gen1 1,localGenerators 2⁆ ∈ H2
      rw [commutator2_1_2]
      exact H2.one_mem
    · change ⁅gen1 1,localGenerators 3⁆ ∈ H2
      rw [commutator2_1_3]
      exact (gen2_mem 3)
    · change ⁅gen1 2,localGenerators 0⁆ ∈ H2
      rw [commutator2_2_0]
      exact (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 3)) (H2.inv_mem (gen2_mem 3))) (H2.inv_mem (gen2_mem 3))) (H2.inv_mem (gen2_mem 4))) (H2.inv_mem (gen2_mem 3))) (H2.inv_mem (gen2_mem 0))) (H2.inv_mem (gen2_mem 4)))
    · change ⁅gen1 2,localGenerators 1⁆ ∈ H2
      rw [commutator2_2_1]
      exact (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 1)) (gen2_mem 0)) (gen2_mem 1))
    · change ⁅gen1 2,localGenerators 2⁆ ∈ H2
      rw [commutator2_2_2]
      exact (gen2_mem 4)
    · change ⁅gen1 2,localGenerators 3⁆ ∈ H2
      rw [commutator2_2_3]
      exact (H2.mul_mem (gen2_mem 3) (gen2_mem 4))
    · change ⁅gen1 3,localGenerators 0⁆ ∈ H2
      rw [commutator2_3_0]
      exact (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 3)) (H2.inv_mem (gen2_mem 3))) (H2.inv_mem (gen2_mem 1)))
    · change ⁅gen1 3,localGenerators 1⁆ ∈ H2
      rw [commutator2_3_1]
      exact (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 1)) (H2.inv_mem (gen2_mem 4))) (H2.inv_mem (gen2_mem 0))) (H2.inv_mem (gen2_mem 2))) (H2.inv_mem (gen2_mem 3)))
    · change ⁅gen1 3,localGenerators 2⁆ ∈ H2
      rw [commutator2_3_2]
      exact (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 3)) (H2.inv_mem (gen2_mem 3))) (H2.inv_mem (gen2_mem 1)))
    · change ⁅gen1 3,localGenerators 3⁆ ∈ H2
      rw [commutator2_3_3]
      exact (H2.mul_mem (H2.mul_mem (H2.mul_mem (gen2_mem 3) (gen2_mem 4)) (gen2_mem 1)) (gen2_mem 3))
    · change ⁅gen1 4,localGenerators 0⁆ ∈ H2
      rw [commutator2_4_0]
      exact (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 3)) (H2.inv_mem (gen2_mem 1))) (H2.inv_mem (gen2_mem 4))) (H2.inv_mem (gen2_mem 2))) (H2.inv_mem (gen2_mem 3))) (H2.inv_mem (gen2_mem 4)))
    · change ⁅gen1 4,localGenerators 1⁆ ∈ H2
      rw [commutator2_4_1]
      exact (H2.mul_mem (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 3)) (gen2_mem 4)) (H2.inv_mem (gen2_mem 3))) (H2.inv_mem (gen2_mem 4)))
    · change ⁅gen1 4,localGenerators 2⁆ ∈ H2
      rw [commutator2_4_2]
      exact (H2.inv_mem (gen2_mem 4))
    · change ⁅gen1 4,localGenerators 3⁆ ∈ H2
      rw [commutator2_4_3]
      exact (H2.mul_mem (H2.mul_mem (H2.inv_mem (gen2_mem 4)) (H2.inv_mem (gen2_mem 0))) (H2.inv_mem (gen2_mem 3)))

private def H3 : Subgroup Model := closure (Set.range gen3)
private theorem gen3_mem (j : Fin 5) : gen3 j ∈ H3 := subset_closure ⟨j,rfl⟩
private theorem H3_le : H3 ≤ localP := by
  apply (closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (Subgroup.lowerCentralSeries_antitone localP (Nat.zero_le 3)) (gen3_mem_lower j)
private theorem H3_normalizer : localP ≤ normalizer (H3 : Set Model) := by
  apply normalized_closure gen3 localGenerators
  intro j k
  fin_cases j <;> fin_cases k
  · change localGenerators 0 * gen3 0 * (localGenerators 0)⁻¹ ∈ H3
    rw [conjugate3_0_0]
    exact (H3.inv_mem (gen3_mem 0))
  · change localGenerators 1 * gen3 0 * (localGenerators 1)⁻¹ ∈ H3
    rw [conjugate3_0_1]
    exact (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 4)) (H3.inv_mem (gen3_mem 0))) (H3.inv_mem (gen3_mem 3))) (H3.inv_mem (gen3_mem 4))) (H3.inv_mem (gen3_mem 3)))
  · change localGenerators 2 * gen3 0 * (localGenerators 2)⁻¹ ∈ H3
    rw [conjugate3_0_2]
    exact (H3.inv_mem (gen3_mem 0))
  · change localGenerators 3 * gen3 0 * (localGenerators 3)⁻¹ ∈ H3
    rw [conjugate3_0_3]
    exact (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 0)) (H3.inv_mem (gen3_mem 1))) (H3.inv_mem (gen3_mem 2)))
  · change localGenerators 0 * gen3 1 * (localGenerators 0)⁻¹ ∈ H3
    rw [conjugate3_1_0]
    exact (H3.inv_mem (gen3_mem 1))
  · change localGenerators 1 * gen3 1 * (localGenerators 1)⁻¹ ∈ H3
    rw [conjugate3_1_1]
    exact (H3.inv_mem (gen3_mem 1))
  · change localGenerators 2 * gen3 1 * (localGenerators 2)⁻¹ ∈ H3
    rw [conjugate3_1_2]
    exact (H3.inv_mem (gen3_mem 1))
  · change localGenerators 3 * gen3 1 * (localGenerators 3)⁻¹ ∈ H3
    rw [conjugate3_1_3]
    exact (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 4)) (H3.inv_mem (gen3_mem 2))) (H3.inv_mem (gen3_mem 3))) (H3.inv_mem (gen3_mem 4))) (H3.inv_mem (gen3_mem 3)))
  · change localGenerators 0 * gen3 2 * (localGenerators 0)⁻¹ ∈ H3
    rw [conjugate3_2_0]
    exact (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 4)) (H3.inv_mem (gen3_mem 2))) (H3.inv_mem (gen3_mem 3))) (H3.inv_mem (gen3_mem 4))) (H3.inv_mem (gen3_mem 3)))
  · change localGenerators 1 * gen3 2 * (localGenerators 1)⁻¹ ∈ H3
    rw [conjugate3_2_1]
    exact (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 4)) (H3.inv_mem (gen3_mem 2))) (H3.inv_mem (gen3_mem 3))) (H3.inv_mem (gen3_mem 4))) (H3.inv_mem (gen3_mem 3)))
  · change localGenerators 2 * gen3 2 * (localGenerators 2)⁻¹ ∈ H3
    rw [conjugate3_2_2]
    exact (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 0)) (H3.inv_mem (gen3_mem 1))) (H3.inv_mem (gen3_mem 2)))
  · change localGenerators 3 * gen3 2 * (localGenerators 3)⁻¹ ∈ H3
    rw [conjugate3_2_3]
    exact (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 4)) (H3.inv_mem (gen3_mem 0))) (H3.inv_mem (gen3_mem 3))) (H3.inv_mem (gen3_mem 4))) (H3.inv_mem (gen3_mem 3)))
  · change localGenerators 0 * gen3 3 * (localGenerators 0)⁻¹ ∈ H3
    rw [conjugate3_3_0]
    exact (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 4)) (H3.inv_mem (gen3_mem 3))) (H3.inv_mem (gen3_mem 4)))
  · change localGenerators 1 * gen3 3 * (localGenerators 1)⁻¹ ∈ H3
    rw [conjugate3_3_1]
    exact (H3.inv_mem (gen3_mem 3))
  · change localGenerators 2 * gen3 3 * (localGenerators 2)⁻¹ ∈ H3
    rw [conjugate3_3_2]
    exact (H3.mul_mem (H3.inv_mem (gen3_mem 0)) (H3.inv_mem (gen3_mem 3)))
  · change localGenerators 3 * gen3 3 * (localGenerators 3)⁻¹ ∈ H3
    rw [conjugate3_3_3]
    exact (H3.mul_mem (H3.inv_mem (gen3_mem 1)) (H3.inv_mem (gen3_mem 3)))
  · change localGenerators 0 * gen3 4 * (localGenerators 0)⁻¹ ∈ H3
    rw [conjugate3_4_0]
    exact (H3.inv_mem (gen3_mem 4))
  · change localGenerators 1 * gen3 4 * (localGenerators 1)⁻¹ ∈ H3
    rw [conjugate3_4_1]
    exact (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 1)) (H3.inv_mem (gen3_mem 3))) (H3.inv_mem (gen3_mem 4))) (H3.inv_mem (gen3_mem 3)))
  · change localGenerators 2 * gen3 4 * (localGenerators 2)⁻¹ ∈ H3
    rw [conjugate3_4_2]
    exact (H3.inv_mem (gen3_mem 4))
  · change localGenerators 3 * gen3 4 * (localGenerators 3)⁻¹ ∈ H3
    rw [conjugate3_4_3]
    exact (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 2)) (H3.inv_mem (gen3_mem 3))) (H3.inv_mem (gen3_mem 4))) (H3.inv_mem (gen3_mem 3)))

private theorem step3 : ⁅H2,localP⁆ ≤ H3 := by
  apply commutator_closures_le_relative gen2 localGenerators H3
  · intro j
    exact H2_le (gen2_mem j)
  · exact H3_le
  · exact H3_normalizer
  · intro j k
    fin_cases j <;> fin_cases k
    · change ⁅gen2 0,localGenerators 0⁆ ∈ H3
      rw [commutator3_0_0]
      exact (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 4)) (H3.inv_mem (gen3_mem 3))) (H3.inv_mem (gen3_mem 4))) (H3.inv_mem (gen3_mem 3)))
    · change ⁅gen2 0,localGenerators 1⁆ ∈ H3
      rw [commutator3_0_1]
      exact H3.one_mem
    · change ⁅gen2 0,localGenerators 2⁆ ∈ H3
      rw [commutator3_0_2]
      exact (H3.inv_mem (gen3_mem 0))
    · change ⁅gen2 0,localGenerators 3⁆ ∈ H3
      rw [commutator3_0_3]
      exact (H3.inv_mem (gen3_mem 1))
    · change ⁅gen2 1,localGenerators 0⁆ ∈ H3
      rw [commutator3_1_0]
      exact H3.one_mem
    · change ⁅gen2 1,localGenerators 1⁆ ∈ H3
      rw [commutator3_1_1]
      exact (H3.inv_mem (gen3_mem 1))
    · change ⁅gen2 1,localGenerators 2⁆ ∈ H3
      rw [commutator3_1_2]
      exact H3.one_mem
    · change ⁅gen2 1,localGenerators 3⁆ ∈ H3
      rw [commutator3_1_3]
      exact (H3.inv_mem (gen3_mem 2))
    · change ⁅gen2 2,localGenerators 0⁆ ∈ H3
      rw [commutator3_2_0]
      exact (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 4)) (H3.inv_mem (gen3_mem 3))) (H3.inv_mem (gen3_mem 4))) (H3.inv_mem (gen3_mem 3)))
    · change ⁅gen2 2,localGenerators 1⁆ ∈ H3
      rw [commutator3_2_1]
      exact (H3.inv_mem (gen3_mem 1))
    · change ⁅gen2 2,localGenerators 2⁆ ∈ H3
      rw [commutator3_2_2]
      exact (H3.inv_mem (gen3_mem 0))
    · change ⁅gen2 2,localGenerators 3⁆ ∈ H3
      rw [commutator3_2_3]
      exact (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 4)) (H3.inv_mem (gen3_mem 3))) (H3.inv_mem (gen3_mem 4))) (H3.inv_mem (gen3_mem 3)))
    · change ⁅gen2 3,localGenerators 0⁆ ∈ H3
      rw [commutator3_3_0]
      exact (H3.mul_mem (H3.inv_mem (gen3_mem 0)) (H3.inv_mem (gen3_mem 1)))
    · change ⁅gen2 3,localGenerators 1⁆ ∈ H3
      rw [commutator3_3_1]
      exact (H3.inv_mem (gen3_mem 3))
    · change ⁅gen2 3,localGenerators 2⁆ ∈ H3
      rw [commutator3_3_2]
      exact (H3.inv_mem (gen3_mem 4))
    · change ⁅gen2 3,localGenerators 3⁆ ∈ H3
      rw [commutator3_3_3]
      exact (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 1)) (H3.inv_mem (gen3_mem 3))) (H3.inv_mem (gen3_mem 4)))
    · change ⁅gen2 4,localGenerators 0⁆ ∈ H3
      rw [commutator3_4_0]
      exact (H3.inv_mem (gen3_mem 1))
    · change ⁅gen2 4,localGenerators 1⁆ ∈ H3
      rw [commutator3_4_1]
      exact (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 4)) (H3.inv_mem (gen3_mem 0))) (H3.inv_mem (gen3_mem 2))) (H3.inv_mem (gen3_mem 3))) (H3.inv_mem (gen3_mem 4)))
    · change ⁅gen2 4,localGenerators 2⁆ ∈ H3
      rw [commutator3_4_2]
      exact (H3.mul_mem (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 4)) (H3.inv_mem (gen3_mem 3))) (H3.inv_mem (gen3_mem 4))) (H3.inv_mem (gen3_mem 3)))
    · change ⁅gen2 4,localGenerators 3⁆ ∈ H3
      rw [commutator3_4_3]
      exact (H3.mul_mem (H3.mul_mem (H3.inv_mem (gen3_mem 0)) (H3.inv_mem (gen3_mem 1))) (H3.inv_mem (gen3_mem 3)))

private def H4 : Subgroup Model := closure (Set.range gen4)
private theorem gen4_mem (j : Fin 4) : gen4 j ∈ H4 := subset_closure ⟨j,rfl⟩
private theorem H4_le : H4 ≤ localP := by
  apply (closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (Subgroup.lowerCentralSeries_antitone localP (Nat.zero_le 4)) (gen4_mem_lower j)
private theorem H4_normalizer : localP ≤ normalizer (H4 : Set Model) := by
  apply normalized_closure gen4 localGenerators
  intro j k
  fin_cases j <;> fin_cases k
  · change localGenerators 0 * gen4 0 * (localGenerators 0)⁻¹ ∈ H4
    rw [conjugate4_0_0]
    exact (H4.inv_mem (gen4_mem 0))
  · change localGenerators 1 * gen4 0 * (localGenerators 1)⁻¹ ∈ H4
    rw [conjugate4_0_1]
    exact (H4.inv_mem (gen4_mem 0))
  · change localGenerators 2 * gen4 0 * (localGenerators 2)⁻¹ ∈ H4
    rw [conjugate4_0_2]
    exact (H4.inv_mem (gen4_mem 0))
  · change localGenerators 3 * gen4 0 * (localGenerators 3)⁻¹ ∈ H4
    rw [conjugate4_0_3]
    exact (H4.inv_mem (gen4_mem 0))
  · change localGenerators 0 * gen4 1 * (localGenerators 0)⁻¹ ∈ H4
    rw [conjugate4_1_0]
    exact (H4.mul_mem (H4.inv_mem (gen4_mem 1)) (H4.inv_mem (gen4_mem 0)))
  · change localGenerators 1 * gen4 1 * (localGenerators 1)⁻¹ ∈ H4
    rw [conjugate4_1_1]
    exact (H4.mul_mem (H4.inv_mem (gen4_mem 1)) (H4.inv_mem (gen4_mem 0)))
  · change localGenerators 2 * gen4 1 * (localGenerators 2)⁻¹ ∈ H4
    rw [conjugate4_1_2]
    exact (H4.mul_mem (H4.inv_mem (gen4_mem 1)) (H4.inv_mem (gen4_mem 2)))
  · change localGenerators 3 * gen4 1 * (localGenerators 3)⁻¹ ∈ H4
    rw [conjugate4_1_3]
    exact (H4.mul_mem (H4.inv_mem (gen4_mem 1)) (H4.inv_mem (gen4_mem 2)))
  · change localGenerators 0 * gen4 2 * (localGenerators 0)⁻¹ ∈ H4
    rw [conjugate4_2_0]
    exact (H4.inv_mem (gen4_mem 2))
  · change localGenerators 1 * gen4 2 * (localGenerators 1)⁻¹ ∈ H4
    rw [conjugate4_2_1]
    exact (H4.mul_mem (H4.inv_mem (gen4_mem 0)) (H4.inv_mem (gen4_mem 2)))
  · change localGenerators 2 * gen4 2 * (localGenerators 2)⁻¹ ∈ H4
    rw [conjugate4_2_2]
    exact (H4.inv_mem (gen4_mem 2))
  · change localGenerators 3 * gen4 2 * (localGenerators 3)⁻¹ ∈ H4
    rw [conjugate4_2_3]
    exact (H4.mul_mem (H4.inv_mem (gen4_mem 0)) (H4.inv_mem (gen4_mem 2)))
  · change localGenerators 0 * gen4 3 * (localGenerators 0)⁻¹ ∈ H4
    rw [conjugate4_3_0]
    exact (H4.inv_mem (gen4_mem 3))
  · change localGenerators 1 * gen4 3 * (localGenerators 1)⁻¹ ∈ H4
    rw [conjugate4_3_1]
    exact (H4.mul_mem (H4.inv_mem (gen4_mem 0)) (H4.inv_mem (gen4_mem 3)))
  · change localGenerators 2 * gen4 3 * (localGenerators 2)⁻¹ ∈ H4
    rw [conjugate4_3_2]
    exact (H4.inv_mem (gen4_mem 3))
  · change localGenerators 3 * gen4 3 * (localGenerators 3)⁻¹ ∈ H4
    rw [conjugate4_3_3]
    exact (H4.mul_mem (H4.inv_mem (gen4_mem 1)) (H4.inv_mem (gen4_mem 3)))

private theorem step4 : ⁅H3,localP⁆ ≤ H4 := by
  apply commutator_closures_le_relative gen3 localGenerators H4
  · intro j
    exact H3_le (gen3_mem j)
  · exact H4_le
  · exact H4_normalizer
  · intro j k
    fin_cases j <;> fin_cases k
    · change ⁅gen3 0,localGenerators 0⁆ ∈ H4
      rw [commutator4_0_0]
      exact H4.one_mem
    · change ⁅gen3 0,localGenerators 1⁆ ∈ H4
      rw [commutator4_0_1]
      exact (H4.inv_mem (gen4_mem 0))
    · change ⁅gen3 0,localGenerators 2⁆ ∈ H4
      rw [commutator4_0_2]
      exact H4.one_mem
    · change ⁅gen3 0,localGenerators 3⁆ ∈ H4
      rw [commutator4_0_3]
      exact (H4.inv_mem (gen4_mem 1))
    · change ⁅gen3 1,localGenerators 0⁆ ∈ H4
      rw [commutator4_1_0]
      exact H4.one_mem
    · change ⁅gen3 1,localGenerators 1⁆ ∈ H4
      rw [commutator4_1_1]
      exact H4.one_mem
    · change ⁅gen3 1,localGenerators 2⁆ ∈ H4
      rw [commutator4_1_2]
      exact H4.one_mem
    · change ⁅gen3 1,localGenerators 3⁆ ∈ H4
      rw [commutator4_1_3]
      exact (H4.mul_mem (H4.inv_mem (gen4_mem 1)) (H4.inv_mem (gen4_mem 0)))
    · change ⁅gen3 2,localGenerators 0⁆ ∈ H4
      rw [commutator4_2_0]
      exact (H4.inv_mem (gen4_mem 0))
    · change ⁅gen3 2,localGenerators 1⁆ ∈ H4
      rw [commutator4_2_1]
      exact (H4.inv_mem (gen4_mem 0))
    · change ⁅gen3 2,localGenerators 2⁆ ∈ H4
      rw [commutator4_2_2]
      exact (H4.inv_mem (gen4_mem 2))
    · change ⁅gen3 2,localGenerators 3⁆ ∈ H4
      rw [commutator4_2_3]
      exact (H4.mul_mem (H4.mul_mem (H4.inv_mem (gen4_mem 1)) (H4.inv_mem (gen4_mem 0))) (H4.inv_mem (gen4_mem 2)))
    · change ⁅gen3 3,localGenerators 0⁆ ∈ H4
      rw [commutator4_3_0]
      exact (H4.inv_mem (gen4_mem 0))
    · change ⁅gen3 3,localGenerators 1⁆ ∈ H4
      rw [commutator4_3_1]
      exact H4.one_mem
    · change ⁅gen3 3,localGenerators 2⁆ ∈ H4
      rw [commutator4_3_2]
      exact (H4.inv_mem (gen4_mem 3))
    · change ⁅gen3 3,localGenerators 3⁆ ∈ H4
      rw [commutator4_3_3]
      exact (H4.mul_mem (H4.inv_mem (gen4_mem 2)) (H4.inv_mem (gen4_mem 3)))
    · change ⁅gen3 4,localGenerators 0⁆ ∈ H4
      rw [commutator4_4_0]
      exact H4.one_mem
    · change ⁅gen3 4,localGenerators 1⁆ ∈ H4
      rw [commutator4_4_1]
      exact (H4.mul_mem (H4.mul_mem (H4.inv_mem (gen4_mem 0)) (H4.inv_mem (gen4_mem 2))) (H4.inv_mem (gen4_mem 3)))
    · change ⁅gen3 4,localGenerators 2⁆ ∈ H4
      rw [commutator4_4_2]
      exact H4.one_mem
    · change ⁅gen3 4,localGenerators 3⁆ ∈ H4
      rw [commutator4_4_3]
      exact (H4.mul_mem (H4.mul_mem (H4.mul_mem (H4.inv_mem (gen4_mem 1)) (H4.inv_mem (gen4_mem 0))) (H4.inv_mem (gen4_mem 2))) (H4.inv_mem (gen4_mem 3)))

private def H5 : Subgroup Model := closure (Set.range gen5)
private theorem gen5_mem (j : Fin 3) : gen5 j ∈ H5 := subset_closure ⟨j,rfl⟩
private theorem H5_le : H5 ≤ localP := by
  apply (closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  exact (Subgroup.lowerCentralSeries_antitone localP (Nat.zero_le 5)) (gen5_mem_lower j)
private theorem H5_normalizer : localP ≤ normalizer (H5 : Set Model) := by
  apply normalized_closure gen5 localGenerators
  intro j k
  fin_cases j <;> fin_cases k
  · change localGenerators 0 * gen5 0 * (localGenerators 0)⁻¹ ∈ H5
    rw [conjugate5_0_0]
    exact (H5.inv_mem (gen5_mem 0))
  · change localGenerators 1 * gen5 0 * (localGenerators 1)⁻¹ ∈ H5
    rw [conjugate5_0_1]
    exact (H5.inv_mem (gen5_mem 0))
  · change localGenerators 2 * gen5 0 * (localGenerators 2)⁻¹ ∈ H5
    rw [conjugate5_0_2]
    exact (H5.inv_mem (gen5_mem 0))
  · change localGenerators 3 * gen5 0 * (localGenerators 3)⁻¹ ∈ H5
    rw [conjugate5_0_3]
    exact (H5.inv_mem (gen5_mem 0))
  · change localGenerators 0 * gen5 1 * (localGenerators 0)⁻¹ ∈ H5
    rw [conjugate5_1_0]
    exact (H5.inv_mem (gen5_mem 1))
  · change localGenerators 1 * gen5 1 * (localGenerators 1)⁻¹ ∈ H5
    rw [conjugate5_1_1]
    exact (H5.mul_mem (H5.inv_mem (gen5_mem 0)) (H5.inv_mem (gen5_mem 1)))
  · change localGenerators 2 * gen5 1 * (localGenerators 2)⁻¹ ∈ H5
    rw [conjugate5_1_2]
    exact (H5.inv_mem (gen5_mem 1))
  · change localGenerators 3 * gen5 1 * (localGenerators 3)⁻¹ ∈ H5
    rw [conjugate5_1_3]
    exact (H5.mul_mem (H5.inv_mem (gen5_mem 0)) (H5.inv_mem (gen5_mem 1)))
  · change localGenerators 0 * gen5 2 * (localGenerators 0)⁻¹ ∈ H5
    rw [conjugate5_2_0]
    exact (H5.mul_mem (H5.inv_mem (gen5_mem 0)) (H5.inv_mem (gen5_mem 2)))
  · change localGenerators 1 * gen5 2 * (localGenerators 1)⁻¹ ∈ H5
    rw [conjugate5_2_1]
    exact (H5.mul_mem (H5.inv_mem (gen5_mem 0)) (H5.inv_mem (gen5_mem 2)))
  · change localGenerators 2 * gen5 2 * (localGenerators 2)⁻¹ ∈ H5
    rw [conjugate5_2_2]
    exact (H5.mul_mem (H5.inv_mem (gen5_mem 1)) (H5.inv_mem (gen5_mem 2)))
  · change localGenerators 3 * gen5 2 * (localGenerators 3)⁻¹ ∈ H5
    rw [conjugate5_2_3]
    exact (H5.mul_mem (H5.inv_mem (gen5_mem 1)) (H5.inv_mem (gen5_mem 2)))

private theorem step5 : ⁅H4,localP⁆ ≤ H5 := by
  apply commutator_closures_le_relative gen4 localGenerators H5
  · intro j
    exact H4_le (gen4_mem j)
  · exact H5_le
  · exact H5_normalizer
  · intro j k
    fin_cases j <;> fin_cases k
    · change ⁅gen4 0,localGenerators 0⁆ ∈ H5
      rw [commutator5_0_0]
      exact H5.one_mem
    · change ⁅gen4 0,localGenerators 1⁆ ∈ H5
      rw [commutator5_0_1]
      exact H5.one_mem
    · change ⁅gen4 0,localGenerators 2⁆ ∈ H5
      rw [commutator5_0_2]
      exact H5.one_mem
    · change ⁅gen4 0,localGenerators 3⁆ ∈ H5
      rw [commutator5_0_3]
      exact H5.one_mem
    · change ⁅gen4 1,localGenerators 0⁆ ∈ H5
      rw [commutator5_1_0]
      exact (H5.inv_mem (gen5_mem 0))
    · change ⁅gen4 1,localGenerators 1⁆ ∈ H5
      rw [commutator5_1_1]
      exact (H5.inv_mem (gen5_mem 0))
    · change ⁅gen4 1,localGenerators 2⁆ ∈ H5
      rw [commutator5_1_2]
      exact (H5.inv_mem (gen5_mem 1))
    · change ⁅gen4 1,localGenerators 3⁆ ∈ H5
      rw [commutator5_1_3]
      exact (H5.inv_mem (gen5_mem 1))
    · change ⁅gen4 2,localGenerators 0⁆ ∈ H5
      rw [commutator5_2_0]
      exact H5.one_mem
    · change ⁅gen4 2,localGenerators 1⁆ ∈ H5
      rw [commutator5_2_1]
      exact (H5.inv_mem (gen5_mem 0))
    · change ⁅gen4 2,localGenerators 2⁆ ∈ H5
      rw [commutator5_2_2]
      exact H5.one_mem
    · change ⁅gen4 2,localGenerators 3⁆ ∈ H5
      rw [commutator5_2_3]
      exact (H5.inv_mem (gen5_mem 0))
    · change ⁅gen4 3,localGenerators 0⁆ ∈ H5
      rw [commutator5_3_0]
      exact H5.one_mem
    · change ⁅gen4 3,localGenerators 1⁆ ∈ H5
      rw [commutator5_3_1]
      exact (H5.inv_mem (gen5_mem 0))
    · change ⁅gen4 3,localGenerators 2⁆ ∈ H5
      rw [commutator5_3_2]
      exact H5.one_mem
    · change ⁅gen4 3,localGenerators 3⁆ ∈ H5
      rw [commutator5_3_3]
      exact (H5.inv_mem (gen5_mem 2))

private theorem last_in_eight0 : gen5 0 = (RankOneEightCharacteristic.basis 0)⁻¹ := by
  have he : perm5 0 = (CatalogueCertificate.elementaryPermutation 0)⁻¹ := by
    apply Equiv.ext
    apply Rudvalis.OrderCertificate.allFin
    decide +kernel
  apply modelSubgroup.subtype_injective
  change modelSubgroup.subtype (gen5 0) = (modelSubgroup.subtype (RankOneEightCharacteristic.basis 0))⁻¹
  simp only [perm5_eq,CatalogueCertificate.elementaryPermutation_eq] at he
  exact he
private theorem last_in_eight1 : gen5 1 = (RankOneEightCharacteristic.basis 1)⁻¹ := by
  have he : perm5 1 = (CatalogueCertificate.elementaryPermutation 1)⁻¹ := by
    apply Equiv.ext
    apply Rudvalis.OrderCertificate.allFin
    decide +kernel
  apply modelSubgroup.subtype_injective
  change modelSubgroup.subtype (gen5 1) = (modelSubgroup.subtype (RankOneEightCharacteristic.basis 1))⁻¹
  simp only [perm5_eq,CatalogueCertificate.elementaryPermutation_eq] at he
  exact he
private theorem last_in_eight2 : gen5 2 = (RankOneEightCharacteristic.basis 0)⁻¹ * (RankOneEightCharacteristic.basis 2)⁻¹ := by
  have he : perm5 2 = (CatalogueCertificate.elementaryPermutation 0)⁻¹ * (CatalogueCertificate.elementaryPermutation 2)⁻¹ := by
    apply Equiv.ext
    apply Rudvalis.OrderCertificate.allFin
    decide +kernel
  apply modelSubgroup.subtype_injective
  change modelSubgroup.subtype (gen5 2) = (modelSubgroup.subtype (RankOneEightCharacteristic.basis 0))⁻¹ * (modelSubgroup.subtype (RankOneEightCharacteristic.basis 2))⁻¹
  simp only [perm5_eq,CatalogueCertificate.elementaryPermutation_eq] at he
  exact he
private theorem eight_in_last0 : RankOneEightCharacteristic.basis 0 = (gen5 0)⁻¹ := by
  have he : CatalogueCertificate.elementaryPermutation 0 = (perm5 0)⁻¹ := by
    apply Equiv.ext
    apply Rudvalis.OrderCertificate.allFin
    decide +kernel
  apply modelSubgroup.subtype_injective
  change modelSubgroup.subtype (RankOneEightCharacteristic.basis 0) = (modelSubgroup.subtype (gen5 0))⁻¹
  simp only [perm5_eq,CatalogueCertificate.elementaryPermutation_eq] at he
  exact he
private theorem eight_in_last1 : RankOneEightCharacteristic.basis 1 = (gen5 1)⁻¹ := by
  have he : CatalogueCertificate.elementaryPermutation 1 = (perm5 1)⁻¹ := by
    apply Equiv.ext
    apply Rudvalis.OrderCertificate.allFin
    decide +kernel
  apply modelSubgroup.subtype_injective
  change modelSubgroup.subtype (RankOneEightCharacteristic.basis 1) = (modelSubgroup.subtype (gen5 1))⁻¹
  simp only [perm5_eq,CatalogueCertificate.elementaryPermutation_eq] at he
  exact he
private theorem eight_in_last2 : RankOneEightCharacteristic.basis 2 = (gen5 0)⁻¹ * (gen5 2)⁻¹ := by
  have he : CatalogueCertificate.elementaryPermutation 2 = (perm5 0)⁻¹ * (perm5 2)⁻¹ := by
    apply Equiv.ext
    apply Rudvalis.OrderCertificate.allFin
    decide +kernel
  apply modelSubgroup.subtype_injective
  change modelSubgroup.subtype (RankOneEightCharacteristic.basis 2) = (modelSubgroup.subtype (gen5 0))⁻¹ * (modelSubgroup.subtype (gen5 2))⁻¹
  simp only [perm5_eq,CatalogueCertificate.elementaryPermutation_eq] at he
  exact he

private theorem last_eq : H5 = elementary 2 := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    fin_cases j
    · change gen5 0 ∈ elementary 2
      rw [last_in_eight0]
      exact (elementary 2).inv_mem (RankOneEightCharacteristic.basis_mem 0)
    · change gen5 1 ∈ elementary 2
      rw [last_in_eight1]
      exact (elementary 2).inv_mem (RankOneEightCharacteristic.basis_mem 1)
    · change gen5 2 ∈ elementary 2
      rw [last_in_eight2]
      exact (elementary 2).mul_mem ((elementary 2).inv_mem (RankOneEightCharacteristic.basis_mem 0))
        ((elementary 2).inv_mem (RankOneEightCharacteristic.basis_mem 2))
  · rw [←RankOneEightCharacteristic.closure_basis]
    apply (closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    fin_cases j
    · change RankOneEightCharacteristic.basis 0 ∈ H5
      rw [eight_in_last0]
      exact H5.inv_mem (gen5_mem 0)
    · change RankOneEightCharacteristic.basis 1 ∈ H5
      rw [eight_in_last1]
      exact H5.inv_mem (gen5_mem 1)
    · change RankOneEightCharacteristic.basis 2 ∈ H5
      rw [eight_in_last2]
      exact H5.mul_mem (H5.inv_mem (gen5_mem 0)) (H5.inv_mem (gen5_mem 2))

/-- The sixth lower-central term is exactly the original marked eight-group. -/
theorem lowerCentral_five : localP.lowerCentralSeries 5 = elementary 2 := by
  rw [←last_eq]
  apply le_antisymm
  · have h1 : localP.lowerCentralSeries 1 ≤ H1 := step1
    have h2 : localP.lowerCentralSeries 2 ≤ H2 := (commutator_mono h1 le_rfl).trans step2
    have h3 : localP.lowerCentralSeries 3 ≤ H3 := (commutator_mono h2 le_rfl).trans step3
    have h4 : localP.lowerCentralSeries 4 ≤ H4 := (commutator_mono h3 le_rfl).trans step4
    exact (commutator_mono h4 le_rfl).trans step5
  · apply (closure_le _).mpr
    rintro _ ⟨j,rfl⟩
    exact gen5_mem_lower j

end Rudvalis.SylowLowerCentral
