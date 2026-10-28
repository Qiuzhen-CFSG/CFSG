module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels
public import GorensteinWalter.PGL2DihedralSylow
public import Theory.GroupTheory.PrimeRankDihedral
public import Theory.GroupTheory.PrimeRankSylow

/-!
# Four-group actors in the large-family branch

Dihedral Sylow subgroups bound the elementary two-rank of odd PGL₂ by two.
An elementary actor of rank greater than one is consequently a four-group.
If the weak-closure normalizer lies in a proper subgroup, a nontrivial
family member must occur in the fixed Sylow subgroup: otherwise the weak
closure is trivial and its normalizer is the whole group.

These deductions use the literal invariant-family and weak-closure
definitions in Aschbacher--Smith E.1.5, printed p.210. They prepare the
inner/outer actor split in E.1.14(6), printed p.214.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal

open Subgroup GorensteinWalter Theory.GroupTheory

/-- The dihedral Sylow theorem bounds the elementary two-rank in PGL₂. -/
theorem pgl_twoRank_le_two (F : Type*) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) : primeRank 2 (PGL2 F) ≤ 2 := by
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  let T : Sylow 2 (PGL2 F) := Classical.choice inferInstance
  obtain ⟨m, _, ⟨e⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F hF T
  rw [T.primeRank_eq, primeRank_equiv 2 e]
  exact dihedral_rank_le_two m

/-- At two-rank at most two, a nontrivial elementary actor of rank greater
than one is a four-group. -/
theorem actor_isKleinFour_of_rank
    {G : Type*} [Group G] [Finite G] (hG : primeRank 2 G ≤ 2)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hAb : A ≠ ⊥)
    (hr : 1 < Group.rank A) : IsKleinFour A := by
  let : IsElementaryAbelian 2 A := hA
  let : Nontrivial A := (A.nontrivial_iff_ne_bot).mpr hAb
  have hcard : Nat.card A ≤ 4 := by
    simpa using (primeRank_le_iff_elementary_card_le G).mp hG A hA
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hn2 : n ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    simpa only [← hn] using hcard
  have h4 : Nat.card A = 4 := by
    interval_cases n
    · have hl := IsElementaryAbelian.rank_le_of_card_le (p := 2) (n := 1) A
        (by rw [hn]; norm_num)
      omega
    · have hl := IsElementaryAbelian.rank_le_of_card_le (p := 2) (n := 1) A
        (by rw [hn])
      omega
    · simpa using hn
  exact ⟨h4, IsElementaryAbelian.exponent_eq_prime⟩

/-- A proper overgroup of the weak-closure normalizer forces a nontrivial
family member inside the specified Sylow subgroup. -/
theorem exists_nontrivial_actor_of_normalizer_le
    {G : Type*} [Group G] (T M : Subgroup G) (Ω : Set (Subgroup G))
    (hM : M ≠ ⊤) (hN : normalizer (weakClosure T Ω : Set G) ≤ M) :
    ∃ A ∈ Ω, A ≤ T ∧ A ≠ ⊥ := by
  classical
  by_contra h
  have hw : weakClosure T Ω = ⊥ := by
    apply le_bot_iff.mp
    apply sSup_le
    rintro A ⟨hA, hAT⟩
    have hAb : A = ⊥ := by
      by_contra hn
      exact h ⟨A, hA, hAT, hn⟩
    exact hAb.le
  rw [hw] at hN
  apply hM
  apply top_unique
  intro x _
  apply hN
  rw [mem_normalizer_iff]
  intro y
  simp

/-- The actual large-family hypothesis in `ConcreteLocalGeometryAt` supplies
a four-group actor in PGL₂, without assuming that actor lies in PSL₂. -/
theorem exists_four_actor
    (F : Type*) [Field F] [Finite F] [Finite (PGL2 F)] (hF : IsOddPrimePower (Nat.card F))
    (T : Sylow 2 (PGL2 F)) (Ω : Set (Subgroup (PGL2 F)))
    (hΩ : IsElementaryFamily Ω)
    (hlarge : ∀ A ∈ Ω, A ≤ (T : Subgroup (PGL2 F)) → A ≠ ⊥ → 1 < Group.rank A)
    (M : Subgroup (PGL2 F)) (hM : M ≠ ⊤)
    (hN : normalizer (weakClosure (T : Subgroup (PGL2 F)) Ω : Set (PGL2 F)) ≤ M) :
    ∃ A ∈ Ω, A ≤ (T : Subgroup (PGL2 F)) ∧ IsKleinFour A := by
  obtain ⟨A, hA, hAT, hAb⟩ := exists_nontrivial_actor_of_normalizer_le
    (T : Subgroup (PGL2 F)) M Ω hM hN
  exact ⟨A, hA, hAT, actor_isKleinFour_of_rank (pgl_twoRank_le_two F hF)
    A (hΩ.1 A hA) hAb (hlarge A hA hAT hAb)⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal
