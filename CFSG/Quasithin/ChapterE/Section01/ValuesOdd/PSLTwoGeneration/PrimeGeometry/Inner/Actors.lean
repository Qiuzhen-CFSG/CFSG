module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LinearModels
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.ElementaryAbelian.FixedOrderGeneration

/-!
# Four-group actors in odd PSL₂

An elementary subgroup of rank greater than one contains a four-group.
In odd PSL₂ that four-group is self-centralizing, so the whole elementary
subgroup equals it. Consequently the large-family case of E.1.14(6) involves
only four-groups and possibly the identity subgroup. Removing the identity
does not change the literal weak closure.

This supplies the actors, not their escaping local overgroups.
Source: Aschbacher--Smith, E.1.2 and E.1.14(6), printed pp.209--210 and 214.
-/

public section

open Subgroup GorensteinWalter

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner

variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

private theorem four_of_selfCentralizing_four
    (hcent : ∀ A : Subgroup G, IsKleinFour A → centralizer (A : Set G) = A)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hr : 1 < Group.rank A) :
    IsKleinFour A := by
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hrn : Group.rank A ≤ n := IsElementaryAbelian.rank_le_of_card_le A hn.le
  have hc : 2 ^ 2 ≤ Nat.card A := by
    rw [hn]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨B, hBA, hB, hBc, _⟩ :=
    IsElementaryAbelian.exists_two_power_subgroup_mem A (by decide : 0 < 2) hc 1 A.one_mem
  let : IsElementaryAbelian 2 B := hB
  let : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hBK : IsKleinFour B := ⟨hBc, IsElementaryAbelian.exponent_eq_prime⟩
  have hAB : A ≤ centralizer (B : Set G) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val
      (IsMulCommutative.is_comm.comm (⟨b, hBA hb⟩ : A) ⟨a, ha⟩)
  have he : A = B := le_antisymm (hAB.trans_eq (hcent B hBK)) hBA
  rwa [he]

/-- Every elementary actor of rank greater than one in an actual odd PSL₂
model is a four-group. -/
theorem actor_isKleinFour (hF : IsOddPrimePower (Nat.card F)) (e : G ≃* PSL2 F)
    (A : Subgroup G) [IsElementaryAbelian 2 A] (hr : 1 < Group.rank A) :
    IsKleinFour A := by
  apply four_of_selfCentralizing_four _ A hr
  intro B hB
  exact kleinFour_selfCentralizing_of_embedding hF
    (Matrix.ProjectiveSpecialLinearGroup.toPGL.comp e.toMonoidHom)
    (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp e.injective) B hB

/-- In the large-family case, restricting to four-groups preserves the
actual weak closure, including when the original family contains the identity. -/
theorem weakClosure_eq_four_group_family
    (hF : IsOddPrimePower (Nat.card F)) (e : G ≃* PSL2 F)
    (T : Sylow 2 G) (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (hlarge : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → 1 < Group.rank A) :
    weakClosure (T : Subgroup G) Ω =
      weakClosure (T : Subgroup G) {A | A ∈ Ω ∧ IsKleinFour A} := by
  apply le_antisymm
  · apply sSup_le
    intro A hA
    by_cases hbot : A = ⊥
    · exact hbot ▸ bot_le
    let : IsElementaryAbelian 2 A := hΩ.1 A hA.1
    exact le_sSup ⟨⟨hA.1, actor_isKleinFour hF e A (hlarge A hA.1 hA.2 hbot)⟩, hA.2⟩
  · exact sSup_le fun A hA => le_sSup ⟨hA.1.1, hA.2⟩

/-- A proper overgroup of the weak-closure normalizer forces an actual
four-group from the family to occur inside the chosen Sylow subgroup. -/
theorem exists_four_group_actor
    (hF : IsOddPrimePower (Nat.card F)) (e : G ≃* PSL2 F)
    (T : Sylow 2 G) (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (hlarge : ∀ A ∈ Ω, A ≤ (T : Subgroup G) → A ≠ ⊥ → 1 < Group.rank A)
    (M : Subgroup G) (hM : M ≠ ⊤)
    (hNM : normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M) :
    ∃ A : Subgroup G, A ∈ Ω ∧ A ≤ (T : Subgroup G) ∧ IsKleinFour A := by
  classical
  by_contra hnone
  have hW : weakClosure (T : Subgroup G) Ω = ⊥ := by
    rw [weakClosure_eq_four_group_family hF e T Ω hΩ hlarge]
    apply le_bot_iff.mp
    apply sSup_le
    intro A hA
    exact (hnone ⟨A, hA.1.1, hA.2, hA.1.2⟩).elim
  apply hM
  apply top_unique
  simpa only [hW, normalizer_eq_top] using hNM

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Inner
