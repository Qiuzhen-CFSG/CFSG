module
public import Theory.SpecificGroups.SymmetricFive.OuterFourGeometry
public import Theory.GroupTheory.ConjugatePairInternalLift
/-!
# Sylow two-normalizers in the symmetric group on five letters

The eight words in (01), (23), and (02)(13) form a Sylow two-subgroup.
Any normalizing permutation conjugates each of these generators back into
the eight words, which forces the permutation itself into that set. The
finite certificate tests individual permutations and words, not subgroups.
Sylow conjugacy transports this normalizer calculation to every Sylow.

Source: the symmetric-five diagonal exclusion in Aschbacher–Smith 13.6.14,
printed p.929.
-/
public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricFive.SylowNormalizer
abbrev D := Equiv.Perm (Fin 5)
private def a : D := Equiv.swap 0 1
private def b : D := Equiv.swap 2 3
private def c : D := Equiv.swap 0 2 * Equiv.swap 1 3
private def word : Fin 8 → D := ![1,a,b,a*b,c,a*c,b*c,a*b*c]
private def eight : Subgroup D where
  carrier := Set.range word
  one_mem' := ⟨0,rfl⟩
  mul_mem' := by
    have hh : ∀ i j, ∃ k, word i * word j = word k := by decide +kernel
    rintro x y ⟨i,rfl⟩ ⟨j,rfl⟩
    obtain ⟨k,hk⟩ := hh i j
    exact ⟨k,hk.symm⟩
  inv_mem' := by
    have hh : ∀ i, ∃ k, (word i)⁻¹ = word k := by decide +kernel
    rintro x ⟨i,rfl⟩
    obtain ⟨k,hk⟩ := hh i
    exact ⟨k,hk.symm⟩
private theorem card_eight : Nat.card eight = 8 := by
  have hi : Function.Injective word := by decide +kernel
  change Nat.card (Set.range word) = 8
  rw [← Nat.card_congr (Equiv.ofInjective _ hi)]
  simp
private theorem normalizer_eight : normalizer (eight : Set D) = eight := by
  apply le_antisymm ?_ eight.le_normalizer
  intro g hg
  have ht : ∀ g : D, (∃ i, word i = g*a*g⁻¹) →
      (∃ i, word i = g*b*g⁻¹) → (∃ i, word i = g*c*g⁻¹) →
      ∃ i, word i = g := by decide +kernel
  exact ht g
    ((mem_normalizer_iff.mp hg a).mp ⟨1,rfl⟩)
    ((mem_normalizer_iff.mp hg b).mp ⟨2,rfl⟩)
    ((mem_normalizer_iff.mp hg c).mp ⟨4,rfl⟩)
private noncomputable def sylow : Sylow 2 D := Sylow.ofCard eight (by
  rw [card_eight,Nat.card_eq_fintype_card,Fintype.card_perm]
  norm_num [Nat.factorial]
  decide +kernel)

/-- Every Sylow two-subgroup of S₅ is its own normalizer. -/
theorem sylow_normalizer_eq_self (P : Sylow 2 D) : normalizer (P : Set D) = (P : Subgroup D) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq D sylow P
  have hg := congrArg Sylow.toSubgroup hg
  change eight.map (MulAut.conj g).toMonoidHom = (P : Subgroup D) at hg
  change normalizer ((P : Subgroup D) : Set D) = (P : Subgroup D)
  rw [← hg,← map_equiv_normalizer_eq,normalizer_eight]
end Theory.SpecificGroups.SymmetricFive.SylowNormalizer
