module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.Contracts
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ComponentRestriction
public import Theory.Alternating.Aut
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex

/-!
# The automorphism two-part bound for A₅ and Sz(8)

The full automorphism group of A₅ has order 120 by its proved symmetric-group
conjugation description. The proved Suzuki inner-field coverage gives odd
outer index, so the automorphism two-part is at most the group two-part.
Actual model equivalences transport these calculations to the smaller
component. No model-order or automorphism-table assumptions are added.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.3.6, printed p.1179 / PDF p.1196.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction
open Subgroup Theory.GroupTheory

/-- An odd outer index contributes no power of two to the automorphism group. -/
theorem automorphism_twoPart_le_of_odd_inner_index (A : Type*) [Group A] [Finite A]
    (hodd : Odd (MulAut.conj : A →* MulAut A).range.index) :
    2 ^ (Nat.card (MulAut A)).factorization 2 ≤ 2 ^ (Nat.card A).factorization 2 := by
  let I := (MulAut.conj : A →* MulAut A).range
  have hz : I.index.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by simpa only [← even_iff_two_dvd] using (Nat.not_even_iff_odd.mpr hodd))
  have hfact : (Nat.card (MulAut A)).factorization 2 = (Nat.card I).factorization 2 := by
    rw [← I.card_mul_index, Nat.factorization_mul (Nat.card_pos.ne') Subgroup.index_ne_zero_of_finite,
      Finsupp.add_apply, hz, add_zero]
  rw [hfact]
  apply Nat.pow_le_pow_right (by decide : 0 < 2)
  exact (Nat.factorization_le_iff_dvd (Nat.card_pos.ne') (Nat.card_pos.ne')).mpr
    (card_range_dvd (MulAut.conj : A →* MulAut A)) 2

/-- The exact bound consumed after the A5/Sz(8) alternatives in 16.3.6.
Both model facts are proved upstream on the concrete carriers. -/
theorem automorphism_twoPart_bound (A : Type*) [Group A] [Finite A]
    (hmodel : Nonempty (A ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (A ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)) :
    2 ^ (Nat.card (MulAut A)).factorization 2 ≤ 2 * 2 ^ (Nat.card A).factorization 2 := by
  rcases hmodel with he | he
  · obtain ⟨e⟩ := he
    have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    have hAut : Nat.card (MulAut (alternatingGroup (Fin 5))) = 120 := by
      let eAut := Equiv.ofBijective _
        (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
      rw [Nat.card_congr eAut.symm, Nat.card_perm, Nat.card_fin]
      decide
    rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv, hc, hAut]
    rw [show 120 = 2 * 60 by decide, Nat.factorization_mul (by decide) (by decide),
      Finsupp.add_apply, Nat.prime_two.factorization_self, pow_add]
    simp
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv]
    have hb := automorphism_twoPart_le_of_odd_inner_index
      (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1)
      (BenderSuzuki.MatrixGroups.suzuki_odd_outer_index 1 (by decide))
    omega

/-- Every established exceptional enlargement supplies the needed numerical bound. -/
theorem automorphism_twoPart_bound_of_exceptional {G : Type*} [Group G] [Finite G]
    {E L : Subgroup G} {i : G} (h : ExceptionalEnlargement E L i) :
    2 ^ (Nat.card (MulAut L)).factorization 2 ≤ 2 * 2 ^ (Nat.card L).factorization 2 := by
  apply automorphism_twoPart_bound
  rcases h.models with h | h
  · exact Or.inl h.1
  · exact Or.inr h.1

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction
