module

public import Theory.Quasithin.EmbeddedNormalTwoLocalRank
public import Theory.Quasithin.LocalRankEmbedding
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
public import Mathlib.GroupTheory.Perm.ViaEmbedding

/-!
# Positive local cubic rank from an alternating-four subgroup

The normal Klein four-group in A₄ has an element of order three in its
normalizer. An actual A₄ embedding therefore gives positive two-local
three-rank in the ambient group. Extending permutations by the identity
supplies this witness in every Aₙ with at least four letters.

Source: Aschbacher–Smith, A.1.34 and A.3.8, printed pp.29–30 and45–46.
This is the local contribution in the nonnormal-component rank inequality.
-/

public noncomputable section
open Subgroup
namespace Theory.Quasithin

/-- The normal four-group of A₄ gives a genuine two-local cubic witness. -/
theorem one_le_twoLocalPrimeRank_of_a4_embedding
    {G : Type*} [Group G] [Finite G]
    (f : alternatingGroup (Fin 4) →* G) (hf : Function.Injective f) :
    1 ≤ twoLocalPrimeRank 3 G := by
  let A := alternatingGroup (Fin 4)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := A) 3
    (by rw [alternatingGroup.card_of_card_eq_four (by simp)]; decide)
  let C := zpowers z
  let : CommGroup C := IsCyclic.commGroup
  have hc : Nat.card C = 3 := (Nat.card_zpowers z).trans hz
  have hr : 1 ≤ primeRank 3 A := primeRank_ge_of_elementary_embedding
    (fun a => by simpa only [hc] using pow_card_eq_one' (x := a))
    (by simpa using hc) C.subtype C.subtype_injective
  let Q := alternatingGroup.kleinFour (Fin 4)
  let : Q.Normal := alternatingGroup.normal_kleinFour (by simp)
  have hq : Nat.card Q = 4 := alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
  have hne : Q ≠ ⊥ := by
    intro he
    rw [he, card_bot] at hq
    contradiction
  exact hr.trans (primeRank_le_twoLocalPrimeRank_of_embedding f hf Q hne
    (IsPGroup.of_card (n := 2) hq) 3)

/-- Extending permutations by the identity preserves their alternating sign. -/
def alternatingEmbedding {n : ℕ} (hn : 4 ≤ n) :
    alternatingGroup (Fin 4) →* alternatingGroup (Fin n) := by
  classical
  let j := Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hn)
  exact (j.comp (alternatingGroup (Fin 4)).subtype).codRestrict _ (by
    intro a
    change Equiv.Perm.sign (j a.val) = 1
    simp only [j, Equiv.Perm.viaEmbeddingHom, Equiv.Perm.extendDomainHom_apply,
      Equiv.Perm.sign_extendDomain]
    exact Equiv.Perm.mem_alternatingGroup.mp a.property)

theorem alternatingEmbedding_injective {n : ℕ} (hn : 4 ≤ n) :
    Function.Injective (alternatingEmbedding hn) := by
  intro a b hab
  exact Subtype.ext (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb hn)
    (congrArg Subtype.val hab))

/-- Every alternating group with at least four letters has positive local cubic rank. -/
theorem alternating_one_le_twoLocalPrimeRank {n : ℕ} (hn : 4 ≤ n) :
    1 ≤ twoLocalPrimeRank 3 (alternatingGroup (Fin n)) :=
  one_le_twoLocalPrimeRank_of_a4_embedding (alternatingEmbedding hn)
    (alternatingEmbedding_injective hn)

end Theory.Quasithin
