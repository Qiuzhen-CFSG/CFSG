module

public import Theory.PPrimeCore
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Order.Atoms

/-!
# Maximal prime-complement signalizers

If K is the largest subgroup of order coprime to p normalized by Q, then
N_G(Q) normalizes K. Conjugation preserves coprime order and Q-invariance;
maximality gives containment of the conjugate, and equal orders give equality.

Consequently, let M be a maximal subgroup of a finite simple group. If Q ≤ M
has a normalizer escaping M, and every Q-invariant subgroup of order coprime
to p lies in O_p′(M), then O_p′(M) is trivial. Otherwise its ambient normalizer
is proper by simplicity, contains M, and hence equals M by maximality.

Source: the signalizer-invariance argument of GLS4, Chapter 2, Lemma 19.4,
using the absorption property established there in Lemma 19.3(c). The
absorption property is an explicit hypothesis here; none of the preceding
Sylow geometry or fusion hypotheses of that application are asserted.
-/

namespace Subgroup

/-- The largest Q-invariant subgroup of order coprime to p is N(Q)-invariant. -/
public theorem normalizer_le_normalizer_of_pPrime_absorption
    {G : Type*} [Group G] [Finite G] (p : ℕ) (Q K : Subgroup G)
    (hK : Nat.Coprime p (Nat.card K)) (hQK : Q ≤ normalizer (K : Set G))
    (habs : ∀ Y : Subgroup G, Nat.Coprime p (Nat.card Y) →
      Q ≤ normalizer (Y : Set G) → Y ≤ K) :
    normalizer (Q : Set G) ≤ normalizer (K : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · apply habs
    · rwa [card_map_of_injective (MulAut.conj g).injective]
    · have hmap := (map_mono (f := (MulAut.conj g).toMonoidHom) hQK).trans
        (K.le_normalizer_map (MulAut.conj g).toMonoidHom)
      have hQmap : Q.map (MulAut.conj g).toMonoidHom = Q :=
        mem_normalizer_iff_map_conj_eq.mp hg
      rwa [hQmap] at hmap
  · rw [card_map_of_injective (MulAut.conj g).injective]

/-- An escaping normalizer eliminates the prime-complement core of a maximal
subgroup when that core absorbs every coprime subgroup normalized by Q. -/
public theorem pPrimeCore_eq_bot_of_maximal_normalizer_escape
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (p : ℕ) [Fact p.Prime] (M Q : Subgroup G) (hM : IsCoatom M) (hQM : Q ≤ M)
    (hescape : ¬ normalizer (Q : Set G) ≤ M)
    (habs : ∀ Y : Subgroup G, Nat.Coprime p (Nat.card Y) →
      Q ≤ normalizer (Y : Set G) → Y ≤ (pPrimeCore p M).map M.subtype) :
    pPrimeCore p M = ⊥ := by
  let K := (pPrimeCore p M).map M.subtype
  have hMK : M ≤ normalizer (K : Set G) := by
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pPrimeCore p M).le_normalizer_map M.subtype
  have hKcop : Nat.Coprime p (Nat.card K) := by
    rw [card_map_of_injective M.subtype_injective]
    exact pPrimeCore_coprime_card
  have hNK := normalizer_le_normalizer_of_pPrime_absorption p Q K hKcop
    (hQM.trans hMK) habs
  by_contra hcore
  have hKne : K ≠ ⊥ := by
    intro hk
    exact hcore ((map_eq_bot_iff_of_injective _ M.subtype_injective).mp hk)
  have hproper : normalizer (K : Set G) ≠ ⊤ := by
    intro ht
    rcases (normalizer_eq_top_iff.mp ht).eq_bot_or_eq_top with hb | ht
    · exact hKne hb
    · exact hM.ne_top (top_unique (ht ▸ map_subtype_le (pPrimeCore p M)))
  exact hescape (hNK.trans_eq ((hM.le_iff_eq hproper).mp hMK))

end Subgroup
