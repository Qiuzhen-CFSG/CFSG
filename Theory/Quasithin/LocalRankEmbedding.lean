module

public import Theory.Quasithin.LocalRank

/-!
# Local prime rank under embeddings

The normalizer of a nontrivial two-subgroup maps into the normalizer of its
image. Consequently local prime rank is monotone under embeddings, even
though the image of a two-local need not itself be a two-local.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.8,
printed p.34.
-/

public section

open Theory.GroupTheory

/-- Embeddings do not increase local prime rank. -/
theorem twoLocalPrimeRank_le_of_injective {G H : Type*}
    [Group G] [Group H] [Finite G] [Finite H]
    (p : ℕ) (f : G →* H) (hf : Function.Injective f) :
    twoLocalPrimeRank p G ≤ twoLocalPrimeRank p H := by
  apply (twoLocalPrimeRank_le_iff p _).mpr
  rintro M ⟨Q, hQ, hpQ, rfl⟩
  have hR : Q.map f ≠ ⊥ := fun h =>
    hQ ((Subgroup.map_eq_bot_iff_of_injective Q hf).mp h)
  have hlocal : IsTwoLocal (Subgroup.normalizer (Q.map f : Set H)) :=
    ⟨Q.map f, hR, hpQ.map f, rfl⟩
  calc
    primeRank p (Subgroup.normalizer (Q : Set G)) =
        primeRank p ((Subgroup.normalizer (Q : Set G)).map f) :=
      primeRank_equiv p (Subgroup.equivMapOfInjective _ f hf)
    _ ≤ primeRank p (Subgroup.normalizer (Q.map f : Set H)) :=
      primeRank_le_of_injective p (Subgroup.inclusion (Subgroup.le_normalizer_map f))
        (Subgroup.inclusion_injective _)
    _ ≤ twoLocalPrimeRank p H := hlocal.primeRank_le p
