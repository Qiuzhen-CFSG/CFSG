module

public import Theory.Quasithin.LocalRank
public import Theory.Quasithin.Rank

/-!
# Local rank from an embedded group with a normal two-subgroup

If a finite group P has a nontrivial normal 2-subgroup Q, an embedding of P
into G puts its image in the normalizer of the image of Q. Consequently the
ordinary prime rank of P is bounded by the two-local prime rank of G.
The image of Q need not be normal in G.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
Lemma A.2.19, printed p. 41 (the E₉ × A₄ obstruction).
-/

public section
namespace Theory.Quasithin

/-- The image normalizer is a genuine two-local overgroup of the embedded group. -/
theorem primeRank_le_twoLocalPrimeRank_of_embedding {G P : Type*} [Group G] [Finite G] [Group P] [Finite P]
    (f : P →* G) (hf : Function.Injective f)
    (Q : Subgroup P) [Q.Normal] (hQ : Q ≠ ⊥) (hQp : IsPGroup 2 Q)
    (p : ℕ) : primeRank p P ≤ twoLocalPrimeRank p G := by
  have hR : Q.map f ≠ ⊥ := fun h => hQ ((Q.map_eq_bot_iff_of_injective hf).mp h)
  have hlocal : IsTwoLocal (Subgroup.normalizer (Q.map f : Set G)) :=
    ⟨Q.map f, hR, hQp.map f, rfl⟩
  calc
    primeRank p P = primeRank p (Subgroup.normalizer (Q : Set P)) := by
      rw [Q.normalizer_eq_top]
      exact (primeRank_congr p Subgroup.topEquiv).symm
    _ = primeRank p ((Subgroup.normalizer (Q : Set P)).map f) :=
      primeRank_congr p (Subgroup.equivMapOfInjective _ f hf)
    _ ≤ primeRank p (Subgroup.normalizer (Q.map f : Set G)) :=
      primeRank_mono p (Subgroup.le_normalizer_map f)
    _ ≤ twoLocalPrimeRank p G := hlocal.primeRank_le p

end Theory.Quasithin
