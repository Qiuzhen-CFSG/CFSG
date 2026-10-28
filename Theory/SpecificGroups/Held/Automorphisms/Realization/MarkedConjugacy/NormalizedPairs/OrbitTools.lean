module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.Contracts
public import Theory.SpecificGroups.Held.Model.FourPointBase

/-!
# Certifying a whole Held conjugacy class by a closed permutation family

A family of permutations containing the seed and closed under conjugation by
both ATLAS generators contains the image of every conjugate of that seed.
Indeed, its inverse image in `He` is normalized by both generators, hence by
all of `He`. Finiteness turns forward closure into normalization.

Consequently the normalized-pair calculation on every row of such a family
implies `ClassCalculation seed`. The family may be a superset of the class;
no subgroup membership or distinctness assertion about its rows is needed.
All seven relators and the three literal marked words are transported through
the defining representation. The row tests and closure identities remain
explicit hypotheses for their finite certificate producers.

For families already defined as words in `He`, the four-point variant checks
closure on the certified base alone. A failed relator needs only one moved
point; a surviving row needs the three literal marked fixed-point equations.
Thus no complete permutation table is required for these word families.

This is the permutation analogue of the closed-family argument in
`Theory.SpecificGroups.Janko1.Model.SolvableLocal.LargePrimes.Orbit`.
The Held words and action conventions come from John Bray's
`Model/Source/HeG1-P1.M` and the retained degree-2058 ATLAS permutations.
-/

namespace Held.Realization.MarkedConjugacy.NormalizedPairs

private theorem mem_of_isConj_of_closed (T : Set He)
    (ha : ∀ x ∈ T, a * x * a⁻¹ ∈ T)
    (hb : ∀ x ∈ T, b * x * b⁻¹ ∈ T)
    {s x : He} (hs : s ∈ T) (hconj : IsConj s x) : x ∈ T := by
  have hna : a ∈ Subgroup.normalizer T := Subgroup.mem_normalizer_fintype ha
  have hnb : b ∈ Subgroup.normalizer T := Subgroup.mem_normalizer_fintype hb
  have hn : Subgroup.normalizer T = ⊤ := by
    apply top_unique
    rw [← closure_pair, Subgroup.closure_le]
    rintro _ (rfl | h)
    · exact hna
    · exact Set.mem_singleton_iff.mp h ▸ hnb
  obtain ⟨g, rfl⟩ := isConj_iff.mp hconj
  have hg : g ∈ Subgroup.normalizer T := by rw [hn]; trivial
  exact (Subgroup.mem_set_normalizer_iff.mp hg s).mp hs

/-- Generator closure certifies containment of the entire conjugacy class. -/
public theorem representation_mem_family_of_isConj {ι : Type*}
    (family : ι → Equiv.Perm (Fin 2058)) (seed : He)
    (hseed : ∃ i, representation seed = family i)
    (ha : ∀ i, ∃ j, atlasA * family i * atlasA⁻¹ = family j)
    (hb : ∀ i, ∃ j, atlasB * family i * atlasB⁻¹ = family j)
    {x : He} (hx : IsConj seed x) : ∃ i, representation x = family i := by
  let T : Set He := {x | ∃ i, representation x = family i}
  apply mem_of_isConj_of_closed T ?_ ?_ hseed hx
  · rintro z ⟨i, hi⟩
    obtain ⟨j, hj⟩ := ha i
    refine ⟨j, ?_⟩
    simpa only [map_mul, map_inv, hi, show representation a = atlasA from rfl] using hj
  · rintro z ⟨i, hi⟩
    obtain ⟨j, hj⟩ := hb i
    refine ⟨j, ?_⟩
    simpa only [map_mul, map_inv, hi, show representation b = atlasB from rfl] using hj

/-- Checked rows of a generator-closed family give the full class calculation. -/
public theorem classCalculation_of_permutation_family {ι : Type*}
    (family : ι → Equiv.Perm (Fin 2058)) (seed : He)
    (hseed : ∃ i, representation seed = family i)
    (ha : ∀ i, ∃ j, atlasA * family i * atlasA⁻¹ = family j)
    (hb : ∀ i, ∃ j, atlasB * family i * atlasB⁻¹ = family j)
    (hrows : ∀ (k : Fin 17), k = 1 ∨ k = 3 → ∀ i,
      let y := family i * (atlasA * atlasB) ^ k.val
      (∀ r : Fin 7, relationWord (family i) y r = 1) →
      ∃ p : Fin 2058, family i p = p ∧
        ((y ^ 2)⁻¹ * family i * y ^ 2) p = p ∧
        (y ^ 2 * family i * (y ^ 2)⁻¹) p = p) :
    ClassCalculation seed := by
  intro k hk x hx hr
  obtain ⟨i, hi⟩ := representation_mem_family_of_isConj family seed hseed ha hb hx
  have hy : representation (x * (a * b) ^ k.val) =
      family i * (atlasA * atlasB) ^ k.val := by
    simp only [map_mul, map_pow, hi, show representation a = atlasA from rfl,
      show representation b = atlasB from rfl]
  have hr' : ∀ r : Fin 7,
      relationWord (family i) (family i * (atlasA * atlasB) ^ k.val) r = 1 := by
    intro r
    have h := congrArg representation (hr r)
    simpa only [map_relationWord, map_one, hi, hy] using h
  obtain ⟨p, hp⟩ := hrows k hk i hr'
  refine ⟨p, ?_⟩
  simpa only [PairFixes, map_mul, map_inv, map_pow, hi, hy] using hp

/-- A family of actual Held words closed under the generators covers every
conjugate of its seed. Its row tests give the required class calculation. -/
public theorem classCalculation_of_closed_family {ι : Type*}
    (family : ι → He) (seed : He)
    (hseed : ∃ i, seed = family i)
    (ha : ∀ i, ∃ j, a * family i * a⁻¹ = family j)
    (hb : ∀ i, ∃ j, b * family i * b⁻¹ = family j)
    (hrows : ∀ k : Fin 17, k = 1 ∨ k = 3 → ∀ i,
      (∀ r : Fin 7, relationWord (family i) (family i * (a * b) ^ k.val) r = 1) →
      ∃ p : Fin 2058, PairFixes (family i) (family i * (a * b) ^ k.val) p) :
    ClassCalculation seed := by
  intro k hk x hx hr
  have hs : seed ∈ Set.range family := by
    obtain ⟨i, hi⟩ := hseed
    exact ⟨i, hi.symm⟩
  have hxmem : x ∈ Set.range family := by
    apply mem_of_isConj_of_closed (Set.range family) ?_ ?_ hs hx
    · rintro _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := ha i
      exact ⟨j, hj.symm⟩
    · rintro _ ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := hb i
      exact ⟨j, hj.symm⟩
  obtain ⟨i, rfl⟩ := hxmem
  exact hrows k hk i hr

/-- Four-point closure and point-trajectory rejection certify the entire
class of actual Held words, with the source relators and marked words intact. -/
public theorem classCalculation_of_four_point_checks {ι : Type*}
    (family : ι → He) (seed : He)
    (hseed : ∃ i, ∀ t : Fin 4,
      representation seed ⟨t.val, by omega⟩ =
        representation (family i) ⟨t.val, by omega⟩)
    (ha : ∀ i, ∃ j, ∀ t : Fin 4,
      representation (a * family i * a⁻¹) ⟨t.val, by omega⟩ =
        representation (family j) ⟨t.val, by omega⟩)
    (hb : ∀ i, ∃ j, ∀ t : Fin 4,
      representation (b * family i * b⁻¹) ⟨t.val, by omega⟩ =
        representation (family j) ⟨t.val, by omega⟩)
    (hrows : ∀ k : Fin 17, k = 1 ∨ k = 3 → ∀ i,
      (∃ (r : Fin 7) (p : Fin 2058),
        representation (relationWord (family i) (family i * (a * b) ^ k.val) r) p ≠ p) ∨
      ∃ p : Fin 2058, PairFixes (family i) (family i * (a * b) ^ k.val) p) :
    ClassCalculation seed := by
  apply classCalculation_of_closed_family family seed
  · obtain ⟨i, hi⟩ := hseed
    exact ⟨i, eq_of_four_point_images hi⟩
  · intro i
    obtain ⟨j, hj⟩ := ha i
    exact ⟨j, eq_of_four_point_images hj⟩
  · intro i
    obtain ⟨j, hj⟩ := hb i
    exact ⟨j, eq_of_four_point_images hj⟩
  · intro k hk i hr
    rcases hrows k hk i with ⟨r, p, hmove⟩ | hfix
    · exact (hmove (by rw [hr r, map_one]; rfl)).elim
    · exact hfix

end Held.Realization.MarkedConjugacy.NormalizedPairs
