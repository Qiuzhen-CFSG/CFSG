module

public import Stellmacher.Recognition.Parrott.DerivedCentralizer
public import Stellmacher.Recognition.Parrott.DerivedNormalizerOrder
public import Stellmacher.MainDefs
public import Theory.GroupTheory.ThirtyTwoAutomorphismNoEleven
public import Theory.GroupTheory.ElementaryThirtyTwoOrder6720
public import Theory.GroupTheory.ElementaryThirtyTwoOrder9920

/-!
# Parrott's derived-subgroup normalizer in an N₂ group

Let `G` be a finite N₂ group satisfying Parrott's original hypotheses at
an involution `z`. Put `H = C_G(z)`, `J = O₂(H)`, and let `E` be the
actual ambient image of `J'`. Then `N_G(E) = H`. The N₂ hypothesis means
that the normalizer of every nontrivial two-subgroup is solvable; no
simplicity or recognition conclusion is assumed.

The first lemma gives that `E` is elementary abelian of order 32, and the
preceding centralizer theorem gives `C_G(E) = E`. The canonical conjugation
homomorphism from `N_G(E)` into `Aut(E)` therefore has kernel of order 32.
The candidate-order theorem gives `|N_G(E)| = 10240 * n`, where
`n` is 1, 11, 21, or 31. Its solvable automorphism image has order `320 * n`.

Orbit counting excludes a factor 11 in automorphisms of any group of
order 32. Hall's theorem excludes image order 6720. At image order 9920,
irreducibility and the Fitting subgroup produce a normal subgroup of order
31, whose automorphism normalizer has odd order, a contradiction. Thus
`n = 1`. Characteristic transfer gives `H ≤ N_G(E)`, and equal orders give
the required equality.

Source: David Parrott, *A characterization of the Tits' simple group*
(1972), Lemma 2, p. 673, first assertion. This proves its N₂ specialization
using solvability in place of the source's full GL(5,2) subgroup exclusions.
-/

open Subgroup

namespace Stellmacher.Recognition

/-- In an N₂ group, the actual derived two-core normalizer is the given involution centralizer. -/
public theorem parrott_derived_normalizer_of_nTwo {G : Type*} [Group G] [Finite G]
    (hN : IsNTwoGroup G) (z : G) (h : ParrottCentralizerHypotheses z) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    normalizer (E : Set G) = H := by
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let D := commutator J
  let DH := D.map J.subtype
  let E := D.map (H.subtype.comp J.subtype)
  let N := normalizer (E : Set G)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change N = H
  have hcounts := parrott_derived_normalizer_card z h
  obtain ⟨_, _, _, _, _, hElem, hDcard, _⟩ := parrott_centralizer_structure z h
  change IsElementaryAbelian 2 D at hElem
  let : IsElementaryAbelian 2 D := hElem
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map (H.subtype.comp J.subtype)
  have hEcard : Nat.card E = 32 := by
    exact (card_map_of_injective (K := D) (f := H.subtype.comp J.subtype)
      (H.subtype_injective.comp J.subtype_injective)).trans hDcard
  have hEne : E ≠ ⊥ := by
    intro hbot
    rw [hbot, card_bot] at hEcard
    omega
  have hHN : H ≤ N := by
    let : DH.Characteristic := inferInstance
    have hnorm := le_normalizer_map (H := DH) H.subtype
    rw [normalizer_eq_top] at hnorm
    simpa only [← MonoidHom.range_eq_map, range_subtype, DH, map_map] using hnorm
  have hNsolv : Group.IsSolvable N := hN N ⟨E, hEne, IsElementaryAbelian.isPGroup 2 E, rfl⟩
  let : Group.IsSolvable N := hNsolv
  let f : N →* MulAut E := E.normalizerMonoidHom
  let K := f.range
  have hKsolv : Group.IsSolvable K := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hker : Nat.card f.ker = 32 := by
    rw [normalizerMonoidHom_ker, parrott_derived_centralizer z h]
    exact (Nat.card_congr (subgroupOfEquivOfLe (H := E) le_normalizer).toEquiv).trans hEcard
  obtain ⟨n, hn, hNcard⟩ := hcounts
  have hKcard : Nat.card K = 320 * n := by
    have hc := f.ker.card_mul_index
    rw [index_ker, hker, hNcard] at hc
    change 32 * Nat.card K = 10240 * n at hc
    omega
  have hn1 : n = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl | rfl | rfl
    · rfl
    · exfalso
      exact not_eleven_dvd_card_automorphism_thirtytwo hEcard K (by rw [hKcard]; decide)
    · exfalso
      exact Theory.GroupTheory.not_card6720_of_solvable_aut32 hEcard K hKsolv
        (by simpa using hKcard)
    · exfalso
      exact not_card9920_of_solvable_aut32 hEcard K hKsolv (by simpa using hKcard)
  have hHcard : Nat.card H = 10240 := (ParrottCentralizerHypotheses.card_and_solvable z h).1
  apply (eq_of_le_of_card_ge hHN _).symm
  rw [hNcard, hn1, hHcard]

end Stellmacher.Recognition
