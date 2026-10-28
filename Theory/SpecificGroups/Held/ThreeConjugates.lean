module

public import Theory.SpecificGroups.Held.ThreeConjugates.Certificates
public import Theory.SpecificGroups.Held.ThreeConjugates.Transport
public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Coverage
public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.Fusion

/-!
# Three-conjugate generation for every involutory Held automorphism

The checked representative triples contain the actual Held generators.
The exhaustive two-class inner fusion and one-class outer fusion transport
these triples to every nonidentity square-one automorphism. The only premise
is realization of abstract automorphisms in the full permutation normalizer;
no generation, rank, simplicity, or group-order premise remains.

Source: Revin–Zavarnitsine, *Conjugate generation of sporadic almost simple
groups*, arXiv:2505.05173v2, Theorems 1–2 and the Held case of Proposition 2.
This is the geometry used for the degree bound in Aschbacher–Smith, Chapter K,
printed pp.451 and 457. Realization and the rank bound have separate producers.
-/

public section
namespace Held
open Subgroup LocalPairs ThreeConjugates

private theorem seed_hasTriple (r : Fin 3) :
    HasTriple (permutationGroup.normalizerMonoidHom (seed r)) :=
  hasTriple_of_normalizer _ _ _ (seed_generates r)

/-- Every nonidentity involutory automorphism has three inner conjugates
generating a subgroup containing the whole inner automorphism group.
Only full realization in the actual permutation normalizer is assumed. -/
theorem threeConjugateAutomorphisms
    (hreal : Function.Surjective permutationGroup.normalizerMonoidHom) :
    Theory.GroupTheory.ThreeConjugateAutomorphisms He := by
  intro t ht ht2
  have horder : orderOf t = 2 := orderOf_eq_prime ht2 ht
  change HasTriple t
  by_cases hin : ∃ x : He, MulAut.conj x = t
  · obtain ⟨x, rfl⟩ := hin
    have hx : orderOf x = 2 := (InvolutionFixedData.orderOf_conj x).symm.trans horder
    rcases InvolutionFixedData.Coverage.innerInvolutionCoverage x hx with
      ⟨c, hc⟩ | ⟨c, hc⟩
    · have hs : HasTriple (MulAut.conj a) := by
        simpa only [seed, normalizerAction_innerEmbedding] using seed_hasTriple 0
      simpa only [MulAut.congr_conj, hc] using hasTriple_congr hs (MulAut.conj c)
    · have hs : HasTriple (MulAut.conj (TwoLocalCandidates.max5First ^ 4)) := by
        simpa only [seed, normalizerAction_innerEmbedding, TwoLocalCandidates.max5First]
          using seed_hasTriple 1
      simpa only [MulAut.congr_conj, hc] using hasTriple_congr hs (MulAut.conj c)
  · obtain ⟨n, rfl⟩ := hreal t
    obtain ⟨c, hc⟩ := OuterInvolution.Fusion.conjugacy_coverage n horder hin
    have hs : HasTriple OuterInvolution.action := seed_hasTriple 2
    exact hc ▸ hasTriple_congr hs (MulAut.conj c)

end Held
