module

public import Theory.Representation.BinaryIrreducibleCentralizer
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.PrimeRankElementary

/-!
# Automorphism rank from an irreducible binary action

If a normal subgroup acts irreducibly in a faithful binary representation,
the ambient two-rank is at most the two-rank of its full automorphism group.
Every elementary abelian two-subgroup acts faithfully by conjugation: an
involution in its kernel would centralize the irreducible action, contradicting
Schur's lemma in characteristic two. The elementary-cardinality criterion
then gives the bound for the repository's prime-rank convention.

Source application: Aschbacher--Smith, *The Classification of Quasithin Groups*,
G.7.3, printed p.348 / PDF p.359, combined 1 March 2004 manuscript.
-/

public section

namespace Representation.BinaryIrreducibleCentralizer

/-- Conjugation on a normally and irreducibly acting subgroup bounds ambient
two-rank, even when conjugation on the entire ambient group has a kernel. -/
theorem primeRank_le_automorphisms {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    [Representation.IsIrreducible (ρ.comp L.subtype)] (hf : Function.Injective ρ) :
    primeRank 2 G ≤ primeRank 2 (MulAut L) := by
  apply (primeRank_le_iff_elementary_card_le G).mpr
  intro E hE
  let : IsElementaryAbelian 2 E := hE
  have hn : E ≤ Subgroup.normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  let f := L.normalizerMonoidHom.comp (Subgroup.inclusion hn)
  have hf' : Function.Injective f := elementary_conjugation_injective ρ L hf E hn
  have himage : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hc := (primeRank_le_iff_elementary_card_le (MulAut L)).mp le_rfl f.range himage
  exact (Nat.card_congr (MonoidHom.ofInjective hf').toEquiv).le.trans hc

end Representation.BinaryIrreducibleCentralizer
