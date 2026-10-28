module

public import CFSG.Quasithin.Chapter16.Section04To05.Fusion

/-!
# The final conjugate-product obstruction

The last paragraph before Theorem 16.5.14 produces a nonidentity product
v vˡ in a characteristic subgroup W of the common residual X. All nonidentity
elements of W are two-central involutions. Since the chosen conjugator
normalizes X and W, the calculation in 16.5.6(5) produces an inner involution
in another member of Δ₀ whose projection is two-central, a contradiction.

This is a conditional group-theoretic deduction, not Theorem 16.5.14. The
model-specific product and the exclusion of two-central projections are
explicit separate obligations. In particular, the rank-two cases cannot
simply apply 16.5.10(6), whose printed hypothesis excludes rank two over
fields larger than two; they require the general 16.5.6(5) argument with
the long-root exclusion established in 16.5.13.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, pp.1197,
1201–1203. Conjugation is left conjugation.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections

open Subgroup

variable {G : Type*} [Group G]

/-- An involution central in an actual Sylow two-subgroup of L. -/
def IsTwoCentralIn (L : Subgroup G) (v : G) : Prop :=
  orderOf v = 2 ∧ ∃ S : Subgroup G, SylowIn S L ∧ v ∈ S ∧
    S ≤ centralizer ({v} : Set G)

/-- The fusion obstruction applied to a conjugator-invariant subgroup of
two-central involutions. The model proofs must produce a nonidentity product
in W and the source setup must discharge `hdetect` and `havoid`. -/
theorem projected_product_eq_one_of_mem
    {L X W : Subgroup G} {g l u c v : G}
    (hdisjoint : Disjoint L (centralizer (L : Set G)))
    (hXL : X ≤ L) (hWX : W ≤ X)
    (hgX : g ∈ normalizer (X : Set G)) (hgW : g ∈ normalizer (W : Set G))
    (hu : u ∈ (centralizer (L : Set G)).conjBy g) (hu2 : orderOf u = 2)
    (hc : c ∈ centralizer (L : Set G)) (hc2 : c * c = 1)
    (hv : v ∈ L) (hl : l ∈ L) (hucv : u = c * v)
    (hcentral : ∀ w ∈ W, w ≠ 1 → IsTwoCentralIn L w)
    (hdetect : ∀ (J : Subgroup G),
      (∃ a : G, J = (centralizer (L : Set G)).conjBy a) →
      ∀ i : G, i ∈ J → orderOf i = 2 →
        i ∈ centralizer (L : Set G) ⊔ L → i ∉ centralizer (L : Set G) →
        J ∈ deltaZero L)
    (havoid : ∀ J ∈ deltaZero L, ∀ i k w : G,
      i ∈ J → orderOf i = 2 → k ∈ centralizer (L : Set G) →
      w ∈ L → i = k * w → ¬ IsTwoCentralIn L w)
    (hw : v * MulAut.conj l v ∈ W) : v * MulAut.conj l v = 1 := by
  by_contra hne
  have hprod : v * MulAut.conj l v = u * MulAut.conj l u := by
    rw [hucv, product_of_projected_involutions hc hc2 hv hl]
  obtain ⟨J, i, k, hJ, hiJ, hi2, hk, hi, hqL, hq1⟩ :=
    exists_inner_involution_of_product hdisjoint hXL hgX hu hu2 (hWX hw)
      hne hprod hdetect
  have hqW : MulAut.conj g⁻¹ (v * MulAut.conj l v) ∈ W :=
    (mem_normalizer_iff.mp ((normalizer (W : Set G)).inv_mem hgW) _).mp hw
  exact havoid J hJ i k _ hiJ hi2 hk hqL hi (hcentral _ hqW hq1)

end CFSG.Quasithin.Chapter16.Intersections
