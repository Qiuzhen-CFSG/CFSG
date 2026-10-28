module

public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.Conjugation
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.Reductions
public import CFSG.Quasithin.Chapter16.Section04To05.RankTwo.Counting

/-!
# Rank-two deductions for the last intersection argument

The local Sylow exclusion is connected here to the general product
obstruction of 16.5.6(5), using the conjugation bridge and the detector
proved from 16.4.9(1). The printed final citation to 16.5.10(6) does not
apply to Lie rank two over fields larger than two.

The long-root normalizer construction, the covered G₂(4) action argument,
and the Sp₄ configuration remain needed to prove the local exclusion.
Consequently this module does not yet assert source Lemma 16.5.13 or
the final exceptional-model alternative. The auxiliary modules prove
the normalizer transport, TI counting obstruction, and elementary
order-four lift obstruction with their inputs explicit.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.1197 and 1201–1203.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A local exclusion in one fixed Sylow subgroup suffices for the terminal
product obstruction. The local exclusion remains a mathematical premise;
it must be supplied by the rank-two model arguments. -/
theorem projected_product_eq_one_of_local_sylow_exclusion
    (T : Sylow 2 G) {L X W : Subgroup G} {g l u c v : G}
    (hTN : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hNK : normalizer (centralizer (L : Set G) : Set G) =
      normalizer (L : Set G))
    (hdisjoint : Disjoint L (centralizer (L : Set G)))
    (hsmall : ∀ J ∈ delta L, J ∉ deltaZero L →
      ∀ R : Subgroup G, SylowIn R
        (J ⊓ normalizer (centralizer (L : Set G) : Set G)) → Nat.card R = 2)
    (hlocal : ∀ J ∈ deltaZero L, ∀ R : Subgroup G,
      SylowIn R (J ⊓ normalizer (centralizer (L : Set G) : Set G)) →
      R ≤ (T : Subgroup G) → ∀ i k w : G,
      i ∈ R → orderOf i = 2 → k ∈ centralizer (L : Set G) →
      w ∈ L → i = k * w → ¬ IsTwoCentralIn L w)
    (hXL : X ≤ L) (hWX : W ≤ X)
    (hgX : g ∈ normalizer (X : Set G)) (hgW : g ∈ normalizer (W : Set G))
    (hu : u ∈ (centralizer (L : Set G)).conjBy g) (hu2 : orderOf u = 2)
    (hc : c ∈ centralizer (L : Set G)) (hc2 : c * c = 1)
    (hv : v ∈ L) (hl : l ∈ L) (hucv : u = c * v)
    (hcentral : ∀ w ∈ W, w ≠ 1 → IsTwoCentralIn L w)
    (hw : v * MulAut.conj l v ∈ W) : v * MulAut.conj l v = 1 := by
  have hdetect : ∀ J : Subgroup G,
      (∃ a : G, J = (centralizer (L : Set G)).conjBy a) →
      ∀ i : G, i ∈ J → orderOf i = 2 →
      i ∈ centralizer (L : Set G) ⊔ L → i ∉ centralizer (L : Set G) →
      J ∈ deltaZero L := by
    intro J hJ i hi hi2 hiKL hiK
    exact mem_deltaZero_of_inner_involution hNK hsmall hJ (i := i) hi hi2 hiKL hiK
  exact projected_product_eq_one_of_mem hdisjoint hXL hWX hgX hgW hu hu2
    hc hc2 hv hl hucv hcentral hdetect
    (no_twoCentral_projection_of_sylow_exclusion T hTN hNK hdisjoint hdetect hlocal) hw

end CFSG.Quasithin.Chapter16.Intersections
