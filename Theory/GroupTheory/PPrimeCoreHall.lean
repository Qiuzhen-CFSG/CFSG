module

public import Theory.PPrimeCore
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Normal Hall prime-complement subgroups are intrinsic

A normal subgroup of order coprime to `p` and index a power of `p` is
the `p'`-core. Its containment in the core follows from normality; Lagrange's
theorem and coprimality give the reverse cardinality inequality.
Consequently, if such a subgroup occurs inside a centralizer, the normalizer
of the centralized subgroup preserves it.

This is the intrinsic odd-core identification used in Alperin--Brauer--
Gorenstein, III.8 Proposition 5, article p.117.
-/

namespace Subgroup

/-- A normal Hall `p'`-subgroup is the `p'`-core. -/
public theorem eq_pPrimeCore_of_card_mul
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (R : Subgroup G) [R.Normal] (hR : Nat.Coprime p (Nat.card R))
    (n : ℕ) (hcard : Nat.card G = p ^ n * Nat.card R) :
    R = pPrimeCore p G := by
  have hle : R ≤ pPrimeCore p G := le_sSup ⟨inferInstance, hR⟩
  have hd : Nat.card (pPrimeCore p G) ∣ Nat.card R := by
    have hdiv := card_subgroup_dvd_card (pPrimeCore p G)
    rw [hcard] at hdiv
    exact (pPrimeCore_coprime_card (p := p) (G := G)).symm.pow_right n
      |>.dvd_of_dvd_mul_left hdiv
  exact eq_of_le_of_card_ge hle (Nat.le_of_dvd Nat.card_pos hd)

/-- A normal Hall `p'`-subgroup of a centralizer is preserved by the
normalizer of the centralized subgroup. -/
public theorem normalizer_le_normalizer_of_centralizer_hall
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (T R : Subgroup G) (hRC : R ≤ centralizer (T : Set G))
    (hCN : centralizer (T : Set G) ≤ normalizer (R : Set G))
    (hR : Nat.Coprime p (Nat.card R)) (n : ℕ)
    (hcard : Nat.card (centralizer (T : Set G)) = p ^ n * Nat.card R) :
    normalizer (T : Set G) ≤ normalizer (R : Set G) := by
  let C := centralizer (T : Set G)
  let _ : (R.subgroupOf C).Normal :=
    (normal_subgroupOf_iff_le_normalizer hRC).mpr hCN
  have hc : Nat.card (R.subgroupOf C) = Nat.card R :=
    Nat.card_congr (subgroupOfEquivOfLe hRC).toEquiv
  have heq : R.subgroupOf C = pPrimeCore p C :=
    eq_pPrimeCore_of_card_mul p (R.subgroupOf C) (by rwa [hc]) n (by rwa [hc])
  have himage : (pPrimeCore p C).map C.subtype = R := by
    rw [← heq, map_subgroupOf_eq_of_le hRC]
  rw [← himage]
  exact (normalizer_le_normalizer_centralizer T).trans
    (normalizer_le_normalizer_characteristic_image C (pPrimeCore p C))

end Subgroup
