module

public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Binary.Setup

/-!
# Diagonal products in the binary-five residual

For the PSL₅(2) residual, the two order-four factors D=[V,X] and E=C_V(X)
consist of non-two-central involutions, whereas products of nonidentity
members of both factors are two-central. The latter set is not a subgroup,
so the subgroup formulation of the terminal product obstruction does not
apply to V. This lemma instead transports the two factors separately.

A model witness v vˡ = de yields u uˡ = de. The earlier fusion calculation
conjugates this product back into a new Δ₀ conjugate. Since the chosen g
normalizes both factors, its projection remains a mixed product and hence
two-central, contradicting 16.5.10(5).

This is conditional on the intrinsic two-factor geometry and product
witness. Their construction in the actual PSL₅(2) residual remains required.
No identification of the two-residual with an elementary kernel is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
p.1200, the PSL₅(2) paragraph of the proof of Lemma 16.5.12.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary

open Subgroup

/-- The two-factor version of the conjugate-product obstruction. The
intrinsic geometry must supply the factors and the nonidentity product. -/
theorem diagonal_product_obstruction {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {z u g : G} {L R X D E : Subgroup G}
    (h : EarlierInputs T z L g R X u)
    (hdisjoint : Disjoint L (centralizer (L : Set G)))
    (hDX : D ≤ X) (hEX : E ≤ X)
    (hgD : g ∈ normalizer (D : Set G)) (hgE : g ∈ normalizer (E : Set G))
    (hdiagonal : ∀ d ∈ D, d ≠ 1 → ∀ e ∈ E, e ≠ 1 → IsTwoCentralIn L (d * e))
    {c v l d e : G}
    (hc : c ∈ centralizer (L : Set G)) (hc2 : c * c = 1)
    (hv : v ∈ L) (hl : l ∈ L) (hucv : u = c * v)
    (hd : d ∈ D) (hd1 : d ≠ 1) (he : e ∈ E) (he1 : e ≠ 1)
    (hproduct : v * MulAut.conj l v = d * e) : False := by
  have hXL : X ≤ L := by
    rw [h.residual_at_actor u h.mem_actor h.actor_involution]
    exact (map_subtype_le _).trans inf_le_left
  have hw2 := (hdiagonal d hd hd1 e he he1).1
  have hw1 : d * e ≠ 1 := by intro hw; simp [hw] at hw2
  have hwX : d * e ∈ X := X.mul_mem (hDX hd) (hEX he)
  have hcalc : d * e = u * MulAut.conj l u := by
    rw [hucv, product_of_projected_involutions hc hc2 hv hl, hproduct]
  obtain ⟨J, i, k, hJ, hiJ, hi2, hk, hi, hqL, _⟩ :=
    exists_inner_involution_of_product hdisjoint hXL h.conjugator_normalizes_residual
      (h.sylow.le h.mem_actor).1 h.actor_involution hwX hw1 hcalc h.detect
  have hd' : MulAut.conj g⁻¹ d ∈ D :=
    (mem_normalizer_iff.mp ((normalizer (D : Set G)).inv_mem hgD) d).mp hd
  have he' : MulAut.conj g⁻¹ e ∈ E :=
    (mem_normalizer_iff.mp ((normalizer (E : Set G)).inv_mem hgE) e).mp he
  have hd1' : MulAut.conj g⁻¹ d ≠ 1 := by
    intro hd0
    exact hd1 ((MulAut.conj g⁻¹).injective (hd0.trans (map_one _).symm))
  have he1' : MulAut.conj g⁻¹ e ≠ 1 := by
    intro he0
    exact he1 ((MulAut.conj g⁻¹).injective (he0.trans (map_one _).symm))
  have htwo : IsTwoCentralIn L (MulAut.conj g⁻¹ (d * e)) := by
    rw [map_mul]
    exact hdiagonal _ hd' hd1' _ he' he1'
  exact h.avoid_twoCentral hdisjoint J hJ i k _ hiJ hi2 hk hqL hi htwo

end CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.Binary
