module

public import CFSG.Quasithin.Chapter16.Section04To05.Terminal

/-!
# Products from the noncentral involution coset

In the last paragraph of 16.5.11, the local model supplies an involution
x in X and conjugacy of the involutions in vX to v. Since v centralizes X,
vx is an involution; choosing l with vˡ = vx gives vvˡ = x. This constructs
the product used by the earlier fusion obstruction, rather than assuming it.

The final theorem below is conditional on the genuine earlier Δ₀ detector
and exclusion of two-central projections, and on the stated intrinsic
coset-fusion data. It is not an assertion of either numbered source lemma.
The model and covering cases must establish these inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.1199–1200, proof of Lemma 16.5.11. All conjugations are left conjugations.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.NonRankTwo

open Subgroup

variable {G : Type*} [Group G]

/-- The intrinsic coset-fusion assertion used for M₁₂, J₂, HS and Ru.
This is data to prove in the actual model, not a family label. -/
def InvolutionCosetFusion (L X : Subgroup G) (v : G) : Prop :=
  ∀ x ∈ X, orderOf (v * x) = 2 → ∃ l ∈ L, MulAut.conj l v = v * x

/-- A nonidentity involution of X gives the required conjugate product.
The condition v ∉ X rules out the degenerate product vx = 1. -/
theorem exists_product_of_involution_coset_fusion
    {L X : Subgroup G} {v x : G}
    (hv2 : orderOf v = 2) (hvX : v ∉ X)
    (hcentral : v ∈ centralizer (X : Set G))
    (hxX : x ∈ X) (hx2 : orderOf x = 2)
    (hfuse : InvolutionCosetFusion L X v) :
    ∃ l ∈ L, v * MulAut.conj l v = x := by
  have hvpow : v ^ 2 = 1 := by rw [← hv2, pow_orderOf_eq_one]
  have hxpow : x ^ 2 = 1 := by rw [← hx2, pow_orderOf_eq_one]
  have hcomm : Commute v x := (mem_centralizer_iff.mp hcentral x hxX).symm
  have hvxpow : (v * x) ^ 2 = 1 := by rw [hcomm.mul_pow, hvpow, hxpow, one_mul]
  have hvxne : v * x ≠ 1 := by
    intro he
    exact hvX ((eq_inv_of_mul_eq_one_left he).symm ▸ X.inv_mem hxX)
  have hvx2 : orderOf (v * x) = 2 := orderOf_eq_prime_iff.mpr ⟨hvxpow, hvxne⟩
  obtain ⟨l, hl, he⟩ := hfuse x hxX hvx2
  refine ⟨l, hl, ?_⟩
  rw [he, ← mul_assoc, ← pow_two, hvpow, one_mul]

/-- A residual containing an involution and having the printed coset fusion
cannot consist of two-central involutions in this Δ₀ configuration.
The nonidentity product is constructed from fusion, not included as an input. -/
theorem coset_fusion_obstruction
    {L X : Subgroup G} {g u c v : G}
    (hdisjoint : Disjoint L (centralizer (L : Set G)))
    (hXL : X ≤ L) (hgX : g ∈ normalizer (X : Set G))
    (hu : u ∈ (centralizer (L : Set G)).conjBy g) (hu2 : orderOf u = 2)
    (hc : c ∈ centralizer (L : Set G)) (hc2 : c * c = 1)
    (hv : v ∈ L) (hv2 : orderOf v = 2) (hucv : u = c * v)
    (hvX : v ∉ X) (hcvX : v ∈ centralizer (X : Set G))
    (hinvolution : ∃ x ∈ X, orderOf x = 2)
    (hfuse : InvolutionCosetFusion L X v)
    (htwoCentral : ∀ x ∈ X, orderOf x = 2 → IsTwoCentralIn L x)
    (hdetect : ∀ (J : Subgroup G),
      (∃ a : G, J = (centralizer (L : Set G)).conjBy a) →
      ∀ i : G, i ∈ J → orderOf i = 2 →
        i ∈ centralizer (L : Set G) ⊔ L → i ∉ centralizer (L : Set G) →
        J ∈ deltaZero L)
    (havoid : ∀ J ∈ deltaZero L, ∀ i k w : G,
      i ∈ J → orderOf i = 2 → k ∈ centralizer (L : Set G) →
      w ∈ L → i = k * w → ¬ IsTwoCentralIn L w) : False := by
  obtain ⟨x, hxX, hx2⟩ := hinvolution
  obtain ⟨l, hl, he⟩ := exists_product_of_involution_coset_fusion
    hv2 hvX hcvX hxX hx2 hfuse
  have hx1 : x ≠ 1 := by intro h; simp [h] at hx2
  have hprod : x = u * MulAut.conj l u := by
    rw [hucv, product_of_projected_involutions hc hc2 hv hl, he]
  obtain ⟨J, i, k, hJ, hiJ, hi2, hk, hi, hqL, _⟩ :=
    exists_inner_involution_of_product hdisjoint hXL hgX hu hu2 hxX hx1 hprod hdetect
  have hqX : MulAut.conj g⁻¹ x ∈ X :=
    (mem_normalizer_iff.mp ((normalizer (X : Set G)).inv_mem hgX) x).mp hxX
  have hq2 : orderOf (MulAut.conj g⁻¹ x) = 2 := by
    rw [(MulAut.conj g⁻¹).orderOf_eq, hx2]
  exact havoid J hJ i k _ hiJ hi2 hk hqL hi (htwoCentral _ hqX hq2)

end CFSG.Quasithin.Chapter16.Intersections.NonRankTwo
