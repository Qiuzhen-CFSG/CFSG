module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.WordExchange.RootFactors

/-!
# Exchange from relative root collection and rank-one Gauss decomposition

Write a Borel element as `b₀ x`, where the reflection conjugates `b₀`
back into the Borel and `x` belongs to the complete positive simple block.
If the normalizer conjugates this block positively, move `x` to the right.
In the opposite sign case, the identity parameter is immediate and the
nonidentity parameter uses the rank-one Gauss equation. Its second root
factor moves to the right after reflection, while its fixed torus factor
stays in the left Borel.

The three geometric inputs are explicit here. The owning `WordExchange`
module discharges them using only its two normalizer matrix hypotheses.
No normality instance on a quotient is required.
Source: the exchange calculation in GLS3 2.3.4(b), using 2.3.7–8 and §2.4,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.SectionGeometry.BNPair
open Subgroup LargeLocalSeeds Parabolics Parabolics.Binary.FixedGeometry
open scoped Pointwise

private theorem mem_cell (m : ℕ) (n a b : Model m)
    (ha : a ∈ borel m) (hb : b ∈ borel m) : a * n * b ∈ borelCell m n :=
  ⟨a * n, ⟨a, ha, n, Set.mem_singleton n, rfl⟩, b, hb, rfl⟩

private theorem left_mul_mem_cell (m : ℕ) (n a x : Model m)
    (ha : a ∈ borel m) (hx : x ∈ borelCell m n) : a * x ∈ borelCell m n := by
  rcases hx with ⟨z, ⟨l, hl, k, hk, rfl⟩, r, hr, rfl⟩
  rw [Set.mem_singleton_iff] at hk
  subst k
  simpa only [mul_assoc] using mem_cell m n (a * l) r ((borel m).mul_mem ha hl) hr

/-- The relative-root calculations imply the requested concrete word exchange.
This is an assembly lemma; its three geometric premises must be discharged. -/
theorem word_exchange_of_root_factors (m : ℕ)
    (hf : BorelSimpleFactorization m) (hg : RelativeRankOneGauss m)
    (hs : RelativeBlockSign m) :
    ∀ s : Side, ∀ n ∈ normalizerWords m, ∀ b ∈ borel m,
      weylLift m s * b * n ∈ borelCell m (weylLift m s * n) ∪ borelCell m n := by
  intro s n hn b hb
  let v := weylLift m s
  have hv : v * v = 1 := by simpa only [pow_two] using weylLift_sq m s
  obtain ⟨b₀, _, x, hx, rfl, h₀⟩ := hf s b hb
  have he : v * (b₀ * x) * n = (v * b₀ * v) * (v * x * n) := by
    symm
    calc
      _ = v * b₀ * (v * v) * x * n := by group
      _ = _ := by rw [hv]; group
  change v * (b₀ * x) * n ∈ _
  rw [he]
  suffices h : v * x * n ∈ borelCell m (v * n) ∪ borelCell m n by
    exact h.elim (fun h => Or.inl (left_mul_mem_cell m (v * n) _ _ h₀ h))
      (fun h => Or.inr (left_mul_mem_cell m n _ _ h₀ h))
  rcases hs s n hn with hp | hm
  · left
    convert mem_cell m (v * n) 1 (n⁻¹ * x * n) (borel m).one_mem (hp x hx) using 1
    group
  · by_cases hx1 : x = 1
    · left
      simpa only [hx1, mul_one, one_mul] using
        mem_cell m (v * n) 1 1 (borel m).one_mem (borel m).one_mem
    · right
      obtain ⟨a, ha, t, ht, y, hy, hxy⟩ := hg s x hx hx1
      have hc := mem_cell m n (a * t) (n⁻¹ * (v * y * v) * n)
        ((borel m).mul_mem (relativePositiveBlock_le_borel m s ha) (fixedTorus_le_borel m ht))
        (hm y hy)
      convert hc using 1
      calc
        v * x * n = (v * x * v) * v * n := by rw [mul_assoc (v * x), hv, mul_one]
        _ = (a * t * v * y) * v * n := by rw [hxy]
        _ = _ := by group

end ReeF4.SectionGeometry.BNPair
