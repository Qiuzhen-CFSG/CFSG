module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.CentralHigherGeneration.Scalars

/-!
# Exchange of the first two short folded roots

Collecting the six factors in orbits (0,1,2) and (4,5,6) using the checked
D₄ sum table gives orbit (7,8,9) with leading coefficient s F(t) + F(s) t.
The remaining factors are the singleton positions 10 and 11 with coefficients
Tr(s F(s) F²(t)) and Tr(s F(t) F²(t)), respectively. Thus all corrections
are actual fixed-field root elements. The word calculation is performed in an
abstract group to avoid unfolding concrete Geck matrices during rewriting,
then instantiated with the proved `SumExchange` and `NonsumCommute` identities.
The identity is transported through the elementary inclusion and central
quotient to `Carrier P`.

Source: GLS3 2.4.5(b)(4) and §2.6 (`refs/KGroup/GLS3/chapter2.tex`),
with the exact orbit ordering of `FoldedRoots.lean`; used in
Aschbacher–Smith F.1.12(II), printed pp.263–264.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.RadicalCoordinates.LeviCommutators
open Parabolics PositiveCoordinates PositiveCoordinates.SumExchangeData Centers

private theorem exchange_tail {F G : Type*} [Mul F] [Group G]
    (x : Fin 12 → F → G)
    (hx : ∀ i j k, (i,j,k) ∈ sumTriples → ∀ a b,
      x i a * x j b = x j b * x i a * x k (a * b))
    (i j k : Fin 12) (h : (i,j,k) ∈ sumTriples)
    (a b : F) (g : G) :
    x i a * (x j b * g) = x j b * (x i a * (x k (a * b) * g)) := by
  rw [← mul_assoc, hx i j k h]
  simp only [mul_assoc]

private theorem commute_tail {F G : Type*} [Group G]
    (x : Fin 12 → F → G)
    (hx : ∀ i j, i ≠ j → (∀ k, (i,j,k) ∉ sumTriples) → ∀ a b,
      Commute (x i a) (x j b))
    (i j : Fin 12) (hij : i ≠ j) (h : ∀ k, (i,j,k) ∉ sumTriples)
    (a b : F) (g : G) :
    x i a * (x j b * g) = x j b * (x i a * g) := by
  rw [← mul_assoc, (hx i j hij h a b).eq, mul_assoc]

private theorem add_tail {F G : Type*} [Add F] [Group G]
    (x : Fin 12 → F → G) (hx : ∀ i a b, x i (a + b) = x i a * x i b)
    (i : Fin 12) (a b : F) (g : G) :
    x i a * (x i b * g) = x i (a + b) * g := by
  rw [← mul_assoc, ← hx]

private theorem six_curve_collection {F G : Type*} [Add F] [Mul F] [Group G]
    (x : Fin 12 → F → G) (ha : ∀ i a b, x i (a + b) = x i a * x i b)
    (hs : ∀ i j k, (i,j,k) ∈ sumTriples → ∀ a b,
      x i a * x j b = x j b * x i a * x k (a * b))
    (hc : ∀ i j, i ≠ j → (∀ k, (i,j,k) ∉ sumTriples) → ∀ a b,
      Commute (x i a) (x j b))
    (a b c d e f : F) :
    x 0 a * x 1 b * x 2 c *
      x 4 d * x 5 e * x 6 f =
      x 4 d *
      x 5 e *
      x 6 f *
      x 0 a *
      x 1 b *
      x 2 c *
      x 7 ((a * e) + (b * d)) *
      x 8 ((b * f) + (c * e)) *
      x 9 ((a * f) + (c * d)) *
      x 10 (((a * f) * b) + (((a * e) * c) + ((b * d) * c))) *
      x 11 ((((a * e) + (b * d)) * f) + ((c * d) * e)) := by
  suffices h :
      x 0 a * x 1 b * x 2 c *
        x 4 d * x 5 e * x 6 f * 1 =
      x 4 d *
      x 5 e *
      x 6 f *
      x 0 a *
      x 1 b *
      x 2 c *
      x 7 ((a * e) + (b * d)) *
      x 8 ((b * f) + (c * e)) *
      x 9 ((a * f) + (c * d)) *
      x 10 (((a * f) * b) + (((a * e) * c) + ((b * d) * c))) *
      x 11 ((((a * e) + (b * d)) * f) + ((c * d) * e)) * 1 by simpa only [mul_one] using h
  simp only [mul_assoc]
  conv_lhs =>
    rw [exchange_tail x hs 2 4 9 (by decide) c d]
    rw [exchange_tail x hs 1 4 7 (by decide) b d]
    rw [commute_tail x hc 0 4 (by decide) (by decide) a d]
    rw [exchange_tail x hs 7 2 10 (by decide) (b * d) c]
    rw [commute_tail x hc 10 9 (by decide) (by decide) ((b * d) * c) (c * d)]
    rw [commute_tail x hc 10 5 (by decide) (by decide) ((b * d) * c) e]
    rw [exchange_tail x hs 9 5 11 (by decide) (c * d) e]
    rw [commute_tail x hc 7 5 (by decide) (by decide) (b * d) e]
    rw [exchange_tail x hs 2 5 8 (by decide) c e]
    rw [commute_tail x hc 1 5 (by decide) (by decide) b e]
    rw [exchange_tail x hs 0 5 7 (by decide) a e]
    rw [commute_tail x hc 7 1 (by decide) (by decide) (a * e) b]
    rw [exchange_tail x hs 7 2 10 (by decide) (a * e) c]
    rw [commute_tail x hc 10 8 (by decide) (by decide) ((a * e) * c) (c * e)]
    rw [commute_tail x hc 10 7 (by decide) (by decide) ((a * e) * c) (b * d)]
    rw [commute_tail x hc 8 7 (by decide) (by decide) (c * e) (b * d)]
    rw [add_tail x ha 7 (a * e) (b * d)]
    rw [commute_tail x hc 10 9 (by decide) (by decide) ((a * e) * c) (c * d)]
    rw [commute_tail x hc 11 10 (by decide) (by decide) ((c * d) * e) ((b * d) * c)]
    rw [add_tail x ha 10 ((a * e) * c) ((b * d) * c)]
    rw [commute_tail x hc 11 6 (by decide) (by decide) ((c * d) * e) f]
    rw [commute_tail x hc 10 6 (by decide) (by decide) (((a * e) * c) + ((b * d) * c)) f]
    rw [commute_tail x hc 9 6 (by decide) (by decide) (c * d) f]
    rw [commute_tail x hc 8 6 (by decide) (by decide) (c * e) f]
    rw [exchange_tail x hs 7 6 11 (by decide) ((a * e) + (b * d)) f]
    rw [commute_tail x hc 2 6 (by decide) (by decide) c f]
    rw [exchange_tail x hs 1 6 8 (by decide) b f]
    rw [exchange_tail x hs 0 6 9 (by decide) a f]
    rw [exchange_tail x hs 9 1 10 (by decide) (a * f) b]
    rw [commute_tail x hc 10 8 (by decide) (by decide) ((a * f) * b) (b * f)]
    rw [commute_tail x hc 9 8 (by decide) (by decide) (a * f) (b * f)]
    rw [commute_tail x hc 10 2 (by decide) (by decide) ((a * f) * b) c]
    rw [commute_tail x hc 9 2 (by decide) (by decide) (a * f) c]
    rw [commute_tail x hc 8 2 (by decide) (by decide) (b * f) c]
    rw [commute_tail x hc 10 7 (by decide) (by decide) ((a * f) * b) ((a * e) + (b * d))]
    rw [commute_tail x hc 9 7 (by decide) (by decide) (a * f) ((a * e) + (b * d))]
    rw [commute_tail x hc 8 7 (by decide) (by decide) (b * f) ((a * e) + (b * d))]
    rw [commute_tail x hc 11 8 (by decide) (by decide) (((a * e) + (b * d)) * f) (c * e)]
    rw [commute_tail x hc 10 8 (by decide) (by decide) ((a * f) * b) (c * e)]
    rw [commute_tail x hc 9 8 (by decide) (by decide) (a * f) (c * e)]
    rw [add_tail x ha 8 (b * f) (c * e)]
    rw [commute_tail x hc 11 9 (by decide) (by decide) (((a * e) + (b * d)) * f) (c * d)]
    rw [commute_tail x hc 10 9 (by decide) (by decide) ((a * f) * b) (c * d)]
    rw [add_tail x ha 9 (a * f) (c * d)]
    rw [commute_tail x hc 11 10 (by decide) (by decide) (((a * e) + (b * d)) * f) (((a * e) * c) + ((b * d) * c))]
    rw [add_tail x ha 10 ((a * f) * b) (((a * e) * c) + ((b * d) * c))]
    rw [add_tail x ha 11 (((a * e) + (b * d)) * f) ((c * d) * e)]


private theorem folded_collection (P : Parameters) {G : Type*} [Group G]
    (x : Fin 12 → ExtensionField P → G)
    (ha : ∀ i a b, x i (a + b) = x i a * x i b)
    (hs : ∀ i j k, (i,j,k) ∈ sumTriples → ∀ a b,
      x i a * x j b = x j b * x i a * x k (a * b))
    (hc : ∀ i j, i ≠ j → (∀ k, (i,j,k) ∉ sumTriples) → ∀ a b,
      Commute (x i a) (x j b))
    (s t : ExtensionField P) :
    (x 0 s * x 1 (fieldFrobenius P s) * x 2 (fieldFrobenius P (fieldFrobenius P s))) *
      (x 4 t * x 5 (fieldFrobenius P t) * x 6 (fieldFrobenius P (fieldFrobenius P t))) =
    (x 4 t * x 5 (fieldFrobenius P t) * x 6 (fieldFrobenius P (fieldFrobenius P t))) *
      (x 0 s * x 1 (fieldFrobenius P s) * x 2 (fieldFrobenius P (fieldFrobenius P s))) *
      (x 7 (higherCoefficient P s t) * x 8 (fieldFrobenius P (higherCoefficient P s t)) *
        x 9 (fieldFrobenius P (fieldFrobenius P (higherCoefficient P s t)))) *
      x 10 (cubicTrace P (s * fieldFrobenius P s *
        fieldFrobenius P (fieldFrobenius P t))).val *
      x 11 (cubicTrace P (s * fieldFrobenius P t *
        fieldFrobenius P (fieldFrobenius P t))).val := by
  have he := six_curve_collection x ha hs hc
    s (fieldFrobenius P s) (fieldFrobenius P (fieldFrobenius P s))
    t (fieldFrobenius P t) (fieldFrobenius P (fieldFrobenius P t))
  have h8 : fieldFrobenius P s * fieldFrobenius P (fieldFrobenius P t) +
      fieldFrobenius P (fieldFrobenius P s) * fieldFrobenius P t =
      fieldFrobenius P (higherCoefficient P s t) := by
    simp only [higherCoefficient, map_add, map_mul]
  have h9 : s * fieldFrobenius P (fieldFrobenius P t) +
      fieldFrobenius P (fieldFrobenius P s) * t =
      fieldFrobenius P (fieldFrobenius P (higherCoefficient P s t)) := by
    simp only [higherCoefficient, map_add, map_mul, fieldFrobenius_three]
    ring
  have h10 : (s * fieldFrobenius P (fieldFrobenius P t)) * fieldFrobenius P s +
      ((s * fieldFrobenius P t) * fieldFrobenius P (fieldFrobenius P s) +
        (fieldFrobenius P s * t) * fieldFrobenius P (fieldFrobenius P s)) =
      (cubicTrace P (s * fieldFrobenius P s *
        fieldFrobenius P (fieldFrobenius P t))).val := by
    simp only [cubicTrace_coe, map_mul, fieldFrobenius_three]
    ring
  have h11 : (s * fieldFrobenius P t + fieldFrobenius P s * t) *
      fieldFrobenius P (fieldFrobenius P t) +
      (fieldFrobenius P (fieldFrobenius P s) * t) * fieldFrobenius P t =
      (cubicTrace P (s * fieldFrobenius P t *
        fieldFrobenius P (fieldFrobenius P t))).val := by
    simp only [cubicTrace_coe, map_mul, fieldFrobenius_three]
    ring
  rw [h8, h9, h10, h11] at he
  simpa only [higherCoefficient, mul_assoc] using he

/-- The actual split Geck exchange. The two higher correction parameters are
cubic traces, hence belong to the fixed singleton root groups. -/
theorem shortSplit_zero_one_exchange (P : Parameters) (hp : P.prime = 2)
    (s t : ExtensionField P) :
    shortSplit P 0 s * shortSplit P 1 t =
      shortSplit P 1 t * shortSplit P 0 s * shortSplit P 2 (higherCoefficient P s t) *
        longSplit P 1 (cubicTrace P (s * fieldFrobenius P s *
          fieldFrobenius P (fieldFrobenius P t))) *
        longSplit P 2 (cubicTrace P (s * fieldFrobenius P t *
          fieldFrobenius P (fieldFrobenius P t))) := by
  have hs : SumExchange P := by
    obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
    exact sumExchange_binary n hn
  exact folded_collection P (curve P) (curve_add P)
    (fun i j k h => hs i j k ((root_sum_iff i j k).mpr ((mem_sumTriples_iff i j k).mp h)))
    (fun i j hij h => nonsumCommute_parameters P i j hij (by
      rintro ⟨k, hk⟩
      exact h k ((mem_sumTriples_iff i j k).mpr ((root_sum_iff i j k).mp hk)))) s t

/-- Descend the checked exchange to the genuine triality carrier. -/
theorem short_zero_one_exchange (P : Parameters) (hp : P.prime = 2)
    (s t : ExtensionField P) :
    short P hp 0 s * short P hp 1 t =
      short P hp 1 t * short P hp 0 s * short P hp 2 (higherCoefficient P s t) *
        long P hp 1 (cubicTrace P (s * fieldFrobenius P s *
          fieldFrobenius P (fieldFrobenius P t))) *
        long P hp 2 (cubicTrace P (s * fieldFrobenius P t *
          fieldFrobenius P (fieldFrobenius P t))) := by
  simp only [short, long, ← map_mul]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, shortElementary_val, longElementary_val]
  exact shortSplit_zero_one_exchange P hp s t


end Triality.Standard.RadicalCoordinates.LeviCommutators
