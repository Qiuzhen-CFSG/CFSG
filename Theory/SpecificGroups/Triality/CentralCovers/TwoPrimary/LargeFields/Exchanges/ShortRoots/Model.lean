module
public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.LargeFields.Exchanges.LongRoots

/-!
# The remaining short-root carrier exchanges in the D₄ marking

Collect the actual root orbits (0,1,2), (4,5,6), (7,8,9) and the singleton
root 3 using the checked D₄ sum table. The two trace coefficients are
Tr(F²(s)t), the same cyclic trace as the arms pairing. The short0/long0
corrections are st, sF(s)t and N(s)t. The two highest-root contributions
cancel in characteristic two. Collection is proved in an abstract group
before specializing to the Geck curves, avoiding matrix expansion.

The final identities descend through the literal elementary inclusion and
central quotient to the genuine triality carrier.
Source: GLS3 §2.4.5(b)(2),(5), with the marking of `FoldedRoots.lean`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
@[expose] public section
noncomputable section
namespace Triality.Standard.CentralCovers.TwoPrimary.RootSections.ShortPolynomial
open Parabolics PositiveCoordinates PositiveCoordinates.SumExchangeData
open RadicalCoordinates.LeviCommutators RadicalCoordinates.Centers
private theorem swap_sum {F G : Type*} [Mul F] [Group G]
    (x : Fin 12 → F → G)
    (hs : ∀ i j k, (i,j,k) ∈ sumTriples → ∀ a b,
      x i a * x j b = x j b * x i a * x k (a*b))
    (i j k : Fin 12) (h : (i,j,k) ∈ sumTriples) (a b : F) (g : G) :
    x i a * (x j b * g) = x j b * (x i a * (x k (a*b)*g)) := by
  rw [← mul_assoc, hs i j k h]; simp only [mul_assoc]
private theorem swap_comm {F G : Type*} [Group G]
    (x : Fin 12 → F → G)
    (hc : ∀ i j, i ≠ j → (∀ k, (i,j,k) ∉ sumTriples) → ∀ a b, Commute (x i a) (x j b))
    (i j : Fin 12) (hij : i ≠ j) (h : ∀ k, (i,j,k) ∉ sumTriples) (a b : F) (g : G) :
    x i a * (x j b * g) = x j b * (x i a*g) := by
  rw [← mul_assoc, (hc i j hij h a b).eq, mul_assoc]
private theorem join {F G : Type*} [Add F] [Group G]
    (x : Fin 12 → F → G) (ha : ∀ i a b, x i (a+b) = x i a*x i b)
    (i : Fin 12) (a b : F) (g : G) :
    x i a * (x i b*g) = x i (a+b)*g := by rw [← mul_assoc, ← ha]

private theorem collect02 {F G : Type*} [Add F] [Mul F] [Group G]
    (x : Fin 12 → F → G) (ha : ∀ i a b, x i (a+b) = x i a*x i b)
    (hs : ∀ i j k, (i,j,k) ∈ sumTriples → ∀ a b,
      x i a*x j b = x j b*x i a*x k (a*b))
    (hc : ∀ i j, i ≠ j → (∀ k, (i,j,k) ∉ sumTriples) → ∀ a b, Commute (x i a) (x j b))
    (a b c d e f : F) :
    x 0 (a) * x 1 (b) * x 2 (c) * x 7 (d) * x 8 (e) * x 9 (f) * 1 =
    x 7 (d) * x 8 (e) * x 9 (f) * x 0 (a) * x 1 (b) * x 2 (c) * x 10 (((b) * (f)) + (((a) * (e)) + ((c) * (d)))) * 1 := by
  simp only [mul_assoc]
  conv_lhs =>
    rw [swap_sum x hs 2 7 10 (by decide) (c) (d)]
    rw [swap_comm x hc 1 7 (by decide) (by decide) (b) (d)]
    rw [swap_comm x hc 0 7 (by decide) (by decide) (a) (d)]
    rw [swap_comm x hc 10 8 (by decide) (by decide) ((c) * (d)) (e)]
    rw [swap_comm x hc 2 8 (by decide) (by decide) (c) (e)]
    rw [swap_comm x hc 1 8 (by decide) (by decide) (b) (e)]
    rw [swap_sum x hs 0 8 10 (by decide) (a) (e)]
    rw [swap_comm x hc 10 1 (by decide) (by decide) ((a) * (e)) (b)]
    rw [swap_comm x hc 10 2 (by decide) (by decide) ((a) * (e)) (c)]
    rw [join x ha 10 ((a) * (e)) ((c) * (d))]
    rw [swap_comm x hc 10 9 (by decide) (by decide) (((a) * (e)) + ((c) * (d))) (f)]
    rw [swap_comm x hc 2 9 (by decide) (by decide) (c) (f)]
    rw [swap_sum x hs 1 9 10 (by decide) (b) (f)]
    rw [swap_comm x hc 0 9 (by decide) (by decide) (a) (f)]
    rw [swap_comm x hc 10 2 (by decide) (by decide) ((b) * (f)) (c)]
    rw [join x ha 10 ((b) * (f)) (((a) * (e)) + ((c) * (d)))]

private theorem collect12 {F G : Type*} [Add F] [Mul F] [Group G]
    (x : Fin 12 → F → G) (ha : ∀ i a b, x i (a+b) = x i a*x i b)
    (hs : ∀ i j k, (i,j,k) ∈ sumTriples → ∀ a b,
      x i a*x j b = x j b*x i a*x k (a*b))
    (hc : ∀ i j, i ≠ j → (∀ k, (i,j,k) ∉ sumTriples) → ∀ a b, Commute (x i a) (x j b))
    (a b c d e f : F) :
    x 4 (a) * x 5 (b) * x 6 (c) * x 7 (d) * x 8 (e) * x 9 (f) * 1 =
    x 7 (d) * x 8 (e) * x 9 (f) * x 4 (a) * x 5 (b) * x 6 (c) * x 11 (((b) * (f)) + (((a) * (e)) + ((c) * (d)))) * 1 := by
  simp only [mul_assoc]
  conv_lhs =>
    rw [swap_sum x hs 6 7 11 (by decide) (c) (d)]
    rw [swap_comm x hc 5 7 (by decide) (by decide) (b) (d)]
    rw [swap_comm x hc 4 7 (by decide) (by decide) (a) (d)]
    rw [swap_comm x hc 11 8 (by decide) (by decide) ((c) * (d)) (e)]
    rw [swap_comm x hc 6 8 (by decide) (by decide) (c) (e)]
    rw [swap_comm x hc 5 8 (by decide) (by decide) (b) (e)]
    rw [swap_sum x hs 4 8 11 (by decide) (a) (e)]
    rw [swap_comm x hc 11 5 (by decide) (by decide) ((a) * (e)) (b)]
    rw [swap_comm x hc 11 6 (by decide) (by decide) ((a) * (e)) (c)]
    rw [join x ha 11 ((a) * (e)) ((c) * (d))]
    rw [swap_comm x hc 11 9 (by decide) (by decide) (((a) * (e)) + ((c) * (d))) (f)]
    rw [swap_comm x hc 6 9 (by decide) (by decide) (c) (f)]
    rw [swap_sum x hs 5 9 11 (by decide) (b) (f)]
    rw [swap_comm x hc 4 9 (by decide) (by decide) (a) (f)]
    rw [swap_comm x hc 11 6 (by decide) (by decide) ((b) * (f)) (c)]
    rw [join x ha 11 ((b) * (f)) (((a) * (e)) + ((c) * (d)))]

private theorem collect00 {F G : Type*} [Add F] [Mul F] [Group G]
    (x : Fin 12 → F → G) (ha : ∀ i a b, x i (a+b) = x i a*x i b)
    (hs : ∀ i j k, (i,j,k) ∈ sumTriples → ∀ a b,
      x i a*x j b = x j b*x i a*x k (a*b))
    (hc : ∀ i j, i ≠ j → (∀ k, (i,j,k) ∉ sumTriples) → ∀ a b, Commute (x i a) (x j b))
    (a b c d : F) :
    x 0 (a) * x 1 (b) * x 2 (c) * x 3 (d) * 1 =
    x 3 (d) * x 0 (a) * x 1 (b) * x 2 (c) * x 4 ((a) * (d)) * x 5 ((b) * (d)) * x 6 ((c) * (d)) * x 7 (((a) * (d)) * (b)) * x 8 (((b) * (d)) * (c)) * x 9 (((a) * (d)) * (c)) * x 10 ((((a) * (d)) * (b)) * (c)) * x 11 (((((a) * (d)) * (b)) * ((c) * (d))) + ((((a) * (d)) * (c)) * ((b) * (d)))) * 1 := by
  simp only [mul_assoc]
  conv_lhs =>
    rw [swap_sum x hs 2 3 6 (by decide) (c) (d)]
    rw [swap_sum x hs 1 3 5 (by decide) (b) (d)]
    rw [swap_sum x hs 0 3 4 (by decide) (a) (d)]
    rw [swap_sum x hs 4 1 7 (by decide) ((a) * (d)) (b)]
    rw [swap_comm x hc 7 5 (by decide) (by decide) (((a) * (d)) * (b)) ((b) * (d))]
    rw [swap_sum x hs 7 2 10 (by decide) (((a) * (d)) * (b)) (c)]
    rw [swap_sum x hs 5 2 8 (by decide) ((b) * (d)) (c)]
    rw [swap_sum x hs 4 2 9 (by decide) ((a) * (d)) (c)]
    rw [swap_sum x hs 9 5 11 (by decide) (((a) * (d)) * (c)) ((b) * (d))]
    rw [swap_comm x hc 11 8 (by decide) (by decide) ((((a) * (d)) * (c)) * ((b) * (d))) (((b) * (d)) * (c))]
    rw [swap_comm x hc 9 8 (by decide) (by decide) (((a) * (d)) * (c)) (((b) * (d)) * (c))]
    rw [swap_comm x hc 11 7 (by decide) (by decide) ((((a) * (d)) * (c)) * ((b) * (d))) (((a) * (d)) * (b))]
    rw [swap_comm x hc 9 7 (by decide) (by decide) (((a) * (d)) * (c)) (((a) * (d)) * (b))]
    rw [swap_comm x hc 8 7 (by decide) (by decide) (((b) * (d)) * (c)) (((a) * (d)) * (b))]
    rw [swap_comm x hc 11 10 (by decide) (by decide) ((((a) * (d)) * (c)) * ((b) * (d))) ((((a) * (d)) * (b)) * (c))]
    rw [swap_comm x hc 11 6 (by decide) (by decide) ((((a) * (d)) * (c)) * ((b) * (d))) ((c) * (d))]
    rw [swap_comm x hc 10 6 (by decide) (by decide) ((((a) * (d)) * (b)) * (c)) ((c) * (d))]
    rw [swap_comm x hc 9 6 (by decide) (by decide) (((a) * (d)) * (c)) ((c) * (d))]
    rw [swap_comm x hc 8 6 (by decide) (by decide) (((b) * (d)) * (c)) ((c) * (d))]
    rw [swap_sum x hs 7 6 11 (by decide) (((a) * (d)) * (b)) ((c) * (d))]
    rw [swap_comm x hc 11 8 (by decide) (by decide) ((((a) * (d)) * (b)) * ((c) * (d))) (((b) * (d)) * (c))]
    rw [swap_comm x hc 11 9 (by decide) (by decide) ((((a) * (d)) * (b)) * ((c) * (d))) (((a) * (d)) * (c))]
    rw [swap_comm x hc 11 10 (by decide) (by decide) ((((a) * (d)) * (b)) * ((c) * (d))) ((((a) * (d)) * (b)) * (c))]
    rw [join x ha 11 ((((a) * (d)) * (b)) * ((c) * (d))) ((((a) * (d)) * (c)) * ((b) * (d)))]
private theorem sums (P : Parameters) (hp : P.prime = 2)
    (i j k : Fin 12) (h : (i,j,k) ∈ sumTriples) (a b : ExtensionField P) :
    curve P i a * curve P j b = curve P j b * curve P i a * curve P k (a*b) := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  exact sumExchange_binary n hn i j k ((root_sum_iff i j k).mpr ((mem_sumTriples_iff i j k).mp h)) a b
private theorem nonsums (P : Parameters) (i j : Fin 12) (hij : i ≠ j)
    (h : ∀ k, (i,j,k) ∉ sumTriples) (a b : ExtensionField P) :
    Commute (curve P i a) (curve P j b) := by
  apply nonsumCommute_parameters P i j hij
  rintro ⟨k, hk⟩
  exact h k ((mem_sumTriples_iff i j k).mpr ((root_sum_iff i j k).mp hk))

private def ss (P : Parameters) {G : Type*} [Group G] (x : Fin 12 → ExtensionField P → G)
    (i : Fin 3) (s : ExtensionField P) : G :=
  x (shortPosition i 0) s * x (shortPosition i 1) (fieldFrobenius P s) *
    x (shortPosition i 2) (fieldFrobenius P (fieldFrobenius P s))
private def ll (P : Parameters) {G : Type*} [Group G] (x : Fin 12 → ExtensionField P → G)
    (i : Fin 3) (s : fixedField P) : G := x (longPosition i) s.val
private theorem folded_trace02 (P : Parameters) (hp : P.prime = 2) {G : Type*} [Group G]
    (x : Fin 12 → ExtensionField P → G)
    (ha : ∀ i a b, x i (a+b) = x i a*x i b)
    (hz : ∀ i, x i 0 = 1)
    (hs : ∀ i j k, (i,j,k) ∈ sumTriples → ∀ a b, x i a*x j b = x j b*x i a*x k (a*b))
    (hc : ∀ i j, i ≠ j → (∀ k, (i,j,k) ∉ sumTriples) → ∀ a b, Commute (x i a) (x j b)) (s t : ExtensionField P) :
    ss P x 0 s * ss P x 2 t = ss P x 2 t * ss P x 0 s *
      ll P x 1 (cubicTrace P (fieldFrobenius P (fieldFrobenius P s) * t)) := by
  have h := collect02 x ha hs hc
    s (fieldFrobenius P s) (fieldFrobenius P (fieldFrobenius P s))
    t (fieldFrobenius P t) (fieldFrobenius P (fieldFrobenius P t))
  have he : fieldFrobenius P s * fieldFrobenius P (fieldFrobenius P t) +
      (s * fieldFrobenius P t + fieldFrobenius P (fieldFrobenius P s) * t) =
      (cubicTrace P (fieldFrobenius P (fieldFrobenius P s) * t)).val := by
    simp only [cubicTrace_coe, map_mul, fieldFrobenius_three]; ring
  rw [he] at h
  simpa only [ss, ll, shortPosition, longPosition,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_one, mul_assoc] using h

private theorem folded_trace12 (P : Parameters) (hp : P.prime = 2) {G : Type*} [Group G]
    (x : Fin 12 → ExtensionField P → G)
    (ha : ∀ i a b, x i (a+b) = x i a*x i b)
    (hz : ∀ i, x i 0 = 1)
    (hs : ∀ i j k, (i,j,k) ∈ sumTriples → ∀ a b, x i a*x j b = x j b*x i a*x k (a*b))
    (hc : ∀ i j, i ≠ j → (∀ k, (i,j,k) ∉ sumTriples) → ∀ a b, Commute (x i a) (x j b)) (s t : ExtensionField P) :
    ss P x 1 s * ss P x 2 t = ss P x 2 t * ss P x 1 s *
      ll P x 2 (cubicTrace P (fieldFrobenius P (fieldFrobenius P s) * t)) := by
  have h := collect12 x ha hs hc
    s (fieldFrobenius P s) (fieldFrobenius P (fieldFrobenius P s))
    t (fieldFrobenius P t) (fieldFrobenius P (fieldFrobenius P t))
  have he : fieldFrobenius P s * fieldFrobenius P (fieldFrobenius P t) +
      (s * fieldFrobenius P t + fieldFrobenius P (fieldFrobenius P s) * t) =
      (cubicTrace P (fieldFrobenius P (fieldFrobenius P s) * t)).val := by
    simp only [cubicTrace_coe, map_mul, fieldFrobenius_three]; ring
  rw [he] at h
  simpa only [ss, ll, shortPosition, longPosition,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_one, mul_assoc] using h

private theorem folded_mixed (P : Parameters) (hp : P.prime = 2) {G : Type*} [Group G]
    (x : Fin 12 → ExtensionField P → G)
    (ha : ∀ i a b, x i (a+b) = x i a*x i b)
    (hz : ∀ i, x i 0 = 1)
    (hs : ∀ i j k, (i,j,k) ∈ sumTriples → ∀ a b, x i a*x j b = x j b*x i a*x k (a*b))
    (hc : ∀ i j, i ≠ j → (∀ k, (i,j,k) ∉ sumTriples) → ∀ a b, Commute (x i a) (x j b)) (s : ExtensionField P) (t : fixedField P) :
    ss P x 0 s * ll P x 0 t = ll P x 0 t * ss P x 0 s *
      ss P x 1 (s*t.val) * ss P x 2 (s*fieldFrobenius P s*t.val) *
        ll P x 1 (cubicNorm P s*t) := by
  let : CharP (ExtensionField P) 2 := hp ▸ inferInstanceAs (CharP (ExtensionField P) P.prime)
  have h := collect00 x ha hs hc
    s (fieldFrobenius P s) (fieldFrobenius P (fieldFrobenius P s)) t.val
  have hz : ((s*t.val)*fieldFrobenius P s)*(fieldFrobenius P (fieldFrobenius P s)*t.val) +
      ((s*t.val)*fieldFrobenius P (fieldFrobenius P s))*(fieldFrobenius P s*t.val) = 0 := by
    have he : ((s*t.val)*fieldFrobenius P (fieldFrobenius P s))*(fieldFrobenius P s*t.val) =
        ((s*t.val)*fieldFrobenius P s)*(fieldFrobenius P (fieldFrobenius P s)*t.val) := by ring
    rw [he, CharTwo.add_self_eq_zero]
  rw [hz, ‹∀ i, x i 0 = 1›] at h
  have ht : fieldFrobenius P t.val = t.val := t.property
  simpa only [ss, ll, shortPosition, longPosition, cubicNorm, Subfield.coe_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_one, mul_assoc,
    map_mul, ht, fieldFrobenius_three, mul_comm, mul_left_comm] using h

theorem base_trace02 (P : Parameters) (hp : P.prime = 2) (s t : ExtensionField P) :
    short P hp 0 s * short P hp 2 t = short P hp 2 t * short P hp 0 s *
      long P hp 1 (cubicTrace P (fieldFrobenius P (fieldFrobenius P s)*t)) := by
  simp only [short, long, ← map_mul]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, shortElementary_val, longElementary_val]
  exact folded_trace02 P hp (curve P) (curve_add P) (curve_zero P) (sums P hp) (nonsums P) s t
theorem base_trace12 (P : Parameters) (hp : P.prime = 2) (s t : ExtensionField P) :
    short P hp 1 s * short P hp 2 t = short P hp 2 t * short P hp 1 s *
      long P hp 2 (cubicTrace P (fieldFrobenius P (fieldFrobenius P s)*t)) := by
  simp only [short, long, ← map_mul]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, shortElementary_val, longElementary_val]
  exact folded_trace12 P hp (curve P) (curve_add P) (curve_zero P) (sums P hp) (nonsums P) s t
theorem base_mixed (P : Parameters) (hp : P.prime = 2) (s : ExtensionField P) (t : fixedField P) :
    short P hp 0 s * long P hp 0 t = long P hp 0 t * short P hp 0 s *
      short P hp 1 (s*t.val) * short P hp 2 (s*fieldFrobenius P s*t.val) *
        long P hp 1 (cubicNorm P s*t) := by
  simp only [short, long, ← map_mul]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, shortElementary_val, longElementary_val]
  exact folded_mixed P hp (curve P) (curve_add P) (curve_zero P) (sums P hp) (nonsums P) s t
end Triality.Standard.CentralCovers.TwoPrimary.RootSections.ShortPolynomial
