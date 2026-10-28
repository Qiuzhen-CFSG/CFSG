module

public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Self-normalizing Sylow subgroups in commuting products

Self-normalization of Sylow subgroups passes through surjective homomorphisms
and finite commuting products. For the product, each coordinate of a normalizer
element lies in the corresponding Sylow subgroup. A common prime-power
exponent then makes the entire normalizer a p-group, so Sylow maximality forces
equality. The multiplication map gives the same result for central products,
without requiring trivial intersections between the factors.

Source: the component-product Borel calculation in Aschbacher--Smith,
`refs/quasithin.pdf`, combined manuscript (1 March 2004), printed p.1144,
proof of 15.3.49(k). This module contains only the general finite-group step.
-/

public section

open Subgroup

namespace Sylow

/-- Coordinate normalizer control forces the product normalizer to be a p-group. -/
theorem self_normalizing_pi
    {ι : Type*} [Finite ι] (K : ι → Type*)
    [∀ i, Group (K i)] [∀ i, Finite (K i)]
    {p : ℕ} [Fact p.Prime]
    (hK : ∀ i, ∀ P : Sylow p (K i), normalizer (P : Set (K i)) = P)
    (P : Sylow p (∀ i, K i)) : normalizer (P : Set (∀ i, K i)) = P := by
  classical
  let _ := Fintype.ofFinite ι
  let Q (i : ι) : Sylow p (K i) :=
    P.mapSurjective (f := Pi.evalMonoidHom K i) (Function.surjective_eval i)
  have hx (x : normalizer (P : Set (∀ i, K i))) (i : ι) : x.val i ∈ Q i := by
    change x.val i ∈ (Q i : Subgroup (K i))
    rw [← hK i (Q i)]
    exact (P : Subgroup (∀ i, K i)).le_normalizer_map (Pi.evalMonoidHom K i)
      (mem_map_of_mem _ x.property)
  have hp : IsPGroup p (normalizer (P : Set (∀ i, K i))) := by
    intro x
    choose k hk using fun i => (Q i).isPGroup' ⟨x.val i, hx x i⟩
    refine ⟨∑ i, k i, Subtype.ext (funext fun i => ?_)⟩
    have hi : k i ≤ ∑ j, k j :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (k j)) (Finset.mem_univ i)
    have he : x.val i ^ (p ^ k i) = 1 := congrArg Subtype.val (hk i)
    change x.val i ^ (p ^ ∑ j, k j) = 1
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_of_pow_eq_one he).trans
      (pow_dvd_pow p hi))
  exact P.is_maximal' hp P.le_normalizer

/-- Self-normalization of all Sylow subgroups passes to any homomorphic image. -/
theorem self_normalizing_of_surjective
    {G H : Type*} [Group G] [Group H] [Finite G]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hG : ∀ P : Sylow p G, normalizer (P : Set G) = P)
    (Q : Sylow p H) : normalizer (Q : Set H) = Q := by
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hf p Q
  change normalizer (P.map f : Set H) = P.map f
  rw [← P.normalizer_map_surjective f hf, hG P]

/-- Self-normalization passes to a commuting join, including central products. -/
theorem self_normalizing_of_commuting_family
    {G : Type*} [Group G] [Finite G] {ι : Type*} [Fintype ι]
    (C : ι → Subgroup G)
    (hcomm : Pairwise fun i j => C i ≤ centralizer (C j : Set G))
    (hgen : iSup C = ⊤) {p : ℕ} [Fact p.Prime]
    (hC : ∀ i, ∀ P : Sylow p (C i), normalizer (P : Set (C i)) = P)
    (P : Sylow p G) : normalizer (P : Set G) = P := by
  have hc : Pairwise fun i j => ∀ x y : G, x ∈ C i → y ∈ C j → Commute x y := by
    intro i j hij x y hx hy
    exact (hcomm hij hx y hy).symm
  let f : (∀ i, C i) →* G := noncommPiCoprod hc
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp
    (noncommPiCoprod_range.trans hgen)
  exact self_normalizing_of_surjective f hf (self_normalizing_pi (fun i => C i) hC) P

end Sylow
