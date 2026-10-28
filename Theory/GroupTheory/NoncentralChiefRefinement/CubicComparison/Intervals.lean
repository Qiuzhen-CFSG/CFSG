module
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Count
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.FixedIndex
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Bounds

/-!
# Cubic chief counts on literal subgroup intersections

Above a normal two-kernel, a normal cubic with two-group quotient detects
all noncentral binary chief factors. Concatenating a chief series below
an arbitrary interval with the interval itself extends the bottom-series
formula to every normal two-interval. Injective transport and coprime
fixed-point lifting then identify the chief count on intersections with
an overgroup that is normalized by the original two-groups.

All subgroup inclusions and conjugation actions are retained. Normality is
relative to the specified overgroup, never to a larger ambient simple group.
Source application: Aschbacher–Smith, 13.8.31(3), printed p.965.
-/

public section
open Subgroup
namespace NoncentralChiefRefinement.CubicComparison
variable {H K : Type*} [Group H] [Finite H] [Group K] [Finite K]

/-- The fixed-index formula on an arbitrary normal two-chief interval. -/
theorem interval_count_eq_length
    (f : H →* K) (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (X : Subgroup K) [X.Normal] (hX : Nat.card X = 3)
    (hq : IsPGroup 2 (K ⧸ X)) (A : Subgroup H) (hA : IsPGroup 3 A)
    (hAX : A.map f = X) (s : ChiefSeries H) (hs : IsPGroup 2 s.last.val) :
    s.noncentralTwoCount = sectionCubicLength A s.head.val s.last.val := by
  obtain ⟨b⟩ := SeriesOn.exists_series s.head.val
  have hb : b.series.last = s.head := b.last_eq
  let t : SeriesOn s.last.val := {
    series := b.series.smash s hb
    head_eq := (RelSeries.head_smash hb).trans b.head_eq
    last_eq := RelSeries.last_smash hb }
  have hlo := series_count_eq_length (f := f) (X := X) (A := A) s.head.val
    (hs.to_le (show s.head.val ≤ s.last.val from CompositionSeries.head_le (s := s) (Fin.last s.length))) hf hp hX hq hA hAX b
  have hhi := series_count_eq_length (f := f) (X := X) (A := A) s.last.val
    hs hf hp hX hq hA hAX t
  have ht : t.series.noncentralTwoCount = b.series.noncentralTwoCount + s.noncentralTwoCount :=
    ChiefSeries.noncentralTwoCount_smash b.series s hb
  unfold sectionCubicLength
  omega

/-- Passing to the literal intersections retains the original cubic length
when the two-groups normalize the overgroup. -/
theorem intersection_section_length
    {G : Type*} [Group G] [Finite G]
    (D A N R : Subgroup G) (hAD : A ≤ D) (hA : IsPGroup 3 A)
    (hN : IsPGroup 2 N) (hR : IsPGroup 2 R)
    (hND : N ≤ normalizer (D : Set G)) (hRD : R ≤ normalizer (D : Set G))
    (hDN : D ≤ normalizer (N : Set G)) (hDR : D ≤ normalizer (R : Set G)) :
    sectionCubicLength (A.subgroupOf D) (N.subgroupOf D) (R.subgroupOf D) =
      sectionCubicLength A N R := by
  have hm (S : Subgroup G) :
      conjugationCubicLength (A.subgroupOf D) (S.subgroupOf D) =
        conjugationCubicLength A (S ⊓ D) := by
    have he := length_map_injective D.subtype D.subtype_injective
      (A.subgroupOf D) (S.subgroupOf D)
    rw [map_subgroupOf_eq_of_le hAD] at he
    rw [subgroupOf_map_subtype] at he
    exact he.symm
  unfold sectionCubicLength
  rw [hm R, hm N,
    intersection_length_eq A R D hA hR hAD hRD hDR,
    intersection_length_eq A N D hA hN hAD hND hDN]

/-- Count actual chief sections on the intersection, without selecting any
homogeneous quotient coordinates or assuming the chief count. -/
theorem intersection_interval_count
    {G : Type*} [Group G] [Finite G]
    (D A N R : Subgroup G) (hAD : A ≤ D) (hA : IsPGroup 3 A)
    (hN : IsPGroup 2 N) (hR : IsPGroup 2 R)
    (hND : N ≤ normalizer (D : Set G)) (hRD : R ≤ normalizer (D : Set G))
    (hDN : D ≤ normalizer (N : Set G)) (hDR : D ≤ normalizer (R : Set G))
    (f : D →* K) (hf : Function.Surjective f) (hp : IsPGroup 2 f.ker)
    (X : Subgroup K) [X.Normal] (hX : Nat.card X = 3)
    (hq : IsPGroup 2 (K ⧸ X)) (hAX : (A.subgroupOf D).map f = X)
    (s : ChiefSeries D) (hs0 : s.head.val = N.subgroupOf D)
    (hs1 : s.last.val = R.subgroupOf D) :
    s.noncentralTwoCount = sectionCubicLength A N R := by
  have hs : IsPGroup 2 s.last.val := by
    rw [hs1]
    let i : R.subgroupOf D →* R := {
      toFun x := ⟨x.val.val,x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    exact hR.of_injective i (fun x y h => Subtype.ext (Subtype.ext (show x.val.val = y.val.val from congrArg (fun r : R => r.val) h)))
  have hAD3 : IsPGroup 3 (A.subgroupOf D) :=
    hA.of_equiv (subgroupOfEquivOfLe hAD).symm
  rw [interval_count_eq_length f hf hp X hX hq (A.subgroupOf D) hAD3 hAX s hs,
    hs0, hs1]
  exact intersection_section_length D A N R hAD hA hN hR hND hRD hDN hDR

end NoncentralChiefRefinement.CubicComparison
