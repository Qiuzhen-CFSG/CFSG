module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.FixedNormalizer.Action
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.FixedCollection.SeedGeneration.SuzukiLeviGeneration.FixedNormalizer.Weyl

/-!
# Collection of arbitrary middle-node normalizer words

Write each nonzero rank-one generator as its coroot factor times the
parameter-one lift. The two simple reflections preserve the middle coroot
torus, and their eight-element multiplication table collects the remaining
Weyl word. Left closure induction now gives a two-coroot factor followed by
one of the eight representatives for every element of the actual normalizer.
All rank-one words are involutions in characteristic two, so the same step
handles inverse generators. No Bruhat coverage assumption is used.

Source: GLS3, 2.3.4–8 and 2.4.8, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.SuzukiNormalizer
open Parabolics Binary.FixedGeometry LargeLocalSeeds
open PairNormalization.OppositionCell.FixedBruhatCover
noncomputable section
variable {m : ℕ}

private theorem weyl_square (i : Fin 4) :
    weylWord m (typeF4SimpleRootIndex i) 1 * weylWord m (typeF4SimpleRootIndex i) 1 = 1 := by
  simpa only [weyl_inv] using inv_mul_cancel (weylWord m (typeF4SimpleRootIndex i) 1)

private theorem coroot_one (i : Fin 4) :
    torusWord m (typeF4SimpleRootIndex i) 1 = 1 := by
  simpa only [torusWord, Units.val_one, CharTwo.neg_eq] using weyl_square (m := m) i

private theorem weyl_factor (i : Fin 4) (t : (CoefficientField m)ˣ) :
    weylWord m (typeF4SimpleRootIndex i) t =
      torusWord m (typeF4SimpleRootIndex i) t * simpleWord m [i] := by
  simp only [torusWord, simpleWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, CharTwo.neg_eq]
  rw [mul_assoc, weyl_square, mul_one]

private theorem left_generator (i : Fin 4) (hi : i ∈ leviNodes .suzuki)
    (t a b : (CoefficientField m)ˣ) (k : Fin 8) :
    ∃ c e : (CoefficientField m)ˣ, ∃ j : Fin 8,
      weylWord m (typeF4SimpleRootIndex i) t * (torus a b * representative m k) =
        torus c e * representative m j := by
  change i = 1 ∨ i = 2 at hi
  rcases hi with rfl | rfl
  · refine ⟨t * (a⁻¹ * b^2), b, leftOne k, ?_⟩
    have ht : torusWord m (typeF4SimpleRootIndex 1) t = torus t 1 := by
      simp only [torus, coroot_one, mul_one]
    rw [weyl_factor, ht]
    calc
      _ = torus t 1 * ((simpleWord m [1] * torus a b) * representative m k) := by group
      _ = torus t 1 * ((torus (a⁻¹ * b^2) b * simpleWord m [1]) * representative m k) := by
        rw [simple_one_torus]
      _ = (torus t 1 * torus (a⁻¹ * b^2) b) *
          (simpleWord m [1] * representative m k) := by group
      _ = _ := by rw [torus_mul, left_one, one_mul]
  · refine ⟨a, t * (b⁻¹ * a), leftTwo k, ?_⟩
    have ht : torusWord m (typeF4SimpleRootIndex 2) t = torus 1 t := by
      simp only [torus, coroot_one, one_mul]
    rw [weyl_factor, ht]
    calc
      _ = torus 1 t * ((simpleWord m [2] * torus a b) * representative m k) := by group
      _ = torus 1 t * ((torus a (b⁻¹ * a) * simpleWord m [2]) * representative m k) := by
        rw [simple_two_torus]
      _ = (torus 1 t * torus a (b⁻¹ * a)) *
          (simpleWord m [2] * representative m k) := by group
      _ = _ := by rw [torus_mul, left_two, one_mul]

theorem splitForm (m : ℕ) : SplitForm m := by
  intro n hn
  induction hn using Subgroup.closure_induction_left with
  | one =>
    refine ⟨1, 1, 0, ?_⟩
    simp only [torus_one, one_mul]
    rfl
  | mul_left x hx y hy ih =>
    obtain ⟨i, hi, t, rfl⟩ := hx
    obtain ⟨a, b, k, rfl⟩ := ih
    simpa only [rankOneRepresentative, weylWord, Units.val_inv_eq_inv_val] using
      left_generator i hi t a b k
  | inv_mul_cancel x hx y hy ih =>
    obtain ⟨i, hi, t, rfl⟩ := hx
    obtain ⟨a, b, k, rfl⟩ := ih
    have he : (rankOneRepresentative m (typeF4SimpleRootIndex i) t)⁻¹ =
        rankOneRepresentative m (typeF4SimpleRootIndex i) t := by
      simpa only [rankOneRepresentative, weylWord, Units.val_inv_eq_inv_val] using
        weyl_inv (typeF4SimpleRootIndex i) (t : CoefficientField m)
    rw [he]
    simpa only [rankOneRepresentative, weylWord, Units.val_inv_eq_inv_val] using
      left_generator i hi t a b k

end
end ReeF4.LocalBlockInput.PairRigidity.FixedCollection.SeedGeneration.SuzukiNormalizer
