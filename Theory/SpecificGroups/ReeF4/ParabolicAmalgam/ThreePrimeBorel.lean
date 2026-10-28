module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.Geometry.DiagonalTorus
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.PositiveTwoGroup
public import Theory.GroupTheory.SubgroupProductCard

/-!
# The Ree Borel has order prime to three

The coefficient field has order `q = 2^(2*m+1)`, so `q - 1` is prime to
three. This proves the same for the four-parameter diagonal torus and every
subgroup of its matrix image. Once the coroot words are known to be diagonal,
they normalize the positive two-group. The subgroup product formula then
makes the split Borel, and its actual Ree fixed subgroup, prime to three.

Only the coroot-to-diagonal containment remains a premise. No full Ree order,
simplicity, automorphism coverage, or fixed-point factorization is assumed.
This applies also at `m = 0` to the full fixed group, without identifying it
with the Tits simple group.

Source: the Borel step in Aschbacher–Smith, Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`), with the root-defined torus of F.1.12.
-/

public section

open Subgroup
open scoped Pointwise
namespace ReeF4.Parabolics.ThreePrimeBorel
open LargeLocalSeeds

/-- The odd binary field degree excludes three from the diagonal parameters. -/
theorem torusParameter_coprime_three (m : ℕ) :
    Nat.Coprime 3 (Nat.card (TorusParameter m)) := by
  change Nat.Coprime 3 (Nat.card
    (Theory.AlgebraicGroup.StandardRootSystem.typeF4RootPairing_base.support →
      (CoefficientField m)ˣ))
  rw [Nat.card_fun, Nat.card_units, field_card]
  apply Nat.Coprime.pow_right
  apply Nat.prime_three.coprime_iff_not_dvd.mpr
  have hfour : 4 ^ m % 3 = 1 := by
    change Nat.ModEq 3 (4 ^ m) 1
    simpa only [one_pow] using
      (show Nat.ModEq 3 4 1 by norm_num [Nat.ModEq]).pow m
  have hq : 2 ^ (2 * m + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul]
    norm_num only [Nat.reducePow] at *
    rw [Nat.mul_mod, hfour]
  have hsub : (2 ^ (2 * m + 1) - 1) % 3 = 1 := by
    generalize 2 ^ (2 * m + 1) = q at hq ⊢
    omega
  intro hd
  have hz := Nat.dvd_iff_mod_eq_zero.mp hd
  omega

/-- The diagonal matrix torus inherits the parameter group's three-free order. -/
theorem diagonalTorus_coprime_three (m : ℕ) :
    Nat.Coprime 3 (Nat.card (diagonalTorus m)) := by
  have hr : Nat.Coprime 3 (Nat.card (diagonalTorusHom m).range) :=
    (torusParameter_coprime_three m).of_dvd_right (card_range_dvd (diagonalTorusHom m))
  let f : diagonalTorus m →* (diagonalTorusHom m).range :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  apply hr.of_dvd_right (card_dvd_of_injective f ?_)
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : (diagonalTorusHom m).range => (z : MatrixUnits m)) h

/-- Normalization and the product formula exclude three from the split Borel. -/
theorem splitBorel_coprime_three_of_torus (m : ℕ)
    (hT : splitTorus m ≤ diagonalTorus m) :
    Nat.Coprime 3 (Nat.card (splitBorel m)) := by
  have hn := splitTorus_le_unipotent_normalizer_of_le_diagonalTorus m hT
  have hc := card_set_mul_mul_card_inf (splitUnipotent m) (splitTorus m)
  rw [← coe_mul_of_right_le_normalizer_left _ _ hn] at hc
  have hU : Nat.Coprime 3 (Nat.card (splitUnipotent m)) := by
    obtain ⟨n, hn⟩ := (splitUnipotent_isPGroup m).exists_card_eq
    rw [hn]
    exact Nat.Coprime.pow_right n (by decide)
  have hD := (diagonalTorus_coprime_three m).of_dvd_right (card_dvd_of_le hT)
  exact (hU.mul_right hD).of_dvd_right ⟨_, hc.symm⟩

/-- The genuine fixed-point Borel embeds in the split Borel. -/
theorem borel_coprime_three_of_torus (m : ℕ)
    (hT : splitTorus m ≤ diagonalTorus m) : Nat.Coprime 3 (Nat.card (borel m)) := by
  let f : borel m →* splitBorel m :=
    { toFun := fun x => ⟨toSplitGroup m x.val, x.property⟩
      map_one' := Subtype.ext (map_one (toSplitGroup m))
      map_mul' := fun x y => Subtype.ext (map_mul (toSplitGroup m) x.val y.val) }
  apply (splitBorel_coprime_three_of_torus m hT).of_dvd_right
    (card_dvd_of_injective f ?_)
  intro x y h
  apply Subtype.ext
  apply toSplitGroup_injective m
  exact congrArg (fun z : splitBorel m => (z : SplitGroup m)) h

end ReeF4.Parabolics.ThreePrimeBorel
