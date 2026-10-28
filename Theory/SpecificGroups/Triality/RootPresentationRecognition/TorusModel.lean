module
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.PositiveTorusModel
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.TorusCharacterAlgebra

/-!
# All native torus equations for the finite triality presentation

The checked D₄ Cartan reflection formula acts on the four original coroot
coordinates. Folding gives the two prescribed Weyl actions on the actual cubic
and fixed-field units. The longest Weyl word inverts all four coordinates;
conjugating the positive torus equations by opposition then proves the negative
ones. Together with the existing signed Weyl and positive exchange proofs this
verifies every relation on the genuine graph-field carrier, including q=2,4.

The finite coordinate calculations take place in an abstract commutative group
before transport through the faithful carrier-to-split map. The original
central quotient and fixed-field inclusion remain unchanged.
Source: GLS3 2.4.7–8, with the literal orbit origins of `FoldedRoots`.
-/

@[expose] public noncomputable section
namespace Triality.Standard.RootPresentationRecognition.TorusModel
open Parabolics ConcreteBruhat TorusCoordinates
open Theory.AlgebraicGroup.StandardRootSystem

private theorem conj_mul {G : Type*} [Group G] (g x y : G) :
    g*(x*y)*g⁻¹ = (g*x*g⁻¹)*(g*y*g⁻¹) := by group
private theorem mul_conj {G : Type*} [Group G] (g h x : G) :
    (g*h)*x*(g*h)⁻¹ = g*(h*x*h⁻¹)*g⁻¹ := by group

private def reflect {A : Type*} [CommGroup A] (i : Fin 4) (a : Fin 4 → A) : Fin 4 → A :=
  ![![a 1 / a 0, a 1, a 2, a 3],
    ![a 0, a 0 * a 2 * a 3 / a 1, a 2, a 3],
    ![a 0, a 1, a 1 / a 2, a 3],
    ![a 0, a 1, a 2, a 1 / a 3]] i

private theorem reflect_formula {A : Type*} [CommGroup A] (i : Fin 4) (a : Fin 4 → A) :
    (Function.update (1 : Fin 4 → A) 0 (a 0) * Function.update (1 : Fin 4 → A) i (a 0 ^ (-typeDCartanMatrix 2 0 i))) *
    (Function.update (1 : Fin 4 → A) 2 (a 2) * Function.update (1 : Fin 4 → A) i (a 2 ^ (-typeDCartanMatrix 2 2 i))) *
    (Function.update (1 : Fin 4 → A) 3 (a 3) * Function.update (1 : Fin 4 → A) i (a 3 ^ (-typeDCartanMatrix 2 3 i))) *
    (Function.update (1 : Fin 4 → A) 1 (a 1) * Function.update (1 : Fin 4 → A) i (a 1 ^ (-typeDCartanMatrix 2 1 i))) = reflect i a := by
  funext k
  fin_cases i <;> fin_cases k <;>
    simp [reflect, typeDCartanMatrix, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] <;> group

private theorem simple_product (P : Parameters) (hp : P.prime = 2)
    (i : Fin 4) (a : Coordinates P) :
    weylWord P i 1 * product P a * (weylWord P i 1)⁻¹ = product P (reflect i a) := by
  conv_lhs => rw [product]
  simp only [conj_mul]
  simp only [RootConjugation.weylWord_torusWord_conjugation P hp]
  simp only [← product_single P hp, ← product_mul P hp]
  exact congrArg (product P) (reflect_formula i a)

private theorem torus_split {n : ℕ} {hn : 0 < n} (p : TorusParameters n hn) :
    FixedDescent.carrierToSplit (binaryParameters n hn) rfl ((SignedModel.roots n hn).torus p) =
      product (binaryParameters n hn) (expand (binaryParameters n hn) p) := by
  rw [SignedModel.torus_eq n hn, torusMulEquiv_val (binaryParameters n hn) rfl,
    FixedDescent.carrierToSplit_toCarrier (binaryParameters n hn) rfl,
    inclusion_orbitElementary (binaryParameters n hn) rfl]

variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

theorem arms (p : TorusParameters n hn) :
    (SignedModel.roots n hn).nA 1 * (SignedModel.roots n hn).torus p *
      ((SignedModel.roots n hn).nA 1)⁻¹ =
        (SignedModel.roots n hn).torus (fixedUnit P p.2 / p.1, p.2) := by
  apply FixedDescent.carrierToSplit_injective P rfl
  simp only [map_mul, map_inv, torus_split, SignedModel.nA_one, simpleRepresentative,
    FixedDescent.carrierToSplit_toCarrier P rfl, elementaryInclusion_simple_arms P rfl,
    mul_conj, simple_product P rfl]
  apply congrArg (product P)
  funext i
  fin_cases i <;> simp [reflect, expand, map_div]

theorem central (p : TorusParameters n hn) :
    (SignedModel.roots n hn).nB 1 * (SignedModel.roots n hn).torus p *
      ((SignedModel.roots n hn).nB 1)⁻¹ =
        (SignedModel.roots n hn).torus (p.1, normUnit p.1 / p.2) := by
  apply FixedDescent.carrierToSplit_injective P rfl
  simp only [map_mul, map_inv, torus_split, SignedModel.nB_one, simpleRepresentative,
    FixedDescent.carrierToSplit_toCarrier P rfl, elementaryInclusion_simple_central P rfl,
    simple_product P rfl]
  apply congrArg (product P)
  funext i
  fin_cases i <;> simp [reflect, expand, normUnit]

private theorem longest_reflect {A : Type*} [CommGroup A] (a : Fin 4 → A) :
    reflect 0 (reflect 2 (reflect 3 (reflect 1
      (reflect 0 (reflect 2 (reflect 3 (reflect 1
        (reflect 0 (reflect 2 (reflect 3 (reflect 1 a))))))))))) = a⁻¹ := by
  funext i
  fin_cases i <;> simp [reflect] <;>
    apply Additive.ofMul.injective <;>
    simp only [ofMul_mul, ofMul_div, ofMul_inv] <;> abel

/-- The longest native Weyl representative inverts the full original torus. -/
theorem opposition_torus (p : TorusParameters n hn) :
    SignedModel.opposition P rfl ((SignedModel.roots n hn).torus p) =
      (SignedModel.roots n hn).torus p⁻¹ := by
  have he : SignedModel.longest P rfl =
      (simpleRepresentative P rfl .arms * simpleRepresentative P rfl .central)^3 := by
    simp only [SignedModel.longest, simpleRepresentative]
    rfl
  simp only [SignedModel.opposition, MulAut.conj_apply]
  rw [he]
  apply FixedDescent.carrierToSplit_injective P rfl
  simp only [map_mul, map_inv, map_pow, torus_split, simpleRepresentative,
    FixedDescent.carrierToSplit_toCarrier P rfl,
    elementaryInclusion_simple_arms P rfl, elementaryInclusion_simple_central P rfl]
  simp only [pow_succ, pow_zero, one_mul, mul_conj, simple_product P rfl, longest_reflect]
  exact congrArg (product P) (by
    funext i
    fin_cases i <;> simp [expand])

/-- All signed short-root characters, including the three opposite orbits. -/
theorem short_signed (p : TorusParameters n hn) (s : Bool) (i : Fin 3) (t : ExtensionField P) :
    (SignedModel.roots n hn).torus p * (SignedModel.roots n hn).shortSigned s i t *
      ((SignedModel.roots n hn).torus p)⁻¹ =
    (SignedModel.roots n hn).shortSigned s i
      ((if s then (shortCharacter p i).val else ((shortCharacter p i)⁻¹).val)*t) := by
  cases s
  · have h := congrArg (SignedModel.opposition P rfl)
      (PositiveTorusModel.short_positive n hn i p⁻¹ t)
    simpa only [map_mul, map_inv, opposition_torus n hn, inv_inv,
      shortCharacter_inv, SignedRoots.shortSigned, Bool.false_eq_true, if_false,
      SignedModel.negative_short] using h
  · exact PositiveTorusModel.short_positive n hn i p t

/-- All signed long-root characters, with fixed-field parameters unchanged. -/
theorem long_signed (p : TorusParameters n hn) (s : Bool) (i : Fin 3) (t : fixedField P) :
    (SignedModel.roots n hn).torus p * (SignedModel.roots n hn).longSigned s i t *
      ((SignedModel.roots n hn).torus p)⁻¹ =
    (SignedModel.roots n hn).longSigned s i
      ((if s then (longCharacter p i).val else ((longCharacter p i)⁻¹).val)*t) := by
  cases s
  · have h := congrArg (SignedModel.opposition P rfl)
      (PositiveTorusModel.long_positive n hn i p⁻¹ t)
    simpa only [map_mul, map_inv, opposition_torus n hn, inv_inv,
      longCharacter_inv, SignedRoots.longSigned, Bool.false_eq_true, if_false,
      SignedModel.negative_long] using h
  · exact PositiveTorusModel.long_positive n hn i p t

/-- Every explicit relation holds on the genuine native carrier, also at q=2,4. -/
theorem relations : (SignedModel.roots n hn).Relations :=
  { SignedModel.weylRelations n hn, SignedModel.actionRelations n hn with
    mul := SignedModel.torus_mul n hn
    short := short_signed n hn
    long := long_signed n hn
    arms := arms n hn
    central := central n hn }

end Triality.Standard.RootPresentationRecognition.TorusModel
