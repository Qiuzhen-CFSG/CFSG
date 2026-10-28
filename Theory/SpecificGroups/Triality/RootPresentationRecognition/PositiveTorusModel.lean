module
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.TorusWords

/-!
# Native torus characters on all positive folded roots

The twelve split root weights are checked against the actual D₄ root pairing.
Field-free commutative-group calculations identify the three members of each
short orbit with the successive Frobenius images of its character. The long
characters use units of the actual fixed subfield and the literal cubic norm.
Transport through the injective carrier-to-split map proves the six positive
root conjugation equations for the defined native torus words.

All positive binary exponents are covered, including q=2 and q=4. The negative
root and Weyl-on-torus equations remain separate verification duties.
Source: GLS3 2.4.7(f), retaining the original `FoldedRoots` orbit origins.
-/

@[expose] public noncomputable section
namespace Triality.Standard.RootPresentationRecognition.PositiveTorusModel
open Parabolics Parabolics.RankOneMatrices ConcreteBruhat TorusCoordinates
open PositiveCoordinates PositiveCoordinates.SumExchangeData RadicalCoordinates.LeviCommutators
open Theory.AlgebraicGroup.StandardRootSystem

private def weights : Fin 12 → Fin 4 → ℤ :=
  ![![2,0,0,-1], ![0,2,0,-1], ![0,0,2,-1], ![-1,-1,-1,2],
    ![1,-1,-1,1], ![-1,1,-1,1], ![-1,-1,1,1],
    ![1,1,-1,0], ![-1,1,1,0], ![1,-1,1,0], ![1,1,1,-1], ![0,0,0,1]]

private theorem pairing (i : Fin 12) (j : Fin 4) :
    (typeDRootPairing 2).pairingIn ℤ (rootIndex i)
      (typeDSimpleRootIndex 2 (![0,2,3,1] j)) = weights i j := by
  have hd : (∑ k : Fin 4, rootCoords (simpleIndex (![0,2,3,1] j)) k *
      rootCoords (positiveIndex i) k) = weights i j := by
    revert i j
    decide +kernel
  apply Int.cast_injective (α := ℝ)
  change (algebraMap ℤ ℝ) _ = (weights i j : ℝ)
  rw [RootPairing.algebraMap_pairingIn, typeDRootPairing_pairing,
    ← rootEnumeration_positiveIndex, ← rootEnumeration_simpleIndex]
  change (∑ k : Fin 4, _ * _) = _
  simp only [← typeDRootPairing_root_val, rootCoords_spec]
  simpa only [Int.cast_sum, Int.cast_mul] using congrArg (fun z : ℤ => (z : ℝ)) hd

private theorem coordinate_character (P : Parameters) (i : Fin 12) (p : TorusCoordinates.OrbitParameters P) :
    InputRealization.coordinateCharacter P (rootIndex i) (expand P p) =
      p.1 ^ (weights i 0) * frobenius P p.1 ^ (weights i 1) *
        frobenius P (frobenius P p.1) ^ (weights i 2) * fixedUnit P p.2 ^ (weights i 3) := by
  have h0 : (typeDRootPairing 2).pairingIn ℤ (rootIndex i)
      (typeDSimpleRootIndex 2 0) = weights i 0 := pairing i 0
  have h2 : (typeDRootPairing 2).pairingIn ℤ (rootIndex i)
      (typeDSimpleRootIndex 2 2) = weights i 1 := pairing i 1
  have h3 : (typeDRootPairing 2).pairingIn ℤ (rootIndex i)
      (typeDSimpleRootIndex 2 3) = weights i 2 := pairing i 2
  have h1 : (typeDRootPairing 2).pairingIn ℤ (rootIndex i)
      (typeDSimpleRootIndex 2 1) = weights i 3 := pairing i 3
  change (expand P p 0) ^ (_ : ℤ) * (expand P p 2) ^ (_ : ℤ) * (expand P p 3) ^ (_ : ℤ) * (expand P p 1) ^ (_ : ℤ) = _
  rw [h0, h2, h3, h1]
  rfl

private def shortWeight {A : Type*} [CommGroup A] (f : A →* A) (t u : A) : Fin 3 → A :=
  ![t^2/u, t*u/(f t*f (f t)), t*f t/f (f t)]

private theorem short_weights {A : Type*} [CommGroup A] (f : A →* A) (t u : A)
    (hf : ∀ x, f (f (f x)) = x) (hu : f u = u) (i j : Fin 3) :
    t ^ (weights (shortPosition i j) 0) * f t ^ (weights (shortPosition i j) 1) *
      f (f t) ^ (weights (shortPosition i j) 2) * u ^ (weights (shortPosition i j) 3) =
        f^[j.val] (shortWeight f t u i) := by
  fin_cases i <;> fin_cases j <;>
    simp [weights, shortPosition, shortWeight, Function.iterate_succ_apply,
      hf, hu, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

private def longWeight {A : Type*} [CommGroup A] (f : A →* A) (t u : A) : Fin 3 → A :=
  ![u^2/(t*f t*f (f t)), (t*f t*f (f t))/u, u]

private theorem long_weights {A : Type*} [CommGroup A] (f : A →* A) (t u : A) (i : Fin 3) :
    t ^ (weights (longPosition i) 0) * f t ^ (weights (longPosition i) 1) *
      f (f t) ^ (weights (longPosition i) 2) * u ^ (weights (longPosition i) 3) =
        longWeight f t u i := by
  fin_cases i <;> simp [weights, longPosition, longWeight, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc]

variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

/-- Every split member of a short orbit has the corresponding Frobenius character. -/
theorem short_character (i j : Fin 3) (p : TorusParameters n hn) :
    InputRealization.coordinateCharacter P (rootIndex (shortPosition i j)) (expand P p) =
      (TorusCoordinates.frobenius P)^[j.val] (shortCharacter p i) :=
  (coordinate_character P (shortPosition i j) p).trans
    (short_weights (TorusCoordinates.frobenius P) p.1 (fixedUnit P p.2)
      (frobenius_three P) (frobenius_fixedUnit P p.2) i j)

/-- Long-root characters stay in the actual fixed field. -/
theorem long_character (i : Fin 3) (p : TorusParameters n hn) :
    InputRealization.coordinateCharacter P (rootIndex (longPosition i)) (expand P p) =
      fixedUnit P (longCharacter p i) := by
  have he := (coordinate_character P (longPosition i) p).trans
    (long_weights (TorusCoordinates.frobenius P) p.1 (fixedUnit P p.2) i)
  refine he.trans ?_
  have hnorm : fixedUnit P (normUnit p.1) =
      p.1 * TorusCoordinates.frobenius P p.1 * TorusCoordinates.frobenius P (TorusCoordinates.frobenius P p.1) :=
    fixedUnit_restrictUnit P _ _
  fin_cases i <;> simp [longWeight, longCharacter, hnorm]

private theorem conjugate_mul {G : Type*} [Group G] (g x y : G) :
    g*(x*y)*g⁻¹ = (g*x*g⁻¹)*(g*y*g⁻¹) := by group

private theorem torus_split (p : TorusParameters n hn) :
    FixedDescent.carrierToSplit P rfl ((SignedModel.roots n hn).torus p) = product P (expand P p) := by
  rw [SignedModel.torus_eq n hn, torusMulEquiv_val P rfl,
    FixedDescent.carrierToSplit_toCarrier P rfl, inclusion_orbitElementary P rfl]

/-- The torus acts on each native short positive root by its literal character. -/
theorem short_positive (i : Fin 3) (p : TorusParameters n hn) (t : ExtensionField P) :
    (SignedModel.roots n hn).torus p * short P rfl i t * ((SignedModel.roots n hn).torus p)⁻¹ =
      short P rfl i ((shortCharacter p i).val * t) := by
  apply FixedDescent.carrierToSplit_injective P rfl
  simp only [map_mul, map_inv, torus_split n hn, short, FixedDescent.carrierToSplit_toCarrier P rfl,
    shortElementary_val P rfl, shortSplit, conjugate_mul]
  have hcurve (j : Fin 3) (s : ExtensionField P) :
      product P (expand P p) * curve P (shortPosition i j) s * (product P (expand P p))⁻¹ =
        curve P (shortPosition i j) (((frobenius P)^[j.val] (shortCharacter p i)).val * s) := by
    exact (InputRealization.product_conjugate P rfl _ _ s).trans
      (congrArg (fun u : (ExtensionField P)ˣ => curve P (shortPosition i j) (u.val*s))
        (short_character n hn i j p))
  simp only [hcurve]
  rfl

/-- The torus acts on each native long positive root inside the fixed field. -/
theorem long_positive (i : Fin 3) (p : TorusParameters n hn) (t : fixedField P) :
    (SignedModel.roots n hn).torus p * long P rfl i t * ((SignedModel.roots n hn).torus p)⁻¹ =
      long P rfl i ((longCharacter p i).val * t) := by
  apply FixedDescent.carrierToSplit_injective P rfl
  simp only [map_mul, map_inv, torus_split n hn, long, FixedDescent.carrierToSplit_toCarrier P rfl,
    longElementary_val P rfl, longSplit]
  have h := InputRealization.product_conjugate P rfl (expand P p) (rootIndex (longPosition i)) t.val
  have hc := congrArg (fun u : (ExtensionField P)ˣ => curve P (longPosition i) (u.val*t.val))
    (long_character n hn i p)
  have he := h.trans hc
  exact he

end Triality.Standard.RootPresentationRecognition.PositiveTorusModel
