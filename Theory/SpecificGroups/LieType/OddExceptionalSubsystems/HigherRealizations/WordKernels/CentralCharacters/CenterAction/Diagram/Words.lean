module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.Source
public import Theory.AlgebraicGroup.RootSystems.IntegralTitsCoherence

/-!
# An E6 opposition word and its pinning sign correction

Six repetitions of the bipartite Coxeter word act as minus the pinned diagram
on the E6 root lattice. This finite integral calculation does not yet identify
the action on the ambient E7/E8 roots or their Geck operators. We define the
actual invertible ambient matrix obtained by following the Tits word with the
root-reversing matrix; its operator action remains a separate obligation.

The inverse E6 Cartan matrix modulo two gives explicit coroot coordinates
correcting any six signs. We verify the resulting characters in the literal
E7 and E8 tori, over every coefficient ring. These calculations feed the
sign-corrected kernel comparison in `Diagram`.

Sources: GLS3 §1.12 (Tits lifts and coroot conjugation), §2.5 (longest words),
and the exceptional inclusions in Aschbacher–Smith A.2.17, printed p.39.
-/

@[expose] public section
noncomputable section

namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.Diagram
open Theory.AlgebraicGroup.StandardRootSystem
open scoped BigOperators

/-- Six repetitions of a bipartite E6 Coxeter word, in left-action order. -/
def oppositionWord : List (Fin 6) :=
  List.flatten (List.replicate 6 [0, 2, 5, 1, 3, 4])

/-- Simple reflection on coefficients in the E6 root lattice. -/
def reflectCoefficients (k : Fin 6) (c : Fin 6 → ℤ) : Fin 6 → ℤ :=
  fun i => if i = k then c i - ∑ j, c j * typeE6CartanMatrix j k else c i

/-- The rightmost listed reflection acts first. -/
def wordCoefficients (w : List (Fin 6)) (c : Fin 6 → ℤ) : Fin 6 → ℤ :=
  w.foldr reflectCoefficients c

/-- The selected word is opposition followed by the pinned diagram on the root lattice. -/
theorem oppositionWord_coefficients (i : Fin 6) :
    wordCoefficients oppositionWord (Pi.single i 1) =
      -Pi.single (typeE6DiagramPermutation i) 1 := by
  fin_cases i <;> decide

/-- The inverse E6 Cartan matrix on elements of exponent two. -/
def signCoordinates {A : Type*} [CommGroup A] (e : Fin 6 → A) : Fin 6 → A :=
  ![e 1 * e 3, e 0, e 3, e 0 * e 2 * e 5, e 5, e 3 * e 4]

/-- Every six prescribed signs can be corrected by simple-coroot signs. -/
theorem signCoordinates_cartan {A : Type*} [CommGroup A] (e : Fin 6 → A)
    (he : ∀ i, e i ^ 2 = 1) (i : Fin 6) :
    (∏ k, signCoordinates e k ^ typeE6CartanMatrix i k) = e i := by
  have hi (k : Fin 6) : (e k)⁻¹ = e k := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using he k
  have hm (k : Fin 6) : e k * e k = 1 := by simpa only [pow_two] using he k
  fin_cases i <;>
    simp [signCoordinates, typeE6CartanMatrix, Fin.prod_univ_succ, mul_pow, he, hi,
      mul_assoc, mul_left_comm, mul_comm, hm]
  all_goals rw [← mul_assoc, hm, one_mul]
end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.Diagram

namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.Diagram
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped BigOperators
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- A genuine integral unit on the complete ambient Cartan-plus-root lattice. -/
def oppositionUnit (j : Fin 6 → b.support) :
    (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)ˣ where
  val := omegaMatrix * titsWord (oppositionWord.map j)
  inv := titsWordInv (oppositionWord.map j) * omegaMatrix
  val_inv := by
    calc
      _ = omegaMatrix * (titsWord (oppositionWord.map j) *
        titsWordInv (oppositionWord.map j)) * omegaMatrix := by noncomm_ring
      _ = 1 := by rw [titsWord_mul_inv, mul_one, omegaMatrix_sq]
  inv_val := by
    calc
      _ = titsWordInv (oppositionWord.map j) * (omegaMatrix * omegaMatrix) *
        titsWord (oppositionWord.map j) := by noncomm_ring
      _ = 1 := by rw [omegaMatrix_sq, mul_one, titsWord_inv_mul]

/-- The diagonal sign correction, specified as actual simple-coroot parameters. -/
def signCorrectionParameter {S : Type*} [CommRing S]
    (j : Fin 6 → b.support) (e : Fin 6 → Sˣ) : b.support → Sˣ :=
  ∏ k, integralChevalleySimpleCorootParameter (j k) (signCoordinates e k)

/-- The proposed sign correction has the requested six root characters. -/
theorem signCorrectionParameter_scale {S : Type*} [CommRing S]
    (j : Fin 6 → b.support)
    (hj : ∀ i k, P.pairingIn ℤ (j i) (j k) = typeE6CartanMatrix i k)
    (e : Fin 6 → Sˣ) (he : ∀ i, e i ^ 2 = 1) (i : Fin 6) :
    integralChevalleyRootScale (P := P) (signCorrectionParameter j e) (j i) = e i := by
  let h : (b.support → Sˣ) →* Sˣ :=
    ⟨⟨fun u => integralChevalleyRootScale (P := P) u (j i),
      integralChevalleyRootScale_one (P := P) (b := b) (j i)⟩,
      fun u v => integralChevalleyRootScale_mul u v (j i)⟩
  change h (∏ k, integralChevalleySimpleCorootParameter (j k) (signCoordinates e k)) = _
  rw [map_prod]
  simp only [h, MonoidHom.coe_mk, OneHom.coe_mk,
    integralChevalleyRootScale_simpleCorootParameter, hj]
  exact signCoordinates_cartan e he i

attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

/-- Actual E7 root characters of the sign-correction diagonal. -/
theorem e7_signCorrectionParameter_scale {S : Type*} [CommRing S]
    (e : Fin 6 → Sˣ) (he : ∀ i, e i ^ 2 = 1) (i : Fin 6) :
    integralChevalleyRootScale (P := typeE7RootPairing)
      (signCorrectionParameter e7Node e) (e7Node i) = e i := by
  apply signCorrectionParameter_scale e7Node _ e he i
  intro a k
  exact (typeE7RootPairing_base_cartan_apply _ _).trans (e7_cartan_restrict a k)

/-- Actual E8 root characters of the sign-correction diagonal. -/
theorem e8_signCorrectionParameter_scale {S : Type*} [CommRing S]
    (e : Fin 6 → Sˣ) (he : ∀ i, e i ^ 2 = 1) (i : Fin 6) :
    integralChevalleyRootScale (P := typeE8RootPairing)
      (signCorrectionParameter e8Node e) (e8Node i) = e i := by
  apply signCorrectionParameter_scale e8Node _ e he i
  intro a k
  exact (typeE8RootPairing_base_cartan_apply _ _).trans (e8_cartan_restrict a k)
end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.Diagram
