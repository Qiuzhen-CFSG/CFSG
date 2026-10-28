module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.Reduction
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.Source
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.Diagram.Intertwiner
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.Diagram.Words
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.Diagram.RootAction
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.HigherRealizations.WordKernels.CentralCharacters.CenterAction.Diagram.OperatorAction

/-!
# The pinned E6 diagram preserves the higher matrix kernels

An integral intertwiner on the complete ambient matrix lattice induces the
pinned diagram on all six signed curves and hence preserves the literal word
kernel. It suffices to intertwine the operators up to a common sign in the
positive and negative directions at each node: the explicitly verified
simple-coroot correction removes these signs before extending to words.
Factorial cancellation happens over the integers, so characteristic three
requires no exception.

The opposition word acts as minus the pinned diagram on the actual E7/E8
roots. Its integral Tits lift, followed by the root-reversing matrix, gives
the signed operator intertwiner. Applying the sign correction proves the
two unconditional kernel inclusions `e7Six_ker_le_diagram` and
`e8Six_ker_le_diagram`. These discharge exactly the diagram-kernel premises
of `e7Six_centerAction_of_torus` and `e8Six_centerAction_of_torus`, over every
field. Neither a descended diagram action nor a central-character assertion
is presumed to exist.

Sources: GLS3 §§1.12 and 2.5–2.6, for the exceptional inclusions in
Aschbacher–Smith A.2.17, printed p.39 (`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section

open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.Diagram
attribute [local instance] Classical.decEq
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- An integral pinning intertwiner on the full ambient lattice. -/
def PreservesPinning (j : Fin 6 → b.support)
    (C : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)ˣ) : Prop :=
  ∀ s i, C.val * (simpleFamily (b := b)).dividedPower (s, j i) 1 =
    (simpleFamily (b := b)).dividedPower (s, j (typeE6DiagramPermutation i)) 1 * C.val

variable (F : Type*) [Field F]

/-- Compatibility on the signed curves extends to the actual free-word kernel. -/
theorem six_ker_le_of_unit_intertwiner
    (v : SixNodeWord F →* ExceptionalSplit.rootGenerated P b F)
    (U : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) F)ˣ)
    (hU : ∀ s i t, U * (v (FreeGroup.of (s, i, t))).val =
      (v (FreeGroup.of (s, typeE6DiagramPermutation i, t))).val * U) :
    v.ker ≤ (v.comp (diagramWord F)).ker := by
  let V := (ExceptionalSplit.rootGenerated P b F).subtype.comp v
  have he : (V.comp (diagramWord F)) = (MulAut.conj U).toMonoidHom.comp V := by
    apply FreeGroup.ext_hom
    rintro ⟨s, i, t⟩
    change (v (diagramWord F (FreeGroup.of (s, i, t)))).val =
      U * (v (FreeGroup.of (s, i, t))).val * U⁻¹
    rw [diagramWord_of, hU, mul_assoc, mul_inv_cancel, mul_one]
  intro w hw
  change v (diagramWord F w) = 1
  apply Subtype.ext
  change V (diagramWord F w) = 1
  have hw' : V w = 1 := by
    change (v w).val = 1
    rw [show v w = 1 from hw]
    rfl
  have hh := DFunLike.congr_fun he w
  change V (diagramWord F w) = (MulAut.conj U) (V w) at hh
  simpa only [hw', map_one] using hh

/-- A full integral pinning intertwiner preserves the literal evaluation kernel
in every field, with no exclusion of characteristic three. -/
theorem six_ker_le_of_integral_intertwiner
    (j : Fin 6 → b.support)
    (v : SixNodeWord F →* ExceptionalSplit.rootGenerated P b F)
    (hv : ∀ s i t, (v (FreeGroup.of (s, i, t))).val =
      (simpleFamily (b := b)).unit (s, j i) t)
    (C : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)ˣ)
    (hC : PreservesPinning j C) :
    v.ker ≤ (v.comp (diagramWord F)).ker := by
  apply six_ker_le_of_unit_intertwiner F v
    (Units.map (Int.castRingHom F).mapMatrix.toMonoidHom C)
  intro s i t
  rw [hv, hv]
  have hi := signed_unit_intertwine C (s, j i)
    (s, j (typeE6DiagramPermutation i)) 1
    (by simpa using hC s i) t
  simpa only [Int.cast_one, one_mul] using hi

local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _

/-- The integral matrix criterion at the exact E7 consumer. -/
theorem e7Six_ker_le_of_integral_intertwiner
    (C : (Matrix (typeE7RootPairing_base.support ⊕ typeE7Roots)
      (typeE7RootPairing_base.support ⊕ typeE7Roots) ℤ)ˣ)
    (hC : PreservesPinning e7Node C) :
    (e7Six F).ker ≤ ((e7Six F).comp (diagramWord F)).ker := by
  apply six_ker_le_of_integral_intertwiner F e7Node (e7Six F) _ C hC
  intro s i t
  simp [e7Simple, e7Node]

/-- The integral matrix criterion at the exact E8 consumer. -/
theorem e8Six_ker_le_of_integral_intertwiner
    (C : (Matrix (typeE8RootPairing_base.support ⊕ typeE8Roots)
      (typeE8RootPairing_base.support ⊕ typeE8Roots) ℤ)ˣ)
    (hC : PreservesPinning e8Node C) :
    (e8Six F).ker ≤ ((e8Six F).comp (diagramWord F)).ker := by
  apply six_ker_le_of_integral_intertwiner F e8Node (e8Six F) _ C hC
  intro s i t
  simp [e8Simple, e8Node]
end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.Diagram

namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.Diagram
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction RootPairing.SimpleGeckGroup
variable {ι R M N : Type*} [Field R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
  {b : P.Base} [Fintype ι] [DecidableEq ι]

/-- The same torus sign acts on the positive and negative simple curves. -/
theorem torus_signed_unit {S : Type*} [CommRing S]
    (u : b.support → Sˣ) (i : b.support) (e : Sˣ)
    (he : e ^ 2 = 1) (hu : integralChevalleyRootScale (P := P) u i = e)
    (s : Bool) (t : S) :
    (integralChevalleyTorusElement (P := P) u)⁻¹ *
      (simpleFamily (b := b)).unit (s, i) t *
      integralChevalleyTorusElement (P := P) u =
        (simpleFamily (b := b)).unit (s, i) ((e : S) * t) := by
  let := P.indexNeg
  have hn : integralChevalleyRootScale (P := P) u (-(i : ι)) = e := by
    have hi : e⁻¹ = e := by
      apply inv_eq_of_mul_eq_one_left
      simpa only [pow_two] using he
    rw [← hi, ← hu]
    simp [integralChevalleyRootScale, RootPairing.pairingIn_reflectionPerm_self_left]
  cases s
  · simpa only [rootCurveUnit_neg_simple, negativeUnit, hn] using
      integralChevalleyRootCurve_torus_conjugation (P := P) u (-(i : ι)) t
  · simpa only [rootCurveUnit_simple, positiveUnit, hu] using
      integralChevalleyRootCurve_torus_conjugation (P := P) u (i : ι) t

/-- Arbitrary integral signs in a full ambient intertwiner can be corrected
by the six simple coroots before passing to words. -/
theorem six_ker_le_of_integral_signed_intertwiner (F : Type*) [Field F]
    (j : Fin 6 → b.support)
    (hj : ∀ i k, P.pairingIn ℤ (j i) (j k) = typeE6CartanMatrix i k)
    (v : SixNodeWord F →* ExceptionalSplit.rootGenerated P b F)
    (hv : ∀ s i t, (v (FreeGroup.of (s, i, t))).val =
      (simpleFamily (b := b)).unit (s, j i) t)
    (C : (Matrix (b.support ⊕ ι) (b.support ⊕ ι) ℤ)ˣ)
    (e : Fin 6 → ℤˣ) (he : ∀ i, e i ^ 2 = 1)
    (hC : ∀ s i, C.val * (simpleFamily (b := b)).dividedPower (s, j i) 1 =
      ((e i : ℤ) • (simpleFamily (b := b)).dividedPower
        (s, j (typeE6DiagramPermutation i)) 1) * C.val) :
    v.ker ≤ (v.comp (diagramWord F)).ker := by
  let d : Fin 6 → Fˣ := fun k => Units.map (Int.castRingHom F).toMonoidHom
    (e (typeE6DiagramPermutation k))
  have hd (k : Fin 6) : d k ^ 2 = 1 := by
    dsimp only [d]
    rw [← map_pow, he, map_one]
  let T := integralChevalleyTorusElement (P := P) (signCorrectionParameter j d)
  let U := Units.map (Int.castRingHom F).mapMatrix.toMonoidHom C
  apply six_ker_le_of_unit_intertwiner F v (T⁻¹ * U)
  intro s i t
  rw [hv, hv]
  have hi := signed_unit_intertwine C (s, j i)
    (s, j (typeE6DiagramPermutation i)) (e i : ℤ) (hC s i) t
  change U * _ = _ * U at hi
  have ht := torus_signed_unit (signCorrectionParameter j d)
    (j (typeE6DiagramPermutation i)) (d (typeE6DiagramPermutation i))
    (hd _) (signCorrectionParameter_scale j hj d hd _) s (((e i : ℤ) : F) * t)
  have hdi : (d (typeE6DiagramPermutation i) : F) = ((e i : ℤ) : F) := by
    simp [d]
  have hes : ((e i : ℤ) : F) * ((e i : ℤ) : F) = 1 := by
    have h : (e i : ℤ) * (e i : ℤ) = 1 :=
      congrArg Units.val (show e i * e i = 1 by simpa only [pow_two] using he i)
    rw [← Int.cast_mul, h, Int.cast_one]
  rw [hdi, ← mul_assoc, hes, one_mul] at ht
  change T⁻¹ * _ * T = _ at ht
  have ht' := congrArg (fun z => z * T⁻¹) ht
  simp only [mul_assoc, mul_inv_cancel, mul_one] at ht'
  calc
    (T⁻¹ * U) * _ = T⁻¹ * (U * _) := mul_assoc _ _ _
    _ = T⁻¹ * (_ * U) := by rw [hi]
    _ = (T⁻¹ * _) * U := (mul_assoc _ _ _).symm
    _ = (_ * T⁻¹) * U := by rw [ht']
    _ = _ * (T⁻¹ * U) := mul_assoc _ _ _
end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.Diagram

namespace TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.Diagram
open Theory.AlgebraicGroup.StandardRootSystem RootPairing.SimpleGeckGroup
attribute [local instance] Classical.decEq
local instance : Fintype typeE7Roots := Fintype.ofFinite _
local instance : Fintype typeE8Roots := Fintype.ofFinite _
variable (F : Type*) [Field F]

/-- The signed integral criterion discharges exactly the diagram-kernel premise
of the E7 center-action assembly. -/
theorem e7Six_ker_le_of_integral_signed_intertwiner
    (C : (Matrix (typeE7RootPairing_base.support ⊕ typeE7Roots)
      (typeE7RootPairing_base.support ⊕ typeE7Roots) ℤ)ˣ)
    (e : Fin 6 → ℤˣ) (he : ∀ i, e i ^ 2 = 1)
    (hC : ∀ s i, C.val * (simpleFamily (b := typeE7RootPairing_base)).dividedPower
        (s, e7Node i) 1 =
      ((e i : ℤ) • (simpleFamily (b := typeE7RootPairing_base)).dividedPower
        (s, e7Node (typeE6DiagramPermutation i)) 1) * C.val) :
    (e7Six F).ker ≤ ((e7Six F).comp (diagramWord F)).ker := by
  apply six_ker_le_of_integral_signed_intertwiner F e7Node _ (e7Six F) _ C e he hC
  · intro i k
    exact (typeE7RootPairing_base_cartan_apply _ _).trans (e7_cartan_restrict i k)
  · intro s i t
    simp [e7Simple, e7Node]

/-- The signed integral criterion discharges exactly the diagram-kernel premise
of the E8 center-action assembly. -/
theorem e8Six_ker_le_of_integral_signed_intertwiner
    (C : (Matrix (typeE8RootPairing_base.support ⊕ typeE8Roots)
      (typeE8RootPairing_base.support ⊕ typeE8Roots) ℤ)ˣ)
    (e : Fin 6 → ℤˣ) (he : ∀ i, e i ^ 2 = 1)
    (hC : ∀ s i, C.val * (simpleFamily (b := typeE8RootPairing_base)).dividedPower
        (s, e8Node i) 1 =
      ((e i : ℤ) • (simpleFamily (b := typeE8RootPairing_base)).dividedPower
        (s, e8Node (typeE6DiagramPermutation i)) 1) * C.val) :
    (e8Six F).ker ≤ ((e8Six F).comp (diagramWord F)).ker := by
  apply six_ker_le_of_integral_signed_intertwiner F e8Node _ (e8Six F) _ C e he hC
  · intro i k
    exact (typeE8RootPairing_base_cartan_apply _ _).trans (e8_cartan_restrict i k)
  · intro s i t
    simp [e8Simple, e8Node]

/-- The pinned E6 diagram preserves the literal six-node kernel in E7 over
every field, including characteristic three. This discharges the diagram-kernel
premise of `e7Six_centerAction_of_torus`. -/
theorem e7Six_ker_le_diagram :
    (e7Six F).ker ≤ ((e7Six F).comp (diagramWord F)).ker := by
  obtain ⟨e, he, hC⟩ :=
    e7_exists_oppositionUnit_signed_intertwiner e7_oppositionWord_root
  exact e7Six_ker_le_of_integral_signed_intertwiner F (oppositionUnit e7Node) e he hC

/-- The pinned E6 diagram preserves the literal six-node kernel in E8 over
every field, including characteristic three. This discharges the diagram-kernel
premise of `e8Six_centerAction_of_torus`. -/
theorem e8Six_ker_le_diagram :
    (e8Six F).ker ≤ ((e8Six F).comp (diagramWord F)).ker := by
  obtain ⟨e, he, hC⟩ :=
    e8_exists_oppositionUnit_signed_intertwiner e8_oppositionWord_root
  exact e8Six_ker_le_of_integral_signed_intertwiner F (oppositionUnit e8Node) e he hC
end TwistedE6.FoldedSubsystem.HigherRealizations.CentralCharacters.CenterAction.Diagram
