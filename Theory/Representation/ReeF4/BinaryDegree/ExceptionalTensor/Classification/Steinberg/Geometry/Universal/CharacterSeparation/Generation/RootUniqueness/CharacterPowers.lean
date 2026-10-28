module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.RootWeights

/-!
# Powers of the concrete F4 root characters

Pairing with the four simple coroots embeds the real root space into four
coordinates. Transport of Laurent characters to the literal split torus is
injective in every characteristic. Consequently its root characters are
pairwise distinct, nontrivial, and have no higher powers among themselves.
The last assertion follows from reducedness of the real F4 root system; it
does not differentiate characters in the coefficient field.

These are the character comparisons needed for the concrete specialization
of GLS3, Theorem 1.9.5(b), in `refs/KGroup/GLS3/Chapter1.tex`.
-/

open Theory.AlgebraicGroup.StandardRootSystem
public noncomputable section
namespace Theory.AlgebraicGroup.F4Chevalley
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

private noncomputable def rootCoordinates : Vec 4 →ₗ[ℝ] (Fin 4 → ℝ) :=
  LinearMap.pi fun i =>
    (typeF4RootPairing.toLinearMap.flip
      (typeF4RootPairing.coroot (typeF4RootPairing_baseEquiv i)))

private lemma rootCoordinates_injective : Function.Injective rootCoordinates := by
  intro x y h
  apply typeF4RootPairing.toLinearMap.toPerfPair.injective
  apply typeF4RootPairing_base.flip.toWeightBasis.ext
  intro j
  let j' : typeF4RootPairing_base.support :=
    ⟨j.val, by simpa only [RootPairing.Base.flip_support] using j.property⟩
  have hj := congrFun h (typeF4RootPairing_baseEquiv.symm j')
  change typeF4RootPairing.toLinearMap x
      (typeF4RootPairing.coroot (typeF4RootPairing_baseEquiv
        (typeF4RootPairing_baseEquiv.symm j'))) =
    typeF4RootPairing.toLinearMap y
      (typeF4RootPairing.coroot (typeF4RootPairing_baseEquiv
        (typeF4RootPairing_baseEquiv.symm j'))) at hj
  rw [Equiv.apply_symm_apply] at hj
  simp only [RootPairing.Base.toWeightBasis_apply, LinearMap.toPerfPair_apply]
  exact hj

private lemma rootCoordinates_root (r : Root) :
    rootCoordinates (typeF4RootPairing.root r) = fun i => (torusRootExponent r i : ℝ) := by
  ext i
  change typeF4RootPairing.pairing r (typeF4RootPairing_baseEquiv i) = _
  exact (typeF4RootPairing.algebraMap_pairingIn ℤ _ _).symm

private lemma torusRootExponent_injective : Function.Injective torusRootExponent := by
  intro r s h
  apply typeF4RootPairing.root.injective
  apply rootCoordinates_injective
  rw [rootCoordinates_root, rootCoordinates_root, h]

private lemma torusRootExponent_nsmul_ne_zero (r : Root) {n : ℕ} (hn : n ≠ 0) :
    n • torusRootExponent r ≠ 0 := by
  intro h
  have hr : n • typeF4RootPairing.root r = 0 := by
    apply rootCoordinates_injective
    rw [map_nsmul, map_zero, rootCoordinates_root]
    ext i
    have hi := congrArg (fun z : Fin 4 → ℤ => (z i : ℝ)) h
    simpa using hi
  exact typeF4RootPairing.ne_zero r ((smul_eq_zero.mp hr).resolve_left hn)

private lemma torusRootExponent_nsmul_ne (r s : Root) {n : ℕ} (hn : 2 ≤ n) :
    n • torusRootExponent r ≠ torusRootExponent s := by
  intro h
  have hr : n • typeF4RootPairing.root r = typeF4RootPairing.root s := by
    apply rootCoordinates_injective
    rw [map_nsmul, rootCoordinates_root, rootCoordinates_root]
    ext i
    have hi := congrArg (fun z : Fin 4 → ℤ => (z i : ℝ)) h
    simpa using hi
  let : n.AtLeastTwo := ⟨hn⟩
  exact typeF4RootPairing.nsmul_notMem_range_root ⟨s, hr.symm⟩

local instance : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
  (splitTorus (k := k)).carrierAlgebraicGroup

private lemma splitTorusCharacter_injective :
    Function.Injective (splitTorusCharacter (k := k)) := by
  intro z w h
  apply dLaurentCharacter_injective (k := k) 4
  apply AlgebraicGroup.Morphism.ext
  funext x
  have hx := congrArg (fun c : TorusWeight (splitTorus (k := k)) =>
    c.onPoints ((splitTorusIso (k := k)).hom.onPoints x)) h
  change (dLaurentCharacter 4 z).onPoints
      ((splitTorusIso (k := k)).inv.onPoints
        ((splitTorusIso (k := k)).hom.onPoints x)) =
    (dLaurentCharacter 4 w).onPoints
      ((splitTorusIso (k := k)).inv.onPoints
        ((splitTorusIso (k := k)).hom.onPoints x)) at hx
  rw [(splitTorusIso (k := k)).hom_inv_id] at hx
  exact hx

private lemma splitTorusCharacter_nsmul (n : ℕ) (z : Fin 4 → ℤ) :
    splitTorusCharacter (k := k) (n • z) = (splitTorusCharacter z) ^ n := by
  let precomp : TorusCharacter (dVariety k 4) →* TorusWeight (splitTorus (k := k)) :=
    { toFun := fun c => c.comp (splitTorusIso (k := k)).inv
      map_one' := rfl
      map_mul' _ _ := rfl }
  have h := (dLaurentCharacterHom (k := k) 4).map_nsmul n z
  have h' : dLaurentCharacter (k := k) 4 (n • z) = (dLaurentCharacter 4 z) ^ n := h
  change precomp (dLaurentCharacter 4 (n • z)) = precomp (dLaurentCharacter 4 z) ^ n
  rw [h', map_pow]

private lemma splitTorusCharacter_zero : splitTorusCharacter (k := k) 0 = 1 := by
  have h : dLaurentCharacter (k := k) 4 0 = 1 := (dLaurentCharacterHom 4).map_zero
  apply AlgebraicGroup.Morphism.ext
  funext x
  change ((dLaurentCharacter (k := k) 4 0).comp (splitTorusIso (k := k)).inv).toVariety.toFun x = _
  rw [h]
  rfl

private lemma rootWeight_eq_character (r : Root) :
    rootWeight (k := k) r = splitTorusCharacter (torusRootExponent r) := by
  apply TorusCharacter.pointCharacter_injective
  ext s
  exact (rootWeight_pointCharacter r s).trans
    (congrArg Units.val (splitTorusCharacter_apply_point (torusRootExponent r) s)).symm

/-- Distinct literal F4 roots define distinct characters of the split torus. -/
lemma concreteRootWeight_injective : Function.Injective (rootWeight (k := k)) := by
  intro r s h
  rw [rootWeight_eq_character, rootWeight_eq_character] at h
  exact torusRootExponent_injective (splitTorusCharacter_injective h)

/-- No positive power of a literal root character is trivial. -/
lemma concreteRootWeight_pow_ne_one (r : Root) {n : ℕ} (hn : n ≠ 0) :
    (rootWeight (k := k) r) ^ n ≠ 1 := by
  rw [rootWeight_eq_character]
  rw [← splitTorusCharacter_nsmul, ← splitTorusCharacter_zero (k := k)]
  intro h
  exact torusRootExponent_nsmul_ne_zero r hn
    (splitTorusCharacter_injective h)

/-- Every literal root character is nontrivial. -/
lemma concreteRootWeight_ne_one (r : Root) : rootWeight (k := k) r ≠ 1 := by
  simpa only [pow_one] using concreteRootWeight_pow_ne_one (k := k) r (n := 1) (by decide)

/-- Reducedness excludes higher powers from the literal root characters. -/
lemma concreteRootWeight_pow_ne (r s : Root) {n : ℕ} (hn : 2 ≤ n) :
    (rootWeight (k := k) r) ^ n ≠ rootWeight s := by
  rw [rootWeight_eq_character, rootWeight_eq_character]
  rw [← splitTorusCharacter_nsmul]
  intro h
  exact torusRootExponent_nsmul_ne r s hn (splitTorusCharacter_injective h)

end Theory.AlgebraicGroup.F4Chevalley
