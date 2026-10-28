module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.AmbientCount.TorusData
public import Theory.AlgebraicGroup.RootSubgroups.Cocharacter

/-!
# Actual D4 character and coroot coordinates

The chosen simple-coroot coordinates determine every character of `S.torus`.
They identify actual simple-root characters with the D4 Cartan rows and give
the simple-reflection formula on points. Algebraic torus maps with specified
simple-coroot images consequently have the corresponding character pullback.

The proof uses the realized character--cocharacter pairing and its uniqueness;
it does not assume a Weyl action, ambient conjugacy or a class count.

Source: Steinberg, `refs/KGroup/GLS3/Chapter2St2.tex`, §§6.1--6.4 and 11.2;
GLS3, Chapter 1, Remarks 1.9.6. The formulas use the actual `S.weight` and
`S.roots.rootCocharacter`, including the project's inverse-conjugation convention.
-/

@[expose] public noncomputable section
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount.TorusGeometry
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight

universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

omit [IsAlgClosed k] in
/-- The four realized simple-coroot coordinates determine a character. -/
theorem character_ext (S : Geometry K) {χ ψ : TorusWeight S.torus}
    (h : ∀ i : Fin 4, S.roots.weightPairing χ (S.simpleRoot i).val =
      S.roots.weightPairing ψ (S.simpleRoot i).val) : χ = ψ := by
  obtain ⟨a, rfl⟩ := S.weight.surjective χ
  obtain ⟨b, rfl⟩ := S.weight.surjective ψ
  congr 1
  change a.toAdd = b.toAdd
  funext i
  exact (S.weight_coordinate a.toAdd i).symm.trans
    ((h i).trans (S.weight_coordinate b.toAdd i))

omit [IsAlgClosed k] in
/-- Evaluate an actual weight on a chosen simple coroot. -/
theorem weight_coroot (S : Geometry K) (a : Weight) (i : Fin 4)
    (z : Variety.Point (KMult k)) :
    (S.weight (Multiplicative.ofAdd a)).pointCharacter
      ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints z) =
        (dPointEquiv 1 z 0 : k) ^ a i := by
  simpa only [S.weight_coordinate] using
    S.realized.weightPairing_spec (S.weight (Multiplicative.ofAdd a))
      (S.simpleRoot i).val z

omit [IsAlgClosed k] in
/-- The marked simple roots have the actual D4 Cartan pairing. -/
theorem simple_pairing (S : Geometry K) (i j : Fin 4) :
    S.roots.pairing (S.simpleRoot i).val (S.simpleRoot j).val =
      typeDCartanMatrix 2 i j := by
  have h := S.based.1 (S.simpleRoot i).val (S.simpleRoot j).val
  rw [S.simpleRoot_index, S.simpleRoot_index,
    typeDRootPairing_simpleIndex_pairing] at h
  exact_mod_cast h

omit [IsAlgClosed k] in
/-- A simple-root character has its Cartan row as weight coordinates. -/
theorem simple_rootWeight (S : Geometry K) (i : Fin 4) :
    S.roots.rootWeight (S.simpleRoot i).val =
      S.weight (Multiplicative.ofAdd (typeDCartanMatrix 2 i)) := by
  apply character_ext S
  intro j
  rw [S.realized.weightPairing_rootWeight, S.weight_coordinate, simple_pairing]

omit [IsAlgClosed k] in
/-- The coordinate reflection is multiplication by the corresponding power
of the actual simple-root character. -/
theorem reflection_character (S : Geometry K) (i : Fin 4) (a : Weight) :
    S.weight (Multiplicative.ofAdd (reflection i a)) =
      S.weight (Multiplicative.ofAdd a) *
        S.roots.rootWeight (S.simpleRoot i).val ^ (-a i) := by
  rw [simple_rootWeight, ← map_zpow, ← map_mul]
  congr 1
  change reflection i a = a + (-a i) • typeDCartanMatrix 2 i
  funext j
  change a j - a i * typeDCartanMatrix 2 i j =
    a j + (-a i) * typeDCartanMatrix 2 i j
  ring

/-- The point reflection formula built from the actual root and coroot.
Its realization by the Weyl action is a separate geometric obligation. -/
def simpleReflection (S : Geometry K) (i : Fin 4)
    (t : Variety.Point S.torus.carrierVariety) : Variety.Point S.torus.carrierVariety :=
  t * ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints
    ((S.roots.rootWeight (S.simpleRoot i).val).onPoints t))⁻¹

omit [IsAlgClosed k] in
/-- Evaluating the point reflection gives the specified weight reflection. -/
theorem simpleReflection_weight (S : Geometry K) (i : Fin 4) (a : Weight)
    (t : Variety.Point S.torus.carrierVariety) :
    (S.weight (Multiplicative.ofAdd a)).pointCharacter (simpleReflection S i t) =
      (S.weight (Multiplicative.ofAdd (reflection i a))).pointCharacter t := by
  rw [simpleReflection, map_mul, map_inv, weight_coroot, reflection_character]
  change _ = ((torusPointEval S.torus.carrierVariety t
    (S.weight (Multiplicative.ofAdd a) *
      S.roots.rootWeight (S.simpleRoot i).val ^ (-a i))) : k)
  rw [map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_neg]
  rfl

/-- Equality on simple-coroot points determines an algebraic character. -/
theorem character_ext_coroot (S : Geometry K) {χ ψ : TorusWeight S.torus}
    (h : ∀ (i : Fin 4) (z : Variety.Point (KMult k)),
      χ.pointCharacter ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints z) =
        ψ.pointCharacter ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints z)) :
    χ = ψ := by
  apply character_ext S
  intro i
  apply (weightCocharacterEquation_existsUnique S.torus χ
    (S.roots.rootCocharacter (S.simpleRoot i).val)).unique
  · exact S.realized.weightPairing_spec χ (S.simpleRoot i).val
  · intro z
    rw [h i z]
    exact S.realized.weightPairing_spec ψ (S.simpleRoot i).val z

/-- Permuting and powering the simple coroots determines the pullback on all
weights, by uniqueness of the character--cocharacter exponent. -/
theorem pullback_weight_of_coroot (S : Geometry K)
    (f : Theory.AlgebraicGroup.Morphism S.torus.carrierVariety S.torus.carrierVariety)
    (p : Fin 4 → Fin 4) (q : ℕ)
    (hf : ∀ (i : Fin 4) (z : Variety.Point (KMult k)),
      f.onPoints ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints z) =
        (S.roots.rootCocharacter (S.simpleRoot (p i)).val).onPoints (z ^ q))
    (a : Weight) (t : Variety.Point S.torus.carrierVariety) :
    (S.weight (Multiplicative.ofAdd a)).pointCharacter (f.onPoints t) =
      (S.weight (Multiplicative.ofAdd (a ∘ p))).pointCharacter t ^ q := by
  have heq : TorusCharacter.pullback f (S.weight (Multiplicative.ofAdd a)) =
      S.weight (Multiplicative.ofAdd (a ∘ p)) ^ q := by
    apply character_ext_coroot S
    intro i z
    change (S.weight (Multiplicative.ofAdd a)).pointCharacter
      (f.onPoints ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints z)) = _
    rw [hf, weight_coroot, dPointEquiv_pow]
    change (((dPointEquiv 1 z 0) ^ q : kˣ) : k) ^ a (p i) =
      ((torusPointEval S.torus.carrierVariety
        ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints z)
        (S.weight (Multiplicative.ofAdd (a ∘ p)) ^ q)) : k)
    rw [map_pow, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
    change ((dPointEquiv 1 z 0 : k) ^ q) ^ a (p i) =
      ((S.weight (Multiplicative.ofAdd (a ∘ p))).pointCharacter
        ((S.roots.rootCocharacter (S.simpleRoot i).val).onPoints z)) ^ q
    rw [weight_coroot]
    calc
      _ = (dPointEquiv 1 z 0 : k) ^ ((q : ℤ) * a (p i)) := by
        rw [zpow_mul, zpow_natCast]
      _ = (dPointEquiv 1 z 0 : k) ^ (a (p i) * (q : ℤ)) := by rw [mul_comm]
      _ = _ := by rw [zpow_mul, zpow_natCast]; rfl
  have ht := congrArg (fun χ : TorusWeight S.torus => χ.pointCharacter t) heq
  change _ = ((torusPointEval S.torus.carrierVariety t
    (S.weight (Multiplicative.ofAdd (a ∘ p)) ^ q)) : k) at ht
  rw [map_pow, Units.val_pow_eq_pow_val] at ht
  exact ht

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.AmbientCount.TorusGeometry
