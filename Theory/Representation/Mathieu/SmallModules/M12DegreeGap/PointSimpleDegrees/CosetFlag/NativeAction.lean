module

public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag.NativeBridge
public import Theory.Representation.Mathieu.SmallModules.M12DegreeGap.PointSimpleDegrees.CosetFlag.NativeAction.Certificate

/-!
# The native action on the 720 eleven-cosets of M₁₁

The finite certificate checks A gⱼ = gₖ (AB)ᵉ and B gⱼ = gₖ (AB)ᵉ on all eleven
points, using the literal published words and action tables. The numeric point
evaluator agrees with the native generators, products, and powers. Equality of
native permutations therefore gives equality in M₁₁. Passing to the actual left
cosets of ⟨AB⟩ proves the action table without any normality hypothesis.

The final coordinates are an application to the actual inverse-permutation
representation, through `NativeBridge.cosetCoordinates`.
Source context: James, J. Algebra 27 (1973), 57–111; `../source/README.md`.
-/

@[expose] public section
open Sporadic.Mathieu
namespace Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag
open NativeBridge

namespace NativeActionCertificate

private theorem mul_point (g h : M11) (x : Fin 11) :
    ((g * h).val x).val = (g.val (h.val x)).val := rfl

private theorem native_ext {g h : M11}
    (hp : ∀ x : Fin 11, (g.val x).val = (h.val x).val) : g = h := by
  apply Subtype.ext
  apply _root_.Equiv.ext
  intro x
  exact Fin.ext (hp x)

private theorem generator_point (s : Fin 2) (x : Fin 11) :
    ((generator s).val x).val = generatorPoint s x.val := by
  revert s x
  decide +kernel

private theorem word_point (w : List (Fin 2)) (x : Fin 11) :
    (((w.map generator).prod : M11).val x).val = wordPoint w x.val := by
  induction w with
  | nil => rfl
  | cons s w ih =>
    change ((generator s).val (((w.map generator).prod : M11).val x)).val = _
    rw [generator_point, ih]
    rfl

private theorem representative_point (j : Fin 720) (x : Fin 11) :
    ((representative j).val x).val = wordPoint (wordAt j.val) x.val := by
  unfold representative
  rw [word_point, wordAt_eq]

private theorem sylow_point (x : Fin 11) :
    (m11Sylow11Generator.val x).val =
      generatorPoint 0 (generatorPoint 1 x.val) := by
  revert x
  decide +kernel

private theorem power_point (n : ℕ) (x : Fin 11) :
    ((m11Sylow11Generator ^ n).val x).val = powerPoint n x.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', mul_point, sylow_point, ih]
    rfl

/-- All 1,440 right corrections hold in the literal native subgroup M₁₁. -/
theorem representative_correction (s : Fin 2) (j : Fin 720) :
    generator s * representative j =
      representative (leftIndex s j) * m11Sylow11Generator ^ correction s j.val := by
  apply native_ext
  intro x
  rw [mul_point, mul_point, generator_point, representative_point,
    representative_point, power_point]
  simpa only [leftIndex, leftAt_eq] using (checked_at s j).2 x

end NativeActionCertificate

/-- The published action table is the native action on the actual left cosets. -/
theorem nativeAction : NativeBridge.NativeAction := by
  intro s j
  change (QuotientGroup.mk (representative (leftIndex s j)) : ElevenCoset) =
    QuotientGroup.mk (generator s * representative j)
  rw [NativeActionCertificate.representative_correction]
  exact (QuotientGroup.mk_mul_of_mem _ (Subgroup.npow_mem_zpowers _ _)).symm

/-- Unconditional coordinates on the native eleven-coset permutation module. -/
noncomputable def nativeCosetCoordinates : CosetCoordinates :=
  NativeBridge.cosetCoordinates nativeAction

end Representation.MathieuSmall.M12DegreeGap.PointSimpleDegrees.CosetFlag
