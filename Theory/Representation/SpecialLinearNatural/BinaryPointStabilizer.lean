module
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Projectivization.Action

/-!
# Point stabilizers on the binary natural three-space

Over F₂ a projective point has a unique nonzero representative. Two-transitivity
of SL₃ on projective points therefore makes a vector stabilizer transitive
on the vectors outside its fixed line. This applies to the literal natural
conjugation action in Aschbacher--Smith 10.2.11, printed p.754.
-/

public noncomputable section
namespace Representation.BinaryPointStabilizer

private theorem binary_projective_injective (v w : Fin 3 → ZMod 2)
    (hv : v ≠ 0) (hw : w ≠ 0)
    (h : Projectivization.mk (ZMod 2) v hv = Projectivization.mk (ZMod 2) w hw) : v = w := by
  obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff (ZMod 2) v w hv hw).mp h
  have hu1 : u = 1 := (by decide : ∀ u : (ZMod 2)ˣ, u = 1) u
  simpa only [hu1, one_smul] using hu.symm

/-- The stabilizer of a nonzero vector is transitive outside its binary line. -/
theorem exists_point_fixer (u v w : Fin 3 → ZMod 2)
    (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0) (hvu : v ≠ u) (hwu : w ≠ u) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2),
      Representation.specialLinearNatural 3 g u = u ∧
      Representation.specialLinearNatural 3 g v = w := by
  have huv : Projectivization.mk (ZMod 2) u hu ≠ Projectivization.mk (ZMod 2) v hv :=
    fun h => hvu (binary_projective_injective u v hu hv h).symm
  have huw : Projectivization.mk (ZMod 2) u hu ≠ Projectivization.mk (ZMod 2) w hw :=
    fun h => hwu (binary_projective_injective u w hu hw h).symm
  obtain ⟨g, hg, hg'⟩ := (MulAction.is_two_pretransitive_iff
    (G := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (α := Projectivization (ZMod 2) (Fin 3 → ZMod 2))).mp inferInstance huv huw
  rw [Projectivization.smul_mk] at hg hg'
  exact ⟨g, binary_projective_injective _ _ _ _ hg,
    binary_projective_injective _ _ _ _ hg'⟩

end Representation.BinaryPointStabilizer
