module

public import Theory.Representation.OrthogonalFourPlusMatrix.OuterWeakClosureGeometry.FixedLine.Involution
public import Theory.Representation.OrthogonalFourPlusMatrix.OuterWeakClosureGeometry.FixedLine.Normalized

/-!
# Weak-closure geometry of an outer actor fixing a singular field line

An outer involution fixing the singular matrix unit has a nonsingular center
fixed by the whole commuting actor. Left multiplication through this center
reduces the action to the eight-element pointwise stabilizer of `1` and `E01`.
The fixed hyperplane of the factor swap has a pointwise stabilizer of index
at most four, and its moved space contains two distinct nonsingular field
lines. These are the precise matrix-space conclusions used in the outer
branch of Aschbacher–Smith 9.4.5, printed pp.736–737.
-/

@[expose] public noncomputable section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary.OuterWeakClosureGeometry.FixedLine

/-- A large elementary outer actor fixing the singular matrix unit has a
subspace fixed by an index-four subgroup whose moved space meets two
nonsingular field lines. -/
theorem fixed_unit_geometry {H : Type*} [Group H] [Finite H]
    (f : H →* (V ≃ₗ[F] V)) (hf : Function.Injective f)
    (hdet : ∀ h M, (f h M).det = M.det)
    (hcomm : ∀ a b, f a * f b = f b * f a)
    (hinv : ∀ h M, f h (f h M) = M)
    (hN : ∀ h, f h (Matrix.single 0 1 1) = Matrix.single 0 1 1)
    (hcard : 8 ≤ Nat.card H) (houter : ∃ t : H, ∀ g : G, f t ≠ matrixHom g) :
    ∃ U : Submodule (ZMod 2) V, ∃ K : Subgroup H,
      K.index ≤ 4 ∧ (∀ h ∈ K, ∀ v ∈ U, f h v = v) ∧
      ∃ x ∈ Normalized.movedSpace f U, ∃ y ∈ Normalized.movedSpace f U,
        x.det ≠ 0 ∧ y.det ≠ 0 ∧ y ∉ Submodule.span F ({x} : Set V) := by
  obtain ⟨t, ht⟩ := houter
  obtain ⟨u, hu, hu10, hfix⟩ :=
    common_fixed_center_of_outer f hdet hcomm hinv hN t ht
  exact Normalized.geometry_of_upper_fixed f hf hdet hcard u hu hu10 hfix hN

end ClassicalOrthogonal.FourPlusMatrix.Binary.OuterWeakClosureGeometry.FixedLine
