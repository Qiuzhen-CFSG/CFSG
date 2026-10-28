module
public import Theory.SpecificGroups.BinaryLinear.PointStabilizerRank
/-!
# The two-core quotient of a binary three-space point stabilizer

The point stabilizer is the parabolic of its one-dimensional span. Its
Levi quotient is GL1(2) times GL2(2), hence S3. The construction retains
the actual nonzero vector and the original intrinsic two-core quotient.

Source: Aschbacher–Smith, 13.7.6(1), printed p.940.
-/
@[expose] public section
namespace BinaryLinear.PointStabilizerRank
open SmallParabolicLevi OuterCyclic
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
/-- The actual binary three-space point stabilizer has two-core quotient S3. -/
theorem three_point_quotient (hd : Module.finrank (ZMod 2) V = 3)
    (v : V) (hv : v ≠ 0) :
    Nonempty ((MulAction.stabilizer (BinaryLinear.GL V) v ⧸
      pCore 2 (MulAction.stabilizer (BinaryLinear.GL V) v)) ≃* Equiv.Perm (Fin 3)) := by
  rw [stabilizer_eq_parabolic]
  let W := Submodule.span (ZMod 2) {v}
  have hW : Module.finrank (ZMod 2) W = 1 := finrank_span_singleton hv
  have hQ : Module.finrank (ZMod 2) (V ⧸ W) = 2 := by
    have hh := W.finrank_quotient_add_finrank
    rw [hW,hd] at hh
    omega
  let a := (Module.finBasisOfFinrankEq (ZMod 2) W hW).equivFun
  let b := (Module.finBasisOfFinrankEq (ZMod 2) (V ⧸ W) hQ).equivFun
  let : Unique (LinearGroup 1) :=
    { default := 1
      uniq := fun _g => (slEquivLinear 1).symm.injective (Subsingleton.elim _ _) }
  exact ⟨(quotientTwoCoreEquivOfCoordinates W a b).trans
    ((MulEquiv.uniqueProd (N := LinearGroup 1) (M := LinearGroup 2)).trans
      linearTwoEquivSymmetricThree)⟩
end BinaryLinear.PointStabilizerRank
