module
public import Theory.Representation.SL5ExteriorSquare.SeedCoreGeometry
public import Theory.Representation.SL5ExteriorSquare.MarkedRecognition

/-!
# Sylow fixed lines in the binary ten-dimensional exterior modules

Conjugating the actual Sylow subgroup to the standard flag puts its fixed
space in the highest wedge line. Marked recognition transports this bound
to either ten-dimensional irreducible, allowing the prescribed graph twist.
The constrained natural--dual point action in Chapter10 uses the bound to
exclude an inner action on its original quotient.

Source: Aschbacher--Smith 10.2.9, printed p.752, and I.1.6(7), p.408.
-/

public noncomputable section
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional Subgroup

/-- A full Sylow subgroup fixes at most the highest wedge line. -/
theorem square_sylow_fixed_finrank_le_one (S : Sylow 2 Group) :
    Module.finrank (ZMod 2) (BinaryOffender.fixedSpace (exteriorAction 2) S) ≤ 1 := by
  obtain ⟨g,hg⟩ := exists_sylow_map_eq_flagGroup S
  let E : V ≃ₗ[ZMod 2] V :=
    LinearMap.GeneralLinearGroup.toLinearEquiv ((exteriorAction 2).asGroupHom g)
  have hE (a : Group) (v : V) :
      E (exteriorAction 2 a v) = exteriorAction 2 ((MulAut.conj g) a) (E v) := by
    change exteriorAction 2 g (exteriorAction 2 a v) =
      exteriorAction 2 (g*a*g⁻¹) (exteriorAction 2 g v)
    simp only [← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  have hm := BinaryOffender.fixedSpace_map_equivariant (exteriorAction 2)
    (exteriorAction 2) (MulAut.conj g).toMonoidHom E hE (S : Subgroup Group)
  rw [hg] at hm
  have hd := Submodule.finrank_mono fixedSpace_flagGroup_le
  rw [standard_dimensions.1, ←hm, E.finrank_map_eq] at hd
  exact hd

/-- The bound holds for the prescribed actor on either rank-ten irreducible. -/
theorem marked_sylow_fixed_finrank_le_one
    {H W : Type*} [_root_.Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W) [IsIrreducible ρ]
    (mark : H ≃* Group) (hdim : Module.finrank (ZMod 2) W = 10)
    (S : Sylow 2 H) : Module.finrank (ZMod 2) (BinaryOffender.fixedSpace ρ S) ≤ 1 := by
  obtain ⟨a,E,_,hE⟩ := square_coordinates_of_finrank_ten ρ mark hdim
  have hm := BinaryOffender.fixedSpace_map_equivariant ρ (exteriorAction 2)
    a.toMonoidHom E hE (S : Subgroup H)
  have hd := square_sylow_fixed_finrank_le_one (S.mapSurjective (f := a.toMonoidHom) a.surjective)
  change Module.finrank (ZMod 2) (BinaryOffender.fixedSpace (exteriorAction 2)
    ((S : Subgroup H).map a.toMonoidHom)) ≤ 1 at hd
  rw [←hm,E.finrank_map_eq] at hd
  exact hd
end Representation.SL5ExteriorSquare
