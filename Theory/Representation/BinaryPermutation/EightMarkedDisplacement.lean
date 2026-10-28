module
public import Theory.Representation.BinaryPermutation.EightOrthogonalActors

/-!
# Transvection exclusion in marked copies of the natural A₈ action

The concrete even-permutation displacement bound transfers through the
specified group and linear equivalences. The equivalence identifies the
actual displacement ranges, preserving their dimensions.

Source application: Aschbacher--Smith 12.9.4, printed pp.859--860.
-/

public noncomputable section
open Module Subgroup
namespace BinaryPermutation.EightOrthogonalActors
variable {G V : Type*} [Group G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [FiniteDimensional (ZMod 2) V] in
/-- Every nonidentity involution in the marked natural A₈ action moves
at least two dimensions, using the supplied intertwiner. -/
theorem marked_two_le_displacement
    (ρ : Representation (ZMod 2) G V)
    (e : G ≃* alternatingGroup (Fin 8))
    (c : V ≃ₗ[ZMod 2] natural (Fin 8))
    (he : ∀ a v, c (ρ a v) = naturalRepresentation (Fin 8) (e a).val (c v))
    (a : G) (ha : a ≠ 1) (ha2 : a^2 = 1) :
    2 ≤ finrank (ZMod 2) (ρ a - LinearMap.id).range := by
  have hr : ((ρ a - LinearMap.id).range).map c.toLinearMap =
      (naturalRepresentation (Fin 8) (e a).val - LinearMap.id).range := by
    ext w
    constructor
    · rintro ⟨u,⟨z,rfl⟩,rfl⟩
      refine ⟨c z,?_⟩
      change naturalRepresentation (Fin 8) (e a).val (c z) - c z = c (ρ a z - z)
      rw [map_sub,he]
    · rintro ⟨z,rfl⟩
      refine ⟨ρ a (c.symm z) - c.symm z,⟨c.symm z,rfl⟩,?_⟩
      change c (ρ a (c.symm z) - c.symm z) = _
      rw [map_sub,he,c.apply_symm_apply]
      rfl
  have hh := two_le_displacement (e a).val (e a).property
    (fun h => ha (e.injective ((Subtype.ext h : e a = 1).trans e.map_one.symm)))
    (by simpa only [map_pow,map_one,Subgroup.coe_pow,Subgroup.coe_one] using
      congrArg (fun x : G => (e x).val) ha2)
  rw [←hr,c.finrank_map_eq] at hh
  exact hh
end BinaryPermutation.EightOrthogonalActors
