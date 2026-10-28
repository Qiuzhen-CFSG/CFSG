module
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.ProjectiveAction
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry

/-!
# A projective intertwiner from point-parabolic preservation

The actual symplectic group is transitive on projective points, by its
transitivity on nonzero vectors. If an automorphism takes the standard
point stabilizer to a conjugate, the two transitive actions have matching
stabilizers. Choosing transporters constructs a bijection of projective
points intertwining the automorphism and the natural matrix action.

This construction uses point-parabolic preservation alone. It does not yet
assert that the resulting permutation preserves orthogonality; that is the
remaining finite polar-geometry obligation in the classification argument.

Source: the diagram-automorphism fact used in Aschbacher--Smith F.1.12,
printed pp.263--264 of `refs/quasithin.pdf`.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
open Projectivization
variable {F : Type*} [Field F]

/-- The actual matrix group is transitive on projective points. -/
theorem projective_transitive (p q : ProjectivePoint F) :
    ∃ g : Sp F, g • p = q := by
  obtain ⟨g, hg⟩ := TwoLocalCover.nonzero_vector_transitive p.rep_nonzero q.rep_nonzero
  refine ⟨g, ?_⟩
  rw [← mk_rep p, smul_mk]
  simp only [hg, mk_rep]

private theorem exists_intertwiner_of_stabilizer_map
    {G X : Type*} [Group G] [MulAction G X]
    (htrans : ∀ p q : X, ∃ g : G, g • p = q)
    (a : MulAut G) (p q : X)
    (hstab : (MulAction.stabilizer G p).map a.toMonoidHom = MulAction.stabilizer G q) :
    ∃ φ : Equiv.Perm X, ∀ h x, φ (h • x) = a h • φ x := by
  classical
  have heq (x y : G) : a x • q = a y • q ↔ x • p = y • p := by
    calc
      a x • q = a y • q ↔ a (y⁻¹ * x) ∈ MulAction.stabilizer G q := by
        simp only [MulAction.mem_stabilizer_iff, map_mul, map_inv, mul_smul,
          inv_smul_eq_iff]
      _ ↔ y⁻¹ * x ∈ MulAction.stabilizer G p := by
        rw [← hstab, Subgroup.mem_map_equiv]
        simp
      _ ↔ x • p = y • p := by
        simp only [MulAction.mem_stabilizer_iff, mul_smul, inv_smul_eq_iff]
  choose t ht using htrans p
  let f : X → X := fun x => a (t x) • q
  have hf (h : G) : f (h • p) = a h • q :=
    (heq _ _).mpr (ht _)
  have hinj : Function.Injective f := by
    intro x y h
    have he := (heq (t x) (t y)).mp h
    simpa only [ht] using he
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨h, hh⟩ := htrans q x
    refine ⟨a.symm h • p, ?_⟩
    rw [hf, a.apply_symm_apply, hh]
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  intro h x
  change f (h • x) = a h • f x
  rw [← ht x, ← mul_smul, hf, map_mul, mul_smul, hf]

/-- Point-parabolic preservation yields a permutation of the actual projective
points intertwining the group automorphism and its matrix action. -/
theorem exists_projective_intertwiner (a : MulAut (Sp F))
    (ha : PreservesParabolicClass a pointParabolic) :
    ∃ φ : Equiv.Perm (ProjectivePoint F),
      ∀ (h : Sp F) (p : ProjectivePoint F), φ (h • p) = a h • φ p := by
  obtain ⟨g, hg⟩ := ha
  apply exists_intertwiner_of_stabilizer_map projective_transitive a
    standardPoint (g • standardPoint)
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj, standardPoint_stabilizer]
  exact hg

end Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
