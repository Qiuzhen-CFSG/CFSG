module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal

/-!
# Quotients of primitive groups come from point stabilizers

If the kernel of a surjective homomorphism is transitive, every coset of
the kernel meets each point stabilizer: multiply a representative by a
kernel element that brings its image of the point back to the point.
Thus restriction to the stabilizer is still surjective.

In a faithful primitive action every nontrivial normal subgroup is
transitive (Wielandt, *Finite Permutation Groups*, Theorem 7.1, through
Mathlib's normal-orbit criterion). Consequently every noninjective
quotient map restricts to a surjection on each point stabilizer.
-/

namespace MonoidHom

open MulAction

/-- A transitive kernel lets a point stabilizer represent every quotient element. -/
public theorem surjective_domRestrict_stabilizer_of_pretransitive_ker
    {G X S : Type*} [Group G] [Group S] [MulAction G X]
    (f : G →* S) (hf : Function.Surjective f) [IsPretransitive f.ker X] (a : X) :
    Function.Surjective (f.domRestrict (stabilizer G a)) := by
  intro s
  obtain ⟨g, rfl⟩ := hf s
  obtain ⟨k, hk⟩ := exists_smul_eq f.ker a (g • a)
  have hfix : (k : G)⁻¹ * g ∈ stabilizer G a := by
    change ((k : G)⁻¹ * g) • a = a
    rw [mul_smul, inv_smul_eq_iff]
    exact hk.symm
  refine ⟨⟨(k : G)⁻¹ * g, hfix⟩, ?_⟩
  change f ((k : G)⁻¹ * g) = f g
  rw [map_mul, map_inv, show f (k : G) = 1 from k.property, inv_one, one_mul]

/-- A noninjective quotient of a faithful primitive group is already a
quotient of every point stabilizer. -/
public theorem surjective_domRestrict_stabilizer_of_not_injective
    {G X S : Type*} [Group G] [Group S] [MulAction G X]
    [FaithfulSMul G X] [IsPreprimitive G X]
    (f : G →* S) (hf : Function.Surjective f) (hni : ¬ Function.Injective f) (a : X) :
    Function.Surjective (f.domRestrict (stabilizer G a)) := by
  have hk : f.ker ≠ ⊥ := fun h => hni (f.ker_eq_bot_iff.mp h)
  let : IsPretransitive f.ker X := Atlas.GroupTheory.normal_pretransitive f.ker hk
  exact f.surjective_domRestrict_stabilizer_of_pretransitive_ker hf a

end MonoidHom
