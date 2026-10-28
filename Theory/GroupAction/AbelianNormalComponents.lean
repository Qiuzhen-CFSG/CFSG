module

public import Theory.GroupTheory.GeneralizedFitting.SolvableNormalKernel
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal

/-!
# Abelian normal subgroups exclude components in primitive actions

An abelian transitive subgroup of a faithful permutation group is
self-centralizing. To see this, choose an element of that subgroup that
agrees with a given centralizing permutation at one point. Commutation
and transitivity imply agreement at every point, and faithfulness gives
equality. In a primitive action a nontrivial normal subgroup is transitive.
If it is abelian, the solvable-normal-subgroup component dichotomy therefore
excludes every component.

This supplies the component exclusion for primitive affine permutation
groups used in Aschbacher–Smith, B.1.13, printed p.74. The normal-orbit
criterion is the existing `Atlas.GroupTheory.normal_pretransitive`; the
component dichotomy is GLS, volume 2, Theorem 3.5.
-/

public section
open Subgroup MulAction
namespace Theory.GroupTheory

/-- A transitive abelian subgroup contains its full centralizer in a faithful
permutation group. Normality and finiteness are not needed for this step. -/
theorem centralizer_le_of_abelian_pretransitive
    {G Ω : Type*} [Group G] [MulAction G Ω] [FaithfulSMul G Ω]
    [Nonempty Ω] (A : Subgroup G) [IsMulCommutative A] [IsPretransitive A Ω] :
    centralizer (A : Set G) ≤ A := by
  intro g hg
  obtain ⟨x⟩ := ‹Nonempty Ω›
  obtain ⟨a, ha⟩ := exists_smul_eq A x (g • x)
  have he : g = (a : G) := by
    apply eq_of_smul_eq_smul (α := Ω)
    intro y
    obtain ⟨b, rfl⟩ := exists_smul_eq A x y
    have hgb : (b : G) * g = g * b := mem_centralizer_iff.mp hg b b.property
    have hab : (a : G) * b = (b : G) * a := congrArg Subtype.val (mul_comm' a b)
    change g • ((b : G) • x) = (a : G) • ((b : G) • x)
    rw [← mul_smul, ← hgb, mul_smul, ← ha]
    change (b : G) • ((a : G) • x) = (a : G) • ((b : G) • x)
    rw [← mul_smul, ← hab, mul_smul]
  exact he ▸ a.property

/-- A faithful finite primitive group with a nontrivial abelian normal
subgroup has no quasisimple subnormal subgroup. -/
theorem not_isComponent_of_abelian_normal_primitive
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [FaithfulSMul G Ω]
    [Nonempty Ω] [IsPreprimitive G Ω] (A : Subgroup G) [A.Normal]
    [IsMulCommutative A] (hA : A ≠ ⊥) (D : Subgroup G) : ¬ IsComponent G D := by
  let : IsPretransitive A Ω := Atlas.GroupTheory.normal_pretransitive A hA
  let : CommGroup A := IsMulCommutative.instCommGroup
  exact not_isComponent_of_solvable_normal_selfCentralizing A
    (centralizer_le_of_abelian_pretransitive (Ω := Ω) A) D

end Theory.GroupTheory
