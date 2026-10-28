module
public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal
public import Theory.GroupTheory.SolvableNormalAbelian
public import Theory.GroupAction.RegularNormal

/-!
# Characteristic regular subgroups of solvable primitive groups

The last nontrivial derived subgroup is characteristic and abelian. In a
faithful primitive action it is transitive, and commutativity makes point
stabilizers trivial. A regular abelian subgroup is its own centralizer:
compare an arbitrary centralizing permutation with the unique translation
having the same value at one point.

The small unitary three-core is the consumer. Source: the solvable primitive
permutation-group argument, as used for the 3-closed groups U₃(2), SU₃(2)
in DGS, Groups and Graphs (1985), p.104 and 6.1, pp.118--119.
-/

public noncomputable section
open Subgroup MulAction
open scoped IsMulCommutative
namespace MulAction
variable {G X : Type*} [Group G] [MulAction G X] [FaithfulSMul G X]

/-- In a faithful primitive action, a nontrivial abelian normal subgroup is regular. -/
theorem abelian_normal_regular [IsPreprimitive G X]
    (A : Subgroup G) [A.Normal] [IsMulCommutative A] (hA : A ≠ ⊥) :
    ∀ x y : X, ∃! a : A, (a : G) • x = y := by
  let : IsPretransitive A X := Atlas.GroupTheory.normal_pretransitive A hA
  have hfree (a : A) (x : X) (hax : (a : G) • x = x) : a = 1 := by
    apply Subtype.ext
    apply eq_of_smul_eq_smul (α := X)
    intro y
    obtain ⟨b,hb⟩ := exists_smul_eq A x y
    rw [← hb]
    change (a : G) • ((b : G) • x) = (1 : G) • ((b : G) • x)
    have hc : (a : G)*(b : G) = (b : G)*(a : G) := congrArg Subtype.val (mul_comm a b)
    rw [← mul_smul,hc,mul_smul,hax,one_smul]
  intro x y
  obtain ⟨a,ha⟩ := exists_smul_eq A x y
  refine ⟨a,ha,?_⟩
  intro b hb
  apply inv_mul_eq_one.mp
  apply hfree _ x
  change ((b : G)⁻¹*(a : G)) • x = x
  rw [mul_smul]
  change (a : G) • x = y at ha
  rw [ha,←hb,inv_smul_smul]

/-- A regular abelian subgroup is its own centralizer in a faithful action. -/
theorem centralizer_eq_of_abelian_regular (A : Subgroup G) [IsMulCommutative A]
    (o : X) (hreg : ∀ x y : X, ∃! a : A, (a : G) • x = y) :
    centralizer (A : Set G) = A := by
  apply le_antisymm
  · intro g hg
    obtain ⟨a,ha,_⟩ := hreg o (g • o)
    have he : g = (a : G) := by
      apply eq_of_smul_eq_smul (α := X)
      intro y
      obtain ⟨b,hb,_⟩ := hreg o y
      rw [←hb,←mul_smul,←mul_smul]
      have hc : (a : G)*(b : G) = (b : G)*(a : G) := congrArg Subtype.val (mul_comm a b)
      rw [←hg b b.property,hc,mul_smul,mul_smul,ha]
    exact he ▸ a.property
  · exact le_centralizer_iff_isMulCommutative.mpr inferInstance

/-- A nontrivial faithful primitive solvable action has a characteristic regular abelian subgroup. -/
theorem exists_characteristic_abelian_regular [IsPreprimitive G X]
    [Group.IsSolvable G] [Nontrivial X] (o : X) :
    ∃ A : Subgroup G, A.Characteristic ∧ IsMulCommutative A ∧ A ≠ ⊥ ∧
      (∀ x y : X, ∃! a : A, (a : G) • x = y) ∧ centralizer (A : Set G) = A := by
  let : Nontrivial G := by
    obtain ⟨x,hx⟩ := exists_ne o
    obtain ⟨g,hg⟩ := exists_smul_eq G o x
    exact ⟨⟨g,1,fun he => hx (by simpa only [he,one_smul] using hg.symm)⟩⟩
  obtain ⟨A,hAc,hAb,hA⟩ := Group.exists_nontrivial_abelian_characteristic G
  let := hAc
  let := hAb
  have hr := abelian_normal_regular (X := X) A hA
  exact ⟨A,hAc,hAb,hA,hr,centralizer_eq_of_abelian_regular A o hr⟩
end MulAction
