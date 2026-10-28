module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.BinaryBranch.SourceClassification
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.AtlasPort.OtherSporadic.GroupTheory.CenterSimpleQuotient
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Theory.GroupTheory.CComponent.SimpleNormalCentralizer

/-!
# The actual binary simple socle lies in the offender image

The source offender image is a nontrivial normal subgroup of the literal
automorphism group. The inner subgroup is nonabelian simple and has trivial
centralizer, so the normal-subgroup dichotomy puts it inside that image.
This supplies the missing actor containment before comparing B.5.6 modules;
it does not identify the offender group with the whole automorphism group.

Source: Aschbacher–Smith, proof of 15.4.20, printed p.1164.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch.SourceClassification
variable {G : Type*} [Group G] [Finite G]
  {d : Source.Geometry G} {i j : Bool} {H U K : Subgroup G}

/-- Both binary branches contain the same literal inner PSL subgroup in their offender image. -/
theorem inner_le_sourceImage (h : Input d i j H U K) {n : ℕ}
    (hn : n = 4 ∨ n = 5)
    (e : (H ⧸ pCore 2 H) ≃* MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))) :
    MulAut.innerSubgroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)) ≤
      (sourceGroup h).map e.toMonoidHom := by
  let P := Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)
  have hn3 : 3 ≤ n := by rcases hn with rfl | rfl <;> decide
  let : IsSimpleGroup P := Atlas.psl_simple_high_rank n hn3
  let : Group.IsPerfect P := Atlas.psl_perfect n hn3
  have hc : center P = ⊥ := Atlas.GroupTheory.center_eq_bot_of_simple_nonabelian P
    (Group.IsPerfect.not_isMulCommutative P)
  let f : P ≃* MulAut.innerSubgroup P :=
    MonoidHom.ofInjective (MulAut.conj_injective_of_center_eq_bot hc)
  let : IsSimpleGroup (MulAut.innerSubgroup P) := f.symm.isSimpleGroup
  let : Group.IsPerfect (MulAut.innerSubgroup P) :=
    Group.IsPerfect.ofSurjective (f := f.toMonoidHom) f.surjective
  have hnonab : ¬ IsMulCommutative (MulAut.innerSubgroup P) := by
    exact Group.IsPerfect.not_isMulCommutative _
  let := sourceImage_normal h e
  exact simple_normal_le_of_normal_ne_bot_of_centralizer_eq_bot
    (MulAut.innerSubgroup P) hnonab (MulAut.centralizer_innerSubgroup_eq_bot hc)
    ((sourceGroup h).map e.toMonoidHom) (sourceImage_ne_bot h e)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.BinaryBranch.SourceClassification
