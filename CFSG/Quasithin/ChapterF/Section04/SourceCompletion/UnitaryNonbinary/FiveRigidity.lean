module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveRootDefect
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FiveRootCoordinates
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FiveRootGeneration
public import CFSG.Quasithin.Chapter5.Section03UnitaryNativeLift.Geometry
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.Marking.Borel.Left

/-!
# Elimination of the full PSU₅(4) completion defect

The native Cartan fixes both simple roots pointwise. For the Hermitian
root this includes elimination of its central shear, using the genuine
field-sixteen Heisenberg law. These roots and the marked reflections
recover the whole plane parabolic. Maximality of the flag in the point
parabolic and native parabolic generation then determine the automorphism.
Thus the actual fourth rotation-power defect vanishes in every faithful
whole-overlap completion satisfying the full-extension order bound.

The SU₅ projective scalar kernel of order five is retained throughout.
Source: Aschbacher–Smith F.4.10,16–17,24, pp.279,282–283,287.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FiveWeyl
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.UnitaryFive
open SmallCompletion.FiveRoots SmallCompletion.FivePaths
variable (U : GreenBook.UnitaryFive.Model 4)
variable (t : U.F) (ht : t + U.form.conj t = 1)

def SimpleRootsFixed (a : MulAut U.Carrier) : Prop :=
  (∀ x : U.F, a (project U.form (linearRoot U.form t ht U.matrix x))=
    project U.form (linearRoot U.form t ht U.matrix x)) ∧
  (∀ x z : U.F, ∀ hz : z+U.form.conj z=x*U.form.conj x,
    a (project U.form (hermitianRoot U.form U.matrix x z hz))=
      project U.form (hermitianRoot U.form U.matrix x z hz))

/-- The scalar on the linear root and the scalar and shear on the Hermitian
root all vanish under the proved Cartan-fixed involution constraints. -/
theorem constraints_fix_simpleRoots (a : MulAut U.Carrier)
    (ha : SourceExtension.CartanFixedInvolution (point U t ht) (plane U t ht)
      (diagonalCartan U t) a) : SimpleRootsFixed U t ht a := by
  obtain ⟨hl,hh⟩ := constraints_preserve_simpleRoots U t ht a ha
  have hD : ∀ g, SmallCompletion.FiveDiagonal.IsDiagonal U.form t g →
      a (project U.form g)=project U.form g := fun g hg => ha.fixes_cartan _ ⟨g,hg,rfl⟩
  exact ⟨SmallCompletion.FiveRootCoordinates.fixes_linearRoot U.form t ht U.matrix a ha.square hD hl,
    SmallCompletion.FiveRootCoordinates.fixes_hermitianRoot U.form t ht U.matrix U.card
      (fixed_card_four U.form U.card U.conjugation) a ha.square hD hh⟩

/-- Roots, Cartan and Weyl elements determine the native projective automorphism. -/
theorem aut_eq_one_of_generators (a : MulAut U.Carrier)
    (hroot : SimpleRootsFixed U t ht a)
    (hs : a (point U t ht).val=(point U t ht).val)
    (hp : a (plane U t ht).val=(plane U t ht).val)
    (hD : ∀ g, SmallCompletion.FiveDiagonal.IsDiagonal U.form t g →
      a (project U.form g)=project U.form g) : a=1 := by
  let N : Subgroup U.Carrier := a.toMonoidHom.eqLocus (MonoidHom.id U.Carrier)
  let S := N.comap (project U.form)
  have hS : specialStabilizer U.form (Theory.SpecificGroups.UnitaryFive.plane U.F)≤S :=
    SmallCompletion.FiveRootGeneration.plane_le U.form t ht U.matrix S hroot.1 hroot.2 hs hp hD
  have hP : U.rightParabolic≤N := by
    rintro b ⟨g,hg,rfl⟩
    exact hS hg
  have hB : U.overlap≤N := inf_le_right.trans hP
  have hL : U.leftParabolic≤N := by
    have hb : U.overlap.subgroupOf U.leftParabolic≤N.subgroupOf U.leftParabolic := fun _ hx => hB hx
    have hn : N.subgroupOf U.leftParabolic≠U.overlap.subgroupOf U.leftParabolic := by
      intro he
      have hh : point U t ht ∈ N.subgroupOf U.leftParabolic := hs
      rw [he] at hh
      exact Chapter5.UnitaryNativeLift.Five.point_out U t ht hh.2
    exact Subgroup.subgroupOf_eq_top.mp
      ((U.overlap_leftParabolic_isCoatom.ne_iff_eq_top hb).mp hn)
  have hN : N=⊤ := top_unique ((Chapter5.UnitaryNativeLift.Five.parabolics_generate U) ▸ sup_le hL hP)
  apply DFunLike.ext
  intro b
  exact (show b∈N from hN ▸ mem_top b)

/-- The actual full-middle defect is the identity automorphism. -/
theorem constraints_eq_one (a : MulAut U.Carrier)
    (ha : SourceExtension.CartanFixedInvolution (point U t ht) (plane U t ht)
      (diagonalCartan U t) a) : a=1 :=
  aut_eq_one_of_generators U t ht a (constraints_fix_simpleRoots U t ht a ha)
    ha.fixes_point ha.fixes_plane (fun g hg => ha.fixes_cartan _ ⟨g,hg,rfl⟩)

/-- The canonical marked Weyl relation holds even for arbitrary outer degree. -/
theorem rotation_fourth_eq_one (E : FiveExtension U)
    {M : Type*} [Group M] [Finite M]
    (c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := M))
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) : rotation U t ht E c ^ 4=1 := by
  obtain ⟨a,ha,hfix⟩ := fourth_defect U t ht E c ho hcard
  have he : a=1 := Subtype.ext (constraints_eq_one U t ht a.val hfix)
  rw [←ha,he,map_one]
end CFSG.Quasithin.ChapterF.SourceCompletion.UnitaryNonbinary.FiveWeyl
