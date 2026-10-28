module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.SixDimensional.Models
public import Theory.Representation.ElementaryAbelianAction
public import Theory.Representation.BinaryTransvectionGroups.MarkedPair

/-!
# Coordinates for the marked transvection case

We linearize the actual conjugation homomorphism of M on V. The image is
faithful, and its kernel in M is the relative centralizer C_M(V). Subspaces
are obtained from the actual ambient subgroups, so normality of Q in M
implies invariance of its subspace, and a disjoint ambient decomposition
gives the required disjointness of Q and the marked plane.

These are coordinate transports for the proof of Lemma 16.4.7,
Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1187.
No transvection existence, two-core bound, or recognition is assumed here.
-/

@[expose] public section

open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.TransvectionCase
open Subgroup BinaryLinear BinaryTransvectionGroups
variable {G : Type*} [Group G]

abbrev Space (L : Subgroup G) (r z : G) := Additive (shadowSpace L r z)

variable (L : Subgroup G) (g r z : G) [IsElementaryAbelian 2 (shadowSpace L r z)]

/-- The linear automorphism is obtained from the published conjugation action. -/
noncomputable def linearAction : shadowOvergroup L g r z →* BinaryLinear.GL (Space L r z) where
  toFun m := (shadowAction L g r z m).toAdditive.toLinearEquiv
    (fun c v => ZMod.map_smul _ c v)
  map_one' := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun f : MulAut (shadowSpace L r z) => Additive.ofMul (f v.toMul))
      (map_one (shadowAction L g r z))
  map_mul' m n := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun f : MulAut (shadowSpace L r z) => Additive.ofMul (f v.toMul))
      (map_mul (shadowAction L g r z) m n)

theorem linearAction_apply (m : shadowOvergroup L g r z) (v : Space L r z) :
    ((linearAction L g r z m v).toMul : G) = m * v.toMul * (m : G)⁻¹ := rfl

/-- The faithful linear image of the actual action. -/
noncomputable abbrev image : Subgroup (BinaryLinear.GL (Space L r z)) := (linearAction L g r z).range

theorem linearAction_ker : (linearAction L g r z).ker =
    (centralizer (shadowSpace L r z : Set G)).subgroupOf (shadowOvergroup L g r z) := by
  rw [← shadowAction_ker]
  ext m
  change linearAction L g r z m = 1 ↔ shadowAction L g r z m = 1
  constructor
  · intro h
    apply MulEquiv.ext
    intro v
    exact congrArg (fun f : BinaryLinear.GL (Space L r z) => (f (Additive.ofMul v)).toMul) h
  · intro h
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun f : MulAut (shadowSpace L r z) => Additive.ofMul (f v.toMul)) h

/-- Subspaces keep their original ambient membership. -/
noncomputable def subspace (A : Subgroup G) : Submodule (ZMod 2) (Space L r z) :=
  AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup (A.subgroupOf (shadowSpace L r z)))

theorem mem_subspace (A : Subgroup G) (v : Space L r z) :
    v ∈ subspace L r z A ↔ (v.toMul : G) ∈ A := Iff.rfl

def rVector : Space L r z := Additive.ofMul
  ⟨r, (show zpowers r ≤ shadowSpace L r z from le_sup_left.trans le_sup_right)
    (mem_zpowers r)⟩

def zVector : Space L r z := Additive.ofMul
  ⟨z, (show zpowers z ≤ shadowSpace L r z from le_sup_right.trans le_sup_right)
    (mem_zpowers z)⟩

/-- Relative normality, rather than ambient normality, suffices. -/
theorem image_le_parabolic (A : Subgroup G)
    (hA : shadowOvergroup L g r z ≤ normalizer (A : Set G)) :
    image L g r z ≤ parabolic (subspace L r z A) := by
  rintro a ⟨m, rfl⟩ v
  change (m : G) * (v.toMul : G) * (m : G)⁻¹ ∈ A ↔ (v.toMul : G) ∈ A
  exact (mem_normalizer_iff.mp (hA m.property) _).symm

theorem marked_plane_le_subspace :
    centerLine (rVector L r z) ⊔ centerLine (zVector L r z) ≤
      subspace L r z (zpowers r ⊔ zpowers z) := by
  apply sup_le <;> apply Submodule.span_le.mpr
  · rintro v (rfl : v = rVector L r z)
    exact mem_sup_left (mem_zpowers r)
  · rintro v (rfl : v = zVector L r z)
    exact mem_sup_right (mem_zpowers z)

/-- The centerless direct-product decomposition supplies exactly the
disjointness needed in reduced commutation. -/
theorem core_disjoint_marked_plane
    (hdis : Disjoint (residualCore L r) (zpowers r ⊔ zpowers z)) :
    Disjoint (subspace L r z (residualCore L r))
      (centerLine (rVector L r z) ⊔ centerLine (zVector L r z)) := by
  apply Submodule.disjoint_def.mpr
  intro v hvQ hvE
  apply Additive.toMul.injective
  apply Subtype.ext
  exact Subgroup.disjoint_def.mp hdis hvQ (marked_plane_le_subspace L r z hvE)

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow.SixDimensional.TransvectionCase
