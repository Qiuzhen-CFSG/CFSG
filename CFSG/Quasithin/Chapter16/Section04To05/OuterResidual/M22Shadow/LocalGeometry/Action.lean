module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.LocalGeometry.Space
public import Theory.Representation.ElementaryAbelianAction

/-!
# Linearizing the ambient shadow action

The canonical binary vector space on the elementary group V carries the
linearization of the published ambient conjugation action. The evaluation
equation and kernel equality retain the actual embeddings in G.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of Lemma 16.4.7, printed pp.1186–1187.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow
variable {G : Type*} [Group G]

noncomputable def shadowRepresentation (L : Subgroup G) (g r z : G)
    [IsElementaryAbelian 2 (shadowSpace L r z)] :
    Representation (ZMod 2) (shadowOvergroup L g r z) (Additive (shadowSpace L r z)) where
  toFun m := (shadowAction L g r z m).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change shadowAction L g r z 1 v.toMul = v.toMul
    simp
  map_mul' m n := by
    apply LinearMap.ext
    intro v
    change shadowAction L g r z (m * n) v.toMul =
      shadowAction L g r z m (shadowAction L g r z n v.toMul)
    rw [map_mul]
    rfl

theorem shadowRepresentation_apply (L : Subgroup G) (g r z : G)
    [IsElementaryAbelian 2 (shadowSpace L r z)]
    (m : shadowOvergroup L g r z) (v : Additive (shadowSpace L r z)) :
    ((shadowRepresentation L g r z m v).toMul : G) = m * v.toMul * (m : G)⁻¹ := rfl

theorem shadowRepresentation_ker (L : Subgroup G) (g r z : G)
    [IsElementaryAbelian 2 (shadowSpace L r z)] :
    (shadowRepresentation L g r z).ker =
      (centralizer (shadowSpace L r z : Set G)).subgroupOf (shadowOvergroup L g r z) := by
  rw [← shadowAction_ker]
  ext m
  change shadowRepresentation L g r z m = 1 ↔ shadowAction L g r z m = 1
  constructor
  · intro hh
    apply MulEquiv.ext
    intro v
    exact congrArg (fun f : Module.End (ZMod 2) (Additive (shadowSpace L r z)) =>
      (f (Additive.ofMul v)).toMul) hh
  · intro hh
    apply LinearMap.ext
    intro v
    change shadowAction L g r z m v.toMul = v.toMul
    rw [hh]
    rfl

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow
