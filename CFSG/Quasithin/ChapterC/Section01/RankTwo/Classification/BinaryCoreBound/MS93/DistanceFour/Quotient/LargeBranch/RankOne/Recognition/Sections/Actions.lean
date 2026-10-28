module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.Quotients
public import Theory.Representation.SubspaceQuotient

/-!
# The actual local actions on the two linear sections

Subgroups of the original finite local group act through the supplied
projection and the original amalgam embedding. Normalization of a subgroup
and its denominator gives representations on its literal linear quotient,
with the ambient conjugation formula for both quotient maps.

These constructions retain arbitrary local actors so they can be applied
to the source-ordered parabolic residual without replacing it by the full
rank-one actor. The normalizations and the natural-module recognition
remain mathematical obligations of the source assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12)(1)--(2), printed p.910.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.LayerModule
variable {M : Type*} [Group M] {L R : Subgroup M} {source : LocalSource L R}
  {S : Subgroup (FreeAmalgam R)} (d : LayerModule source S)
  (A : Subgroup M) (T N : Subgroup (FreeAmalgam R))
  (hS : A.map (embedM R) ≤ normalizer S)
  (hT : A.map (embedM R) ≤ normalizer T)
  (hN : A.map (embedM R) ≤ normalizer N)

/-- Restrict to an actual local actor and a subgroup image it preserves. -/
noncomputable def invariantSubspace :
    Subrepresentation (d.representation.comp (source.projection.comp A.subtype)) where
  toSubmodule := d.subspace T
  apply_mem_toSubmodule a _ hv :=
    d.subspace_invariant_of_mem T a
      (hS (mem_map_of_mem _ a.property)) (hT (mem_map_of_mem _ a.property)) _ hv

/-- The action on the first quotient, with the original local actor retained. -/
noncomputable def quotientRepresentation :
    Representation (ZMod 2) A (d.Space ⧸ d.subspace T) :=
  (d.invariantSubspace A T hS hT).quotientRepresentation

/-- The first quotient action is exactly the ambient conjugation action. -/
theorem quotientMap_action (a : A) (x y : S)
    (hy : (y : FreeAmalgam R) = embedM R a * (x : FreeAmalgam R) * (embedM R a)⁻¹) :
    (d.quotientMap T y).toAdd =
      d.quotientRepresentation A T hS hT a (d.quotientMap T x).toAdd := by
  change (d.subspace T).mkQ (d.projection y).toAdd =
    (d.subspace T).mkQ (d.representation (source.projection a) (d.projection x).toAdd)
  rw [d.action a x y hy]

/-- The denominator for the action on the second section, with its exact inclusion. -/
noncomputable def invariantSection :
    Subrepresentation (d.invariantSubspace A T hS hT).toRepresentation where
  toSubmodule := (d.subspace N).comap (d.subspace T).subtype
  apply_mem_toSubmodule a _ hv :=
    d.subspace_invariant_of_mem N a
      (hS (mem_map_of_mem _ a.property)) (hN (mem_map_of_mem _ a.property)) _ hv

/-- The action on the literal quotient (T/Z_alpha)/(N/Z_alpha). -/
noncomputable def sectionRepresentation :
    Representation (ZMod 2) A ((d.subspace T) ⧸
      (d.subspace N).comap (d.subspace T).subtype) :=
  (d.invariantSection A T N hS hT hN).quotientRepresentation

/-- The second section action also has the original ambient conjugation formula. -/
theorem sectionMap_action (hTS : T ≤ S) (a : A) (x y : T)
    (hy : (y : FreeAmalgam R) = embedM R a * (x : FreeAmalgam R) * (embedM R a)⁻¹) :
    (d.sectionMap T N hTS y).toAdd =
      d.sectionRepresentation A T N hS hT hN a (d.sectionMap T N hTS x).toAdd := by
  change ((d.subspace N).comap (d.subspace T).subtype).mkQ
      (d.subspaceMap T hTS y).toAdd =
    ((d.subspace N).comap (d.subspace T).subtype).mkQ
      ((d.invariantSubspace A T hS hT).toRepresentation a (d.subspaceMap T hTS x).toAdd)
  congr 1
  apply Subtype.ext
  exact d.action a (inclusion hTS x) (inclusion hTS y) hy

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.LayerModule
