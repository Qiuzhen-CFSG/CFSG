module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointResidualRestriction

/-!
# Lifting the natural point index through a two-group kernel

A surjection sends a Sylow two-subgroup to a Sylow subgroup of its image.
If its kernel is a two-group, the kernel lies in that original Sylow subgroup,
so the two indices agree. Thus a natural point image gives index three in
the original point group as well.
Source: the ordinary recovery in Aschbacher–Smith13.3.9, printed p.887.
-/

public section
open Subgroup BinaryPermutation Representation.BinaryOffender
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags

theorem point_hom_sylow_index_three {H:Type*} [Group H] [Finite H]
    (f:H→*S) (I:Subgroup S) (hI:alternatingGroup (Fin 6)≤I)
    (P:Submodule (ZMod 2) NaturalGeometry.V) (hP:Module.finrank (ZMod 2) P=1)
    (hf:f.range=I⊓subspaceStabilizer (naturalRepresentation (Fin 6)) P)
    (hk:IsPGroup 2 f.ker) (T:Sylow 2 H) : (T:Subgroup H).index=3 := by
  let T':=T.mapSurjective f.rangeRestrict_surjective
  have hi:(T':Subgroup f.range).index=3 := by
    have hh:=point_sylow_index_three I hI P hP
    rw [←hf] at hh
    exact hh T'
  have hker:f.rangeRestrict.ker=f.ker := by
    ext x
    exact Subtype.ext_iff
  have hk':IsPGroup 2 f.rangeRestrict.ker := hker.symm ▸ hk
  change ((T:Subgroup H).map f.rangeRestrict).index=3 at hi
  rwa [index_map_eq _ f.rangeRestrict_surjective (hk'.le_sylow_of_normal T)] at hi
end Theory.SpecificGroups.SymmetricSix.BinaryFlags

