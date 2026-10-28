/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/SextetIsometry.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.SextetReflectionGenerators
public import Theory.AtlasPort.OtherSporadic.Conway.MonomialStabilizer
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechSextetVectors
/-!
Explicit sextet and tetrad isometries of the integral Leech lattice.
Coordinate identities and the retained lattice generators certify the isometry operations.

Source: Gerald Höhn, `Atlas/Conway/SextetIsometry.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

theorem sextetReflection_preserves (x : RationalCoordinates) :
    x ∈ rationalLeech ↔ sextetReflection x ∈ rationalLeech := by
  have hf (y : RationalCoordinates) (hy : y ∈ rationalLeech) : sextetReflection y ∈ rationalLeech := by
    obtain ⟨z,hz,rfl⟩ := hy
    exact sextetReflection_lattice z hz
  constructor
  · exact hf x
  · intro hx
    have hh := hf _ hx
    rwa [sextetReflection_involutive] at hh

def sextetRationalIsometry : rationalLatticeIsometries :=
  ⟨sextetReflectionEquiv,sextetReflection_form,sextetReflection_preserves⟩

def zeta : LeechIsometryGroup := restrictionIsometry sextetRationalIsometry

theorem zeta_agrees (x : leech) : rationalEmbedding (zeta.val x).val =
    sextetReflection (rationalEmbedding x.val) := restriction_agrees sextetRationalIsometry x

theorem zeta_sq : zeta * zeta = 1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply Subtype.ext
  apply rationalEmbedding_injective
  change rationalEmbedding (zeta.val (zeta.val x)).val = rationalEmbedding x.val
  rw [zeta_agrees,zeta_agrees,sextetReflection_involutive]

def zetaFirstTetrad : {T // T ∈ distinguishedUnorderedSextet.val} :=
  ⟨tetrad (0,0),Finset.mem_image.mpr ⟨(0,0),Finset.mem_univ _,rfl⟩⟩

def zetaFirstSigns : ParitySigns zetaFirstTetrad.val 1 :=
  ⟨fun i => if i.val.2 = 0 then 0 else 1,by decide⟩

def zetaFirstParameter : SextetVectorParameters distinguishedUnorderedSextet 1 :=
  ⟨zetaFirstTetrad,zetaFirstSigns⟩

theorem zeta_first_axis : zeta.val (coordinateEight ((0,0),0)) =
    sextetLatticeVector distinguishedUnorderedSextet 1 zetaFirstParameter := by
  apply Subtype.ext
  apply rationalEmbedding_injective
  rw [zeta_agrees]
  change sextetReflection (rationalEmbedding (coordinateVector ((0,0),0) 8)) =
    rationalEmbedding (tetradFourVector (tetrad (0,0)) (fun i => if i.val.2 = 0 then 0 else 1))
  decide +kernel

theorem zeta_standardCross : crossAction zeta standardCross =
    sextetCross distinguishedUnorderedSextet 1 := by
  apply Subtype.ext
  change leechModTwoRepresentation zeta (leechReduction (coordinateEight ((0,0),0))) = _
  rw [leechModTwoRepresentation_reduce,zeta_first_axis]
  exact sextetVector_class _ _ zetaFirstParameter (sextetBaseParameter _ _)

theorem zeta_not_monomial : zeta ∉ monomialSubgroup := by
  rintro ⟨m,hm⟩
  have hc : sextetCross distinguishedUnorderedSextet 1 = standardCross := by
    rw [← zeta_standardCross,← hm,monomial_fixes_standardCross]
  have hv : sextetVector distinguishedUnorderedSextet 1 zetaFirstParameter ∈ axisEightVectors := by
    rw [← standardCross_vectors,← hc,sextetCross_vectors]
    exact Finset.mem_image.mpr ⟨zetaFirstParameter,Finset.mem_univ _,rfl⟩
  obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hv
  have hi := congrFun hp ((0,0),0)
  have ht : sextetVector distinguishedUnorderedSextet 1 zetaFirstParameter ((0,0),0) = 4 := by decide
  rw [ht] at hi
  simp only [eightAxisVector,coordinateVector,Pi.single_apply] at hi
  split_ifs at hi <;> norm_num at hi

def generatedConwayGroup : Subgroup LeechIsometryGroup :=
  monomialSubgroup ⊔ Subgroup.closure {zeta}

instance : Finite generatedConwayGroup := inferInstance

structure SextetIsometryConstruction : Prop where
  rational_agrees : ∀ x, rationalEmbedding (zeta.val x).val = sextetReflection (rationalEmbedding x.val)
  involution : zeta * zeta = 1
  outside_monomial : zeta ∉ monomialSubgroup
  standard_cross_image : crossAction zeta standardCross = sextetCross distinguishedUnorderedSextet 1
  finite_generated : Finite generatedConwayGroup

theorem sextet_isometry_constructed : SextetIsometryConstruction where
  rational_agrees := zeta_agrees
  involution := zeta_sq
  outside_monomial := zeta_not_monomial
  standard_cross_image := zeta_standardCross
  finite_generated := inferInstance

end Atlas.Conway
