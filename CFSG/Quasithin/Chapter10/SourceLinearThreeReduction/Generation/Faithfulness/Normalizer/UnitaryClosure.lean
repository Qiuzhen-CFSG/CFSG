module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.UnitaryLocal
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.BinaryClosure
public import Theory.SpecificGroups.ClassicalUnitary.FourSylowStructure.Transport
public import CFSG.Quasithin.ChapterI.Section03.SylowAutomorphisms
public import Theory.GroupTheory.SylowOuterSolvability

/-!
# Discharging the outer action in the large unitary-four branch

The actual Sylow two-group of PSU₄(2ⁿ), n > 1, has soluble automorphism
group. The pointwise Sylow fixer then proves soluble outer automorphisms.
This makes the original perfect fixed residual act innerly on the normal
component; covering uniqueness places it there, and the local rank bound
excludes the model. The actual Hall application is in HallInspection.

Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622.
The earlier covering-uniqueness premise remains with this task.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04

/-- Intrinsic Sylow restriction proves soluble outer automorphisms for
binary unitary-four groups of fixed-field order at least four. -/
theorem source_unitary_four_outer_solvable
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    {n : ℕ} (hn : 1 < n) (hm : ClassicalGroup.IsPSU S 4 (2 ^ n)) :
    Group.IsSolvable (MulAut.Outer S) := by
  obtain ⟨F,_,_,J,hcard,hconj,⟨e⟩⟩ := hm
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv S e.toEquiv
  let P : Sylow 2 S := Classical.choice inferInstance
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let j : P ≃* Q := P.equivMapOfInjective e.toMonoidHom e.injective
  let : Group.IsSolvable (MulAut Q) :=
    FourSylowStructure.projective_sylow_mulAut_isSolvable F J hn hcard hconj Q
  let : Group.IsSolvable (MulAut P) := Group.isSolvable_of_surjective
    (f := (MulAut.congr j.symm).toMonoidHom) (MulAut.congr j.symm).surjective
  let : Group.IsSolvable (fixingSubgroup (MulAut S) (P : Set S)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  exact MulAut.outer_isSolvable_of_sylow_aut P

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
  (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
  (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
  (hu : UniqueMaximalOvergroup
    ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
      ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal)
  (K : Subgroup (normalizer (B : Set G)))
  (hK : IsComponent (normalizer (B : Set G)) K) [K.Normal]
  (hout : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
include D hn hBC hodd hBV hu hK hout

/-- The original normal component cannot be PSU₄(2ⁿ), n > 1.
Both its outer action and the local rank obstruction are discharged. -/
theorem source_nonnormal_oddNormalizer_no_large_unitary_four_component
    {n : ℕ} (hn' : 1 < n)
    (hm : ClassicalGroup.IsPSU (K ⧸ center K) 4 (2 ^ n)) : False := by
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Group.IsSolvable (MulAut.Outer (K ⧸ center K)) :=
    source_unitary_four_outer_solvable hn' hm
  let : Group.IsSolvable (MulAut.Outer K) := Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (K ⧸ center K)))
  have hYK : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ≤
      normalizer (K : Set (normalizer (B : Set G))) :=
    le_trans le_top le_normalizer_of_normal
  have hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ normalizer (K : Set (normalizer (B : Set G))) :=
    le_trans le_top le_normalizer_of_normal
  have hplaced := (source_nonnormal_oddNormalizer_component_closure_of_overlap_normalizes
    D hn B hBC hodd hBV hu K hK hout hYK
      (source_oddNormalizer_component_inner B K hK hFK)).2.2.2
  exact source_nonnormal_oddNormalizer_no_placed_unitary_four_component
    D hn B hBC hodd hBV K hplaced (by omega) hm

end CFSG.Quasithin.Chapter10
