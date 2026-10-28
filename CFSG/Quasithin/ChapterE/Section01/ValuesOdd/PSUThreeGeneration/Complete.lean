module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.CentralizerStructure
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerAction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.Consumer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianReselection.Application
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicPlacement.Application
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.InnerFamilies.Geometry.SemidihedralTorus.ActorCoordinates.StandardFixer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.CentralizerContainment
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.Geometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
/-!
# Complete odd-prime unitary rank-one E-generation

The simple-socle E₂ construction handles small actors. For a large family
with an inner actor, the proved residual-component calculation traps an
inner-involution centralizer and the unitary geometry contradicts it.
Outer four-actors use the proved centralizer action, whole-actor reselection,
standard-four fixer and cyclic placement. Outer eight-actors use the actual
centralizer quotient, including its marked symmetric-five small-prime case.
Thus all local inputs of the original family reduction are discharged.

The original SQTK two-extension, arbitrary Hermitian model, local tau,
radical quotients and actual family members are retained throughout.
Source: Aschbacher–Smith E.1.14(7), p.214, citing Aschbacher (1982), Lemma 4.11.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
open OuterFamilies FourActors.CentralizerGeometry.InvertedOddSubgroup
variable {G:Type*} [Group G] [Finite G]

/-- The actual odd-prime unitary two-extension is rank-one E-generated. -/
theorem isEGenerated_one_of_model {κ:GroupClass} (hG:IsSQTK κ G)
    [IsSimpleGroup (generalizedFitting G)] (T:Sylow 2 G)
    (hLT:generalizedFitting G⊔(T:Subgroup G)=⊤)
    {p:ℕ} (hp:p.Prime) (ho:Odd p)
    (hm:ClassicalGroup.IsPSU (generalizedFitting G) 3 p) : IsEGenerated 1 G := by
  apply isEGenerated_of_model_and_local_cases T hp ho hm
  · intro hn A _ _ hne
    exact ValuesEvenClassical.RankOneUpper.eCaseComponent_top hn T hLT (T:Subgroup G) A hne
  · intro d hi
    obtain ⟨z,hz,hzL,hzT,hTz,hCM⟩:=exists_inner_centralizer_le (generalizedFitting G) hLT hp ho hm d hi
    exact InnerGeometry.false_of_centralizer_le hG hLT hp ho hm d hi hz hzL hzT hTz hCM
  · intro d hout
    apply no_large_obstruction_of_outer_actor_cases hp ho hm hLT d hout
    · intro A hA _ _ hfour hinter
      obtain ⟨B,hB,hBT,_,hfourB,hinterB,z,hz,hzL,hzB,hTz⟩:=
        FourActors.exists_positioned_four_actor (generalizedFitting G) hp ho hm d hA hfour hinter
      have hCM:=FourActors.positioned_four_centralizer_le hG hLT hp ho hm d hB hBT hfourB hinterB z hz hzL hzB hTz
      apply false_of_positioned_coordinates hp ho hm hLT d hB hzL hTz hCM
      · exact InnerGeometry.ambient_centralizer_isCoatom_of_matrix_geometry hp ho
          (generalizedFitting G) hm z hzL hz
      · intro hmod
        exact InnerGeometry.WreathedNormalizer.exists_solvable_sylow_overgroup
          (generalizedFitting G) hLT hp ho hmod hm hz hzL (hBT hzB) hTz
      · intro hmod
        let : IsElementaryAbelian 2 B:=d.elementary.1 B hB
        have hBout:¬B≤generalizedFitting G := by
          intro h
          rw [inf_eq_left.mpr h,hfourB] at hinterB
          omega
        apply exists_positioned_inverted_coordinates_of_abelian_geometry hp ho hmod hm
          B hBT hfourB hBout hzL hz hzB hTz
        intro F _ _ J hsimple hcard hc hJ
        let := hsimple
        apply abelianOuterCoordinateGeometry_of_standardFixerCoordinates J hp ho hmod hcard hc hJ
        obtain ⟨_,_,ep,_,_,_⟩:=BenderSuzuki.MatrixGroups.HermitianForm.IdentityGram.exists_identityGram_transport J p hp hcard hc
        let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup
            (BenderSuzuki.MatrixGroups.HermitianForm.IdentityGram.identityGram J)):=ep.symm.isSimpleGroup
        exact InnerGeometry.SemidihedralTorus.standardFixerCoordinates _ rfl hp ho hmod hcard hc
    · intro A hA hAT hne hcard hinter
      obtain ⟨z,hz,hzL,_,hTz,hall⟩:=EightActors.exists_common_central_involution hp ho hm d hinter
      have hzA:=hall A hA hAT hcard
      have hCM:=EightActors.centralizer_le_of_eight_actor hG hLT hp ho hm d hout hA hAT hne hcard hinter hz hzL hzA hTz
      exact EightActors.false_of_trapped_centralizer hG hp ho hm hLT d hout hA hAT hne hcard hinter hz hzL hzA hTz hCM
end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
