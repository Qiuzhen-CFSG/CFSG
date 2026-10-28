module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio.Models
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings.SLThree
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.CoverModels.Models
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Exchanged.BorelMarkings.RankOne
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings.SpFour

/-!
# Literal Borel normalizers for the five normal source models

The E.2 marking itself recognizes the simple group and the exact source
Borel. The concrete root Sylows show that this Borel is their normalizer in
all five families. In the unitary case the root Sylow is first projected
from SU₃; the matrix root and torus ranges are retained throughout.

These group calculations supply the actual Borel marking for the natural
module fixed-space argument in Aschbacher–Smith 15.3.65, printed p.1152.
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
open RepresentationReduction.SourceRestrictions
open Cases.Single.SmallRatio Cases.Exchanged.BorelMarkings
open FFExclusions.ModelRigidity ChapterF.Source.Unitary
variable {X : Type*} [Group X] [Finite X] {M K T : Subgroup X} {f : ℕ}

omit [Finite X] in
/-- The source marking retains the actual defining exponent in all five
normal even-family models. -/
theorem source_model_of_normal_cases
    (hm : BenderModel M K f ∨ DiagramModel M K T f) :
    SourceModel (sourceImage M K) f := by
  rcases hm with (h | h) | h
  · rcases h with ⟨F,_,_,_,_,hF,e,he⟩ | ⟨m,hm,hf,e,he⟩
    · exact .linearTwo F hF e
    · exact .suzuki m (by omega) hf e
  · obtain ⟨F,_,_,_,J,_,_,hF,hc,_,e,_⟩ := h
    exact .unitary F J hF hc e
  · rcases h with ⟨F,_,_,_,_,hF,e,_,_⟩ | ⟨F,_,_,_,_,hF,e,_,_⟩
    · exact .linearThree F hF e
    · exact .symplecticFour F hF e

/-- The concrete standard unitary Borel normalizes the projective image of
the actual root Sylow subgroup. -/
theorem unitary_borel_normalizer {F : Type} [Field F] [Finite F]
    (J : HermitianForm 3 F) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hf : 0 < f) (hF : Nat.card F = (2 ^ f)^2)
    (hc : ∀x, J.conj x = x ^ (2 ^ f)) :
    ∃ P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J),
      normalizer (P : Set (ProjectiveSpecialUnitaryMatrixGroup J)) = unitaryBorel J hJ := by
  obtain ⟨_,_,S,hS,_⟩ := ChapterF.Source.Unitary.standard_su_borel_data J f hf hF hc hJ
  let P := S.mapSurjective (suProjection_surjective J)
  have hP : (P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) =
      (hermitianUnipotentPSU J hJ).range := by
    change (S : Subgroup J.specialSubgroup).map (suProjection J) = _
    rw [hS]
    exact ChapterF.Source.Unitary.suRoot_map_projection J hJ
  obtain ⟨_,_,_,_,_,_,hs,hN,_⟩ :=
    ChapterF.Source.Unitary.standard_projective_matrix_borel J f hf hF hc hJ
  refine ⟨P, ?_⟩
  change normalizer ((P : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) :
    Set (ProjectiveSpecialUnitaryMatrixGroup J)) = _
  rw [hP,hN,← hs]

/-- Every genuine normal-source Borel pair is a Sylow normalizer. This
preserves the given recognition map, including the rank-two source Borels. -/
theorem source_borel_normalizer_of_normal_cases
    (hm : BenderModel M K f ∨ DiagramModel M K T f) (hf : 1 < f) :
    ∃ P : Sylow 2 (sourceImage M K),
      normalizer (P : Set (sourceImage M K)) = componentOverlap M K := by
  rcases hm with (h | h) | h
  · rcases h with ⟨F,_,_,_,_,_,e,he⟩ | ⟨m,hm,_,e,he⟩
    · let d := e.trans (BorelReduction.sl2ProjectiveEquiv (F := F)).symm
      have hd : (componentOverlap M K).map d.toMonoidHom = Matrix.SpecialLinearGroup.rankOneBorel F := by
        change (componentOverlap M K).map
          ((BorelReduction.sl2ProjectiveEquiv (F := F)).symm.toMonoidHom.comp e.toMonoidHom) = _
        rw [← map_map]
        rw [he,BorelReduction.sl2ProjectiveEquiv_borel,slTwo_source_borel_eq]
      exact exists_sylow_normalizer_of_equiv d _ _ hd (slTwo_borel_normalizer (F := F))
    · exact exists_sylow_normalizer_of_equiv e _ _ he (suzuki_borel_normalizer m (by omega))
  · obtain ⟨F,_,_,_,J,hJ,_,hF,hc,_,e,he⟩ := h
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_equiv (sourceImage M K) e.toEquiv
    exact exists_sylow_normalizer_of_equiv e _ _ he (unitary_borel_normalizer J hJ (by omega) hF hc)
  · rcases h with ⟨F,_,_,_,_,hF,e,he,_⟩ | ⟨F,_,_,_,_,hF,e,he,_⟩
    · exact exists_sylow_normalizer_of_equiv e _ _ he
        ⟨Matrix.PSL3.LinearThree.unipotentSylow F (by omega) hF,
          Matrix.PSL3.LinearThree.normalizer_unipotent F (by omega) hF⟩
    · let d := e.trans (spFourDerivedEquiv hF hf)
      have hd : (componentOverlap M K).map d.toMonoidHom = Theory.SpecificGroups.SymplecticFour.borel := by
        change (componentOverlap M K).map ((spFourDerivedEquiv hF hf).toMonoidHom.comp e.toMonoidHom) = _
        rw [← map_map]
        rw [he]
        exact Cases.Single.CoverModels.spFourDerivedEquiv_subgroupOf hF hf _
      exact exists_sylow_normalizer_of_equiv d _ _ hd
        (Cases.Single.RankTwoMarkings.spFour_borel_normalizer hF (by omega))
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal
