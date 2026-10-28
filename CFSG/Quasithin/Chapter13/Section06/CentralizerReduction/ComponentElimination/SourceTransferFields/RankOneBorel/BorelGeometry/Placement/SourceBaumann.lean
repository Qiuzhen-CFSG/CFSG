module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement.SourceImage
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ImagesSource
/-!
# The source Baumann image on an arbitrary literal centralizer quotient

Transport the original E.2.3 Thompson--Baumann equality through the canonical
isomorphism from H/C_H(V) to the supplied quotient. Its trivial two-core proves
that the original normal elementary subgroup is reduced. This discharges the
universal Baumann input used by the rank-one branch of 13.6.18.
Source: Aschbacher--Smith E.2.3(2--3), printed pp.216--217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
universe u

theorem sourceBaumannImplication_knownSimple : SourceBaumannImplication.{u} KnownSimple.IsKnownSimple := by
  intro H A _ _ _ _ P V _ _ q hq hk hH hP _ hcore hJ
  let C := centralizer (V : Set H)
  let e : (H ⧸ C) ≃* A := QuotientGroup.liftEquiv C hq hk.symm
  have hred : IsPReduced 2 V := {
    normal := inferInstance
    elementary := inferInstance
    quotient_pCore_eq_bot := by
      rw [←pCore_map_iso 2 e.symm,hcore,Subgroup.map_bot] }
  have h := ChapterE.ThompsonAction.source_thompson_baumann_image hH P hP V hred hJ
  have hh := congrArg (Subgroup.map e.toMonoidHom) h
  have he : e.toMonoidHom.comp (QuotientGroup.mk' C) = q := by
    ext a
    rfl
  rw [Subgroup.map_map,Subgroup.map_map] at hh
  change (elementaryAbelianMaxJ (P : Subgroup H)).map
    (e.toMonoidHom.comp (QuotientGroup.mk' C)) =
      (ChapterB.baumann (P : Subgroup H)).map (e.toMonoidHom.comp (QuotientGroup.mk' C)) at hh
  rw [he] at hh
  exact hh.symm
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.RankOneBorel.BorelGeometry.Placement
