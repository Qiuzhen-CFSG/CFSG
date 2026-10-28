module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Centralizer
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremC
public import Theory.GroupTheory.SolvableSylowSupplement

/-!
# The escaping residual and component in the centralizer

Every solvable overgroup of the original T lies in M. The solvable
Frattini supplement to G_z's residual therefore lies in M, so escape of
G_z forces its residual to escape. The complete A/C source generation
theorem identifies that residual with the C-component layer and supplies
an actual escaping C-component. This is the opening reduction of 10.3.3;
recognition of its orbit and the wreath quotient remain separate.

Source: Aschbacher--Smith 10.3.3, printed p.756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}

/-- The escaping residual conclusion uses only the survivor's proved
solvable-overgroup bound and the actual centralizer escape. -/
theorem CentralizerData.residual_escapes (d : CentralizerData T D s) :
    ¬ (solvableResidual (centralizer ({d.first * d.second} : Set G))).map
      (centralizer ({d.first * d.second} : Set G)).subtype ≤ D.maximalLocal := by
  let C := centralizer ({d.first * d.second} : Set G)
  let S := T.subtype d.sylow_le_centralizer
  obtain ⟨N,hsol,hSN,hgen⟩ := exists_solvable_sylow_supplement S
  let := hsol
  let : Group.IsSolvable (N.map C.subtype) :=
    Group.isSolvable_of_surjective
      (f := (N.equivMapOfInjective C.subtype C.subtype_injective).toMonoidHom)
      (N.equivMapOfInjective C.subtype C.subtype_injective).surjective
  have hTN : (T : Subgroup G) ≤ N.map C.subtype := by
    have hh := map_mono (f := C.subtype) hSN
    change ((T : Subgroup G).subgroupOf C).map C.subtype ≤ N.map C.subtype at hh
    rwa [map_subgroupOf_eq_of_le d.sylow_le_centralizer] at hh
  have hNM := s.solvable_overgroups_le hTN
  intro hRM
  apply d.escape
  have hh := congrArg (map C.subtype) hgen
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hh
  exact hh.symm.le.trans (sup_le hNM hRM)

/-- The genuine local A.3.9 generation theorem supplies a C-component
outside M, rather than merely a nonsolvable subgroup or family tag. -/
theorem CentralizerData.exists_escaping_component (d : CentralizerData T D s) :
    ∃ I : Subgroup G,
      I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G)) ∧
      ¬ I ≤ D.maximalLocal := by
  let C := centralizer ({d.first * d.second} : Set G)
  have hC : C ∈ Chapter1.H G := Chapter1.mem_H_of_isTwoLocal
    (isTwoLocal_involution_centralizer d.order)
  have hgen : cComponentLayer C = solvableResidual C :=
    Chapter1.Section02.proposition_1_2_1_one_of_A_3_9
      (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
        (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
        (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
          (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO)
      (Chapter1.Section02.uniqueness_local_quotient_sqtk D.simpleQTKE hC)
  by_contra! hnone
  apply d.residual_escapes
  rw [←hgen]
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  intro I hI
  apply map_le_iff_le_comap.mp
  apply hnone (I.map C.subtype)
  refine ⟨map_subtype_le I, ?_⟩
  change ((I.map C.subtype).subgroupOf C).IsCComponent
  change I.IsCComponent at hI
  simpa only [subgroupOf, comap_map_eq_self_of_injective C.subtype_injective] using hI

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
