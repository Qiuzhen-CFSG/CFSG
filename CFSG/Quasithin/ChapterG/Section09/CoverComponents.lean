module
public import CFSG.Quasithin.ChapterG.Section09.Setup
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.OrbitSource
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs
public import Theory.GroupTheory.CComponent.ResidualLifting

/-!
# Actual component lifts through an SQTK cover

A quotient component lifts to a C-component because the C-components in its
literal preimage generate the solvable residual. The proved A.3 source theorem
supplies that generation on subgroups of the cover. The cover's component
normalizer has index at most two, and index divisibility passes the bound to
the quotient. The full kernel need not be solvable and no SQTK assertion is
made for an arbitrary quotient.

This discharges the component-orbit input G.10.8(3ii) in the G.11 application.
Source: Aschbacher--Smith A.3.9, 1.2.1, G.10.8 and G.11.6, printed pp.46,
503--504,360,366.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section09
universe u
variable {G : Type u} [Group G]

private theorem layer_eq_residual [Finite G] (h : IsSQTK KnownSimple.IsKnownSimple G) :
    cComponentLayer G = solvableResidual G := by
  have hq : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G) := by
    refine ⟨?_,h.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 G) pCore_isPGroup).trans
      (h.stronglyQuasithin p hp ho)
  let := pCore_isNilpotent (p := 2) (G := G)
  apply cComponentLayer_eq_residual_of_quotient (pCore 2 G)
  exact ChapterA.Section03.SourceComponents.generation
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    hq (pCore_quotient_pCore_eq_bot 2)

/-- Lift a specified ordinary quotient component to an actual C-component of
its SQTK cover. No solvability assumption is imposed on the full kernel. -/
theorem SQTKCover.exists_component_lift (c : SQTKCover KnownSimple.IsKnownSimple G)
    {L : Subgroup G} (hL : IsComponent G L) :
    ∃ K : Subgroup c.Cover, K.IsCComponent ∧ K.map c.projection = L ∧
      (normalizer (K : Set c.Cover)).index ≤ 2 := by
  obtain ⟨K,hK,he⟩ := exists_cComponent_map_eq_of_preimage_layer
    c.projection c.surjective hL.isCComponent
    (layer_eq_residual (c.sqtk.subgroup (L.comap c.projection)))
  refine ⟨K,hK,he,?_⟩
  rcases Chapter1.Section02.component_normal_or_index_two_source c.sqtk hK with hn | hi
  · let := hn
    simp only [normalizer_eq_top,index_top]
    decide
  · exact hi.le

/-- Every ordinary component of a quotient of an SQTK group has at most two
conjugates, by lifting to the cover and descending the normalizer index. -/
theorem SQTKCover.component_normalizer_index_le_two
    (c : SQTKCover KnownSimple.IsKnownSimple G) {L : Subgroup G}
    (hL : IsComponent G L) : (normalizer (L : Set G)).index ≤ 2 := by
  obtain ⟨K,hK,he,hi⟩ := c.exists_component_lift hL
  have hd := (Subgroup.index_dvd_of_le (K.le_normalizer_map c.projection)).trans
    ((normalizer (K : Set c.Cover)).index_map_dvd c.surjective)
  rw [he] at hd
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero
    (normalizer (K : Set c.Cover)).index_ne_zero_of_finite) hd).trans hi

/-- The literal conjugate set has size at most two. -/
theorem SQTKCover.component_conjugates_ncard_le_two
    (c : SQTKCover KnownSimple.IsKnownSimple G) {L : Subgroup G}
    (hL : IsComponent G L) :
    (Set.range fun g : G => L.map (MulAut.conj g).toMonoidHom).ncard ≤ 2 := by
  simpa only [ncard_conjugates_eq_index_normalizer] using c.component_normalizer_index_le_two hL

end CFSG.Quasithin.ChapterG.Section09
