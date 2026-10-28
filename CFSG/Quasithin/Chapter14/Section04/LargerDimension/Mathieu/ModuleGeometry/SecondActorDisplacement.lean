module

public import Theory.Representation.BinaryIndexThreeDisplacement
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Assembly

/-!
# The second Mathieu actor moves a binary plane

The remaining native minimal parabolic has index three over the prescribed
Sylow subgroup, whose fixed binary line is the marked source point. Its actual
two-residual moves that point by the proved actor catalogue. The index-three
orbit argument therefore computes its moved image to have order four,
without assuming a matrix position for its full action on the six-space.
The final theorem retains the catalogue's literal design images and family.

Source: Aschbacher--Smith, Lemma 14.4.12, printed pp.1011--1012.
The independent containment of this moved plane in E remains part of the
source geometry assembly.
-/

@[expose] public section
open Subgroup Representation.BinaryOffender
open CFSG.Quasithin.Chapter14.Section04.LargerDimension
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
open CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry

/-- The actual residual of an index-three native parabolic moves the Sylow
fixed binary line through a subspace of order four. -/
theorem secondActor_commutator_card_four
    (S : Sylow 2 Model) (P : Subgroup Model)
    (hSP : (S : Subgroup Model) ≤ P)
    (hi : (S : Subgroup Model).relIndex P = 3)
    (v : Space) (hfix : ∀ s : S, action s.val v = v)
    (hmove : ¬ twoResidual P ≤ pointCentralizer v) :
    Nat.card (subspaceCommutator action (Submodule.span (ZMod 2) {v}) (twoResidual P)) = 4 := by
  let σ := action.comp P.subtype
  have he : subspaceCommutator σ (Submodule.span (ZMod 2) {v}) (pResidual 2 P) =
      subspaceCommutator action (Submodule.span (ZMod 2) {v}) (twoResidual P) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, w, hw, rfl⟩
      exact Submodule.subset_span ⟨a.val, mem_map_of_mem P.subtype ha, w, hw, rfl⟩
    · apply Submodule.span_le.mpr
      rintro _ ⟨a, ⟨b, hb, rfl⟩, w, hw, rfl⟩
      exact Submodule.subset_span ⟨b, hb, w, hw, rfl⟩
  rw [← he]
  apply index_three_displacement_card σ (S.subtype hSP) (pResidual 2 P)
    (pResidual_sup_sylow_eq_top (S.subtype hSP)) hi v
  · intro s hs
    exact hfix ⟨s.val, hs⟩
  · obtain ⟨a, ha, hm⟩ := Set.not_subset.mp hmove
    obtain ⟨b, hb, rfl⟩ := ha
    exact ⟨b, hb, hm⟩

/-- The genuine three-actor catalogue, with the second moved-image order
proved in its original native carrier and original column action. -/
theorem exists_catalogue_with_second_displacement
    (S : Sylow 2 Model) {v : Space} (hv : v ≠ 0)
    (B : Subgroup Model) (hSB : (S : Subgroup Model) ≤ B)
    (hB : B ≤ pointCentralizer v) (hiB : (S : Subgroup Model).relIndex B = 3) :
    ∃ (P : Subgroup Model) (g : Sporadic.Mathieu.m22DesignAut),
      P ∈ Catalogue.rankOneOvergroups S ∧ Disjoint cubic P ∧
      P.map designProjection = Catalogue.partitionAt g ∧
      B.map designProjection = Catalogue.pairAt g ∧
      XFamily ⊤ (S : Subgroup Model) =
        {twoResidual (pCore 3 Model), twoResidual P, twoResidual B} ∧
      Nat.card (subspaceCommutator action (Submodule.span (ZMod 2) {v}) (twoResidual P)) = 4 := by
  obtain ⟨P, g, hP, hd, hmP, hmB, _, _, _, hmove, _, _, _, hfamily⟩ :=
    Catalogue.exists_catalogue S hv B hSB hB hiB
  refine ⟨P, g, hP, hd, hmP, hmB, hfamily, ?_⟩
  exact secondActor_commutator_card_four S P hP.1 hP.2 v
    (fun s => hB (hSB s.property)) hmove

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry
