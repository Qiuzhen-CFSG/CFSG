module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.Reduction
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# Transport of the proper Sylow-overgroup Fitting bound

A model equivalence maps the specified Sylow and its overgroup to their
literal images. The induced subgroup equivalence carries the generalized
Fitting subgroup and two-core onto their counterparts and carries the
intersection with the ambient centre onto the corresponding central factor.

This supplies model transport for Aschbacher–Smith B.1.13, printed p.74
(PDF p.85); it asserts no recognition or central-cover lifting result.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

/-- Pull the complete bound back along an actual group equivalence. -/
theorem properSylowFittingBound_of_equiv {G H : Type*} [Group G] [Group H] [Finite G]
    (e : G ≃* H) (h : ProperSylowFittingBound H) : ProperSylowFittingBound G := by
  intro S X hSX hX
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let Y := X.map e.toMonoidHom
  have hTY : (T : Subgroup H) ≤ Y := Subgroup.map_mono hSX
  have hY : Y ≠ ⊤ := by
    intro ht
    apply hX
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    exact ht
  let eX : X ≃* Y := e.subgroupMap X
  have hz : ((center H).subgroupOf Y).map eX.symm.toMonoidHom ≤
      (center G).subgroupOf X := by
    rintro _ ⟨z, hz, rfl⟩
    change (z : H) ∈ center H at hz
    change (eX.symm z : G) ∈ center G
    change e.symm (z : H) ∈ center G
    apply mem_center_iff.mpr
    intro x
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using mem_center_iff.mp hz (e x)
  have hh := Subgroup.map_mono (f := eX.symm.toMonoidHom) (h T Y hTY hY)
  rw [map_generalizedFitting_equiv, Subgroup.map_sup, pCore_map_iso] at hh
  exact hh.trans (sup_le_sup_left hz _)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
