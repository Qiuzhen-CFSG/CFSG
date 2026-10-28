module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Transvections
public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.ConjugateIntersections.Hyperplane
public import Theory.Representation.SL2FourNaturalOrbits.NoTransvections

/-!
# The natural and dual S₅ actions have no binary transvections

The alternating subgroup maps onto the original natural SL₂(4) image
through the supplied marking, so normality puts every S₅ actor in its
binary linear normalizer. The concrete normalizer exclusion then applies.
Duality preserves displacement rank, giving precisely the model premise
used in the hyperplane argument for distinct L-conjugates of U.

Source: Aschbacher–Smith, J.2.2(5), printed pp.432–433 (PDF pp.443–444),
combined manuscript of 1 March 2004. No parabolic conclusion is assumed.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ
open Representation Subgroup

private def L2FourAction.linearAction (r : L2FourAction) : S5 →* (FourSpace ≃ₗ[ZMod 2] FourSpace) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) FourSpace).toMonoidHom.comp
    r.action.asGroupHom

private theorem L2FourAction.linearAction_marking (r : L2FourAction) (g : SL2FourNatural.SL) :
    r.linearAction (r.marking g) = SL2FourNatural.action g :=
  LinearEquiv.ext (r.restriction g)

private theorem L2FourAction.linearAction_image_alternating (r : L2FourAction) :
    (alternatingGroup (Fin 5)).map r.linearAction = SL2FourNatural.action.range := by
  apply le_antisymm
  · rintro x ⟨g, hg, rfl⟩
    refine ⟨r.marking.symm ⟨g, hg⟩, ?_⟩
    rw [← r.linearAction_marking, r.marking.apply_symm_apply]
  · rintro x ⟨g, rfl⟩
    exact ⟨r.marking g, (r.marking g).property, r.linearAction_marking g⟩

/-- The given S₅ action normalizes the actual natural SL₂(4) image. -/
private theorem L2FourAction.mem_natural_normalizer (r : L2FourAction) (g : S5) :
    r.linearAction g ∈ SL2FourNatural.SemilinearNormalizer.normalizer := by
  have h := (alternatingGroup (Fin 5)).le_normalizer_map r.linearAction
  rw [r.linearAction_image_alternating] at h
  apply h
  exact ⟨g, by rw [normalizer_eq_top]; trivial, rfl⟩

private theorem L2FourAction.dual_displacement_rank (r : L2FourAction) (g : S5) :
    Module.finrank (ZMod 2) (LinearMap.range (r.action.dual g - LinearMap.id)) =
      Module.finrank (ZMod 2) (LinearMap.range (r.action g⁻¹ - LinearMap.id)) := by
  have he : r.action.dual g - LinearMap.id = (r.action g⁻¹ - LinearMap.id).dualMap := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro v
    change f (r.action g⁻¹ v) - f v = f (r.action g⁻¹ v - v)
    exact (map_sub f _ _).symm
  rw [he, LinearMap.finrank_range_dualMap_eq_finrank_range]

/-- Every actor in the given natural S₅ representation avoids binary rank one. -/
theorem L2FourAction.no_rank_one (r : L2FourAction) (g : S5) :
    Module.finrank (ZMod 2) (LinearMap.range (r.action g - LinearMap.id)) ≠ 1 :=
  SL2FourNatural.normalizer_no_rank_one (r.linearAction g) (r.mem_natural_normalizer g)

/-- The same exclusion holds on the actual contragredient representation. -/
theorem L2FourAction.dual_no_rank_one (r : L2FourAction) (g : S5) :
    Module.finrank (ZMod 2) (LinearMap.range (r.action.dual g - LinearMap.id)) ≠ 1 := by
  rw [r.dual_displacement_rank]
  exact r.no_rank_one g⁻¹

variable {G : Type*} [Group G] [Finite G]

/-- Discharge the concrete model premise of the J.2.2(5) hyperplane argument. -/
theorem LocalSetup.noRankOne (d : LocalSetup G) : ConjugateIntersections.NoRankOne d :=
  d.ru2.naturalAction.dual_no_rank_one

end CFSG.Quasithin.ChapterJ
