module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.SecondParabolic.Overlap
public import Theory.GroupTheory.Amalgam.SylowRigidity

/-!
# Extension of native Hall–Janko Borel actions

An element of the explicit outer Borel normalizes both the inner Borel and
its full second parabolic. Restricting its single ambient action to both
subgroups gives a commuting inclusion square. Thus a pointwise conjugation
coverage theorem for Borel automorphisms supplies exactly the extension
premise needed to remove the discrepancy between independent source maps.

The finite coverage assertion remains an explicit input here. The consumer
is the full-Borel gluing step for DGS (10.9), printed pp.162–163, before the
original J₂/Aut(J₂) restoration from (15.3), printed pp.229–231.
-/

public noncomputable section
open Subgroup
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap
open Theory.GroupTheory Seed

private theorem extensionAction_comp (g : Extension) :
    intoExtension.comp (extensionAction g).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp intoExtension := by
  apply MonoidHom.ext
  intro x
  apply extension.subtype_injective
  rfl

private theorem map_eq_of_normalizes (g : Extension) (H : Subgroup Carrier)
    (hg : g ∈ normalizer (H.map intoExtension : Set Extension)) :
    H.map (extensionAction g).toMonoidHom = H := by
  apply Subgroup.map_injective intoExtension_injective
  rw [map_map, extensionAction_comp, ←map_map]
  exact mem_normalizer_iff_map_conj_eq.mp hg

/-- Every element of the enlarged native Borel normalizes the inner Borel. -/
theorem outerB_normalizes_B (hP : Nat.card p₂ = 1152) :
    outerB ≤ normalizer (B.map intoExtension : Set Extension) := by
  exact sup_le (B.map intoExtension).le_normalizer
    (zpowers_le.mpr (outerElement_normalizes_B hP))

/-- The same enlarged Borel normalizes the full second parabolic. -/
theorem outerB_normalizes_p₂ :
    outerB ≤ normalizer (p₂.map intoExtension : Set Extension) := by
  exact sup_le ((map_mono B_le_p₂).trans (p₂.map intoExtension).le_normalizer)
    (zpowers_le.mpr outerElement_normalizes_p₂)

/-- Restriction of a native outer-Borel actor to the inner Borel. -/
def borelAction (hP : Nat.card p₂ = 1152) (g : outerB) : MulAut B :=
  ((extensionAction (g : Extension)).subgroupMap B).trans
    (MulEquiv.subgroupCongr (map_eq_of_normalizes (g : Extension) B
      (outerB_normalizes_B hP g.property)))

/-- Restriction of the same actor to the full second parabolic. -/
def parabolicAction (g : outerB) : MulAut p₂ :=
  ((extensionAction (g : Extension)).subgroupMap p₂).trans
    (MulEquiv.subgroupCongr (map_eq_of_normalizes (g : Extension) p₂
      (outerB_normalizes_p₂ g.property)))

/-- The native restriction has an actual extension across the Borel inclusion. -/
theorem borelAction_extends (hP : Nat.card p₂ = 1152) (g : outerB) :
    RankTwoAmalgam.ExtendsAcross (Subgroup.inclusion B_le_p₂) (borelAction hP g) := by
  refine ⟨parabolicAction g, fun b => ?_⟩
  apply Subtype.ext
  rfl

/-- Pointwise ambient conjugation coverage discharges the exact native extension
premise used to glue the two reduced field-four endpoint maps. -/
theorem borel_extends_of_outerB_coverage (hP : Nat.card p₂ = 1152)
    (hcover : ∀ d : MulAut B, ∃ g : outerB, ∀ b : B,
      intoExtension (d b : Carrier) =
        (g : Extension) * intoExtension (b : Carrier) * (g : Extension)⁻¹)
    (d : MulAut B) :
    RankTwoAmalgam.ExtendsAcross (Subgroup.inclusion B_le_p₂) d := by
  obtain ⟨g,hg⟩ := hcover d
  have he : borelAction hP g = d := by
    apply MulEquiv.ext
    intro b
    apply Subtype.ext
    apply intoExtension_injective
    exact (DFunLike.congr_fun (extensionAction_comp (g : Extension)) (b : Carrier)).trans
      (hg b).symm
  rw [←he]
  exact borelAction_extends hP g

end Sporadic.LeechRelated.J2.ExceptionalParabolics.SecondParabolic.Overlap
