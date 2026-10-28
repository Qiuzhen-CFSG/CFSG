module
public import Theory.GroupTheory.Amalgam.RankTwoCompletion

/-!
# Ambient equivalence transport for faithful rank-two completions

Compose both endpoint maps with a multiplicative equivalence. Injectivity,
generation and the original commuting square are preserved, as is a supplied
whole-overlap identity. This changes only the ambient carrier, retaining
all three original markings.

Source: equivalence of completions in Aschbacher–Smith F.2.1–2, pp.264–265.
-/

@[expose] public noncomputable section
namespace Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
open Subgroup
variable {L B R G H : Type*} [Group L] [Group B] [Group R] [Group G] [Group H]
variable {α : RankTwoAmalgam L B R} (c : FaithfulCompletion α (G := G)) (e : G ≃* H)

/-- Change the ambient carrier through an actual multiplicative equivalence. -/
def mapEquiv : FaithfulCompletion α (G := H) where
  left := e.toMonoidHom.comp c.left
  right := e.toMonoidHom.comp c.right
  compatible := by rw [MonoidHom.comp_assoc,MonoidHom.comp_assoc,c.compatible]
  left_injective := e.injective.comp c.left_injective
  right_injective := e.injective.comp c.right_injective
  middle_injective := e.injective.comp c.middle_injective
  generated := by
    rw [MonoidHom.range_comp,MonoidHom.range_comp,←Subgroup.map_sup,c.generated,←MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr e.surjective

/-- Whole image overlap is preserved by ambient equivalence. -/
theorem mapEquiv_overlap (hc : c.left.range ⊓ c.right.range = c.middle.range) :
    (c.mapEquiv e).left.range ⊓ (c.mapEquiv e).right.range = (c.mapEquiv e).middle.range := by
  change (e.toMonoidHom.comp c.left).range ⊓ (e.toMonoidHom.comp c.right).range =
    (e.toMonoidHom.comp c.middle).range
  rw [MonoidHom.range_comp,MonoidHom.range_comp,MonoidHom.range_comp,
    ←map_inf _ _ _ e.injective,hc]

end Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
