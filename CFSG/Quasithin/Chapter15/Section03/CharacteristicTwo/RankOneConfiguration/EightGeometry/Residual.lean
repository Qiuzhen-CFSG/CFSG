module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Basic

/-!+# Restricting the fixed-plane residual to the component

Once `L = O^{3′}(C_G(Z₁))`, every three-element centralizing `Z_S`
belongs to `L`, since `Z₁ ≤ Z_S`. Thus the three-prime residual of
`C_G(Z_S)` equals that of `C_L(Z_S)`. This also places `XS` inside `I`.

Identifying `C_L(Z_S)` with the end-node parabolic is still a geometric
obligation. No equality with the two-residual is used here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the implication from 15.3.32(3) to (4), printed p.1133.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry

open Subgroup

variable {G : Type*} [Group G]

/-- Conclusion (3) restricts the fixed-plane three-prime residual to the
component centralizer. The identification of that centralizer as a parabolic
is deliberately separate. -/
theorem threeResidual_fixedPlane_eq_component_intersection
    (d : LocalData G) {L : Subgroup G}
    (hL : L = RankOne.threeResidualIn (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G))) :
    RankOne.threeResidualIn (centralizer (d.ZS : Set G)) =
      RankOne.threeResidualIn (L ⊓ centralizer (d.ZS : Set G)) := by
  simp only [RankOne.threeResidualIn, map_primePowerGenerated_subtype]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro g ⟨hg, n, hn⟩
    have hgL : g ∈ L := by
      rw [hL, RankOne.threeResidualIn, map_primePowerGenerated_subtype]
      exact Subgroup.subset_closure ⟨centralizer_le inf_le_left hg, n, hn⟩
    exact Subgroup.subset_closure ⟨⟨hgL, hg⟩, n, hn⟩
  · apply Subgroup.closure_mono
    rintro g ⟨hg, n, hn⟩
    exact ⟨hg.2, n, hn⟩

/-- The residual-centralizer equality puts the whole overgroup `XS` in `I`. -/
theorem residual_join_le_of_line_centralizer
    (d : LocalData G) {I : Subgroup G} (hI : I ∈ d.Hplus)
    (c : ComponentWitness d I)
    (hL : c.L = RankOne.threeResidualIn
      (centralizer ((d.ZS ⊓ d.V₁ : Subgroup G) : Set G))) :
    RankOne.threeResidualIn (centralizer (d.ZS : Set G)) ⊔ d.S ≤ I := by
  apply sup_le ?_ (le_sup_right.trans hI.1.2)
  rw [threeResidual_fixedPlane_eq_component_intersection d hL]
  exact (map_subtype_le _).trans (inf_le_left.trans (component_le c))

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry

end
