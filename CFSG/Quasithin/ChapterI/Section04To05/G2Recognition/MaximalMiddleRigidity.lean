module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalMiddleAlignment
public import Theory.SpecificGroups.G2.TernaryBorelCoordinates

/-!
# The remaining original whole-middle discrepancy in explicit coordinates

Intrinsic cubing and the already proved exclusion of radical exchange make
both original discrepancy images individually invariant. The actual torus
is then fixed pointwise. All six root coordinates have one simultaneous
four-parameter formula: two nonzero scalars and two central simple-root
shifts. Every element of the entire order-2916 middle is covered by this
formula, through its root-group and torus factors.

The endpoint maps, their core and actor formulas, and the original Sylow
aligner remain those of MaximalMiddleAlignment. An additional torus conjugation removes both root scalars. Extending the
remaining central shifts by endpoint automorphisms remains necessary for completion
recognition. Chapter14MiddleRigidity is the literal source application.
Source: Aschbacher–Smith I.4.5, p.417, via F.4.26, p.288.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace AlignedCubicPair.MiddleAlignment
variable {t : CubicTorus c} {p : AlignedCubicPair t} (d : p.MiddleAlignment)

/-- Both entire radicals are invariant, not merely distinct. -/
theorem difference_radicals (side : Bool) :
    (Atlas.G2.TernaryBorel.middleRadical side).map d.difference.toMonoidHom=
      Atlas.G2.TernaryBorel.middleRadical side :=
  Atlas.G2.TernaryBorel.automorphism_radicals_fixed d.difference d.difference_not_exchange side

/-- The original discrepancy fixes the actual split torus pointwise. -/
theorem difference_torus_pointwise :
    ∀ x∈Atlas.G2.TernaryBorel.A.subgroupOf Atlas.G2.TernaryBorel.B,d.difference x=x :=
  Atlas.G2.TernaryBorel.automorphism_torus_pointwise d.difference
    d.difference_torus d.difference_radicals

/-- One formula determines the discrepancy on the whole Borel. -/
theorem difference_coordinates :
    ∃ (e f j k : ZMod 3),e≠0 ∧ f≠0 ∧
      ∀ (v : Fin 6 → ZMod 3) (l m : (ZMod 3)ˣ),
        d.difference (Atlas.G2.TernaryBorel.positive v*Atlas.G2.TernaryBorel.diagonal l m)=
          Atlas.G2.TernaryBorel.positive (Atlas.G2.TernaryBorel.twistCoordinates e f j k v)*
            Atlas.G2.TernaryBorel.diagonal l m :=
  Atlas.G2.TernaryBorel.automorphism_whole_coordinates d.difference
    d.difference_torus d.difference_radicals

/-- The formula relates both original middle restrictions on every element. -/
theorem middle_restrictions_coordinates :
    ∃ (e f j k : ZMod 3),e≠0 ∧ f≠0 ∧
      ∀ b : t.leftCubicBorel,
        ∃ (v : Fin 6 → ZMod 3) (l m : (ZMod 3)ˣ),
          d.leftMiddle b=Atlas.G2.TernaryBorel.positive v*Atlas.G2.TernaryBorel.diagonal l m ∧
          d.rightMiddle b=
            Atlas.G2.TernaryBorel.positive (Atlas.G2.TernaryBorel.twistCoordinates e f j k v)*
              Atlas.G2.TernaryBorel.diagonal l m := by
  obtain ⟨e,f,j,k,he,hf,h⟩ := d.difference_coordinates
  refine ⟨e,f,j,k,he,hf,?_⟩
  intro b
  obtain ⟨v,l,m,hb⟩ := Atlas.G2.TernaryBorel.exists_positive_diagonal (d.leftMiddle b)
  refine ⟨v,l,m,hb,?_⟩
  have hd : d.difference (d.leftMiddle b)=d.rightMiddle b := by simp [difference]
  rw [←hd,hb,h]

private theorem inner_square {X Y : Type*} [Group X] [Group Y]
    (i : X →* Y) (g : Y) (a : X) (x : Y) (b : X)
    (h : g*x*g⁻¹=i b) :
    (i a*g)*x*(i a*g)⁻¹=i (a*b*a⁻¹) := by
  rw [map_mul,map_mul,map_inv,←h]
  group

/-- An actual additional inner correction in the right endpoint, preserving
all original comparisons and the literal Sylow aligner. -/
noncomputable def correctRightByTorus (a : Atlas.G2.TernaryBorel.B)
    (ha : a∈Atlas.G2.TernaryBorel.A.subgroupOf Atlas.G2.TernaryBorel.B) : p.MiddleAlignment where
  leftComparison := d.leftComparison
  rightComparison := d.rightComparison
  leftCorrection := d.leftCorrection
  rightCorrection := inclusion (Atlas.G2.TernaryBorel.borel_le_endpoint true) a*d.rightCorrection
  leftMiddle := d.leftMiddle
  rightMiddle := d.rightMiddle.trans (MulAut.conj a)
  left_commutes := d.left_commutes
  right_commutes b := by
    exact inner_square (inclusion (Atlas.G2.TernaryBorel.borel_le_endpoint true))
      d.rightCorrection a (p.rightAtlasEndpointEquiv d.rightComparison (p.amalgam.right b))
      (d.rightMiddle b) (d.right_commutes b)
  left_torus := d.left_torus
  right_torus := by
    change p.middleTorus.map ((MulAut.conj a).toMonoidHom.comp d.rightMiddle.toMonoidHom)=_
    rw [←map_map,d.right_torus]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((Atlas.G2.TernaryBorel.A.subgroupOf Atlas.G2.TernaryBorel.B).le_normalizer ha)

/-- The new right correction is the explicit torus multiplier times the old one. -/
theorem correctRightByTorus_rightCorrection (a : Atlas.G2.TernaryBorel.B)
    (ha : a∈Atlas.G2.TernaryBorel.A.subgroupOf Atlas.G2.TernaryBorel.B) :
    (d.correctRightByTorus a ha).rightCorrection=
      inclusion (Atlas.G2.TernaryBorel.borel_le_endpoint true) a*d.rightCorrection := by rfl

/-- This correction changes the exact whole-middle difference by conjugation. -/
theorem correctRightByTorus_difference (a : Atlas.G2.TernaryBorel.B)
    (ha : a∈Atlas.G2.TernaryBorel.A.subgroupOf Atlas.G2.TernaryBorel.B)
    (x : Atlas.G2.TernaryBorel.B) :
    (d.correctRightByTorus a ha).difference x=MulAut.conj a (d.difference x) := by rfl

/-- After endpoint-inner correction only two central shifts remain, on the
whole middle. Neither shift is assumed to extend to an endpoint. -/
theorem exists_normalized_middle :
    ∃ (a : p.MiddleAlignment) (j k : ZMod 3),
      a.leftComparison=d.leftComparison ∧ a.rightComparison=d.rightComparison ∧
      a.leftCorrection=d.leftCorrection ∧
      ∀ (v : Fin 6 → ZMod 3) (l m : (ZMod 3)ˣ),
        a.difference (Atlas.G2.TernaryBorel.positive v*Atlas.G2.TernaryBorel.diagonal l m)=
          Atlas.G2.TernaryBorel.positive (Atlas.G2.TernaryBorel.twistCoordinates 1 1 j k v)*
            Atlas.G2.TernaryBorel.diagonal l m := by
  obtain ⟨a,j,k,ha,h⟩ := Atlas.G2.TernaryBorel.exists_diagonal_normalization d.difference
    d.difference_torus d.difference_radicals
  exact ⟨d.correctRightByTorus a ha,j,k,rfl,rfl,rfl,h⟩

/-- Both corrected original restrictions have the same six scalar coordinates;
only the two explicitly displayed central shifts can still differ. -/
theorem exists_normalized_restrictions :
    ∃ (a : p.MiddleAlignment) (j k : ZMod 3),
      a.leftComparison=d.leftComparison ∧ a.rightComparison=d.rightComparison ∧
      a.leftCorrection=d.leftCorrection ∧
      ∀ b : t.leftCubicBorel,
        ∃ (v : Fin 6 → ZMod 3) (l m : (ZMod 3)ˣ),
          a.leftMiddle b=Atlas.G2.TernaryBorel.positive v*Atlas.G2.TernaryBorel.diagonal l m ∧
          a.rightMiddle b=
            Atlas.G2.TernaryBorel.positive (Atlas.G2.TernaryBorel.twistCoordinates 1 1 j k v)*
              Atlas.G2.TernaryBorel.diagonal l m := by
  obtain ⟨a,j,k,hl,hr,hc,h⟩ := d.exists_normalized_middle
  refine ⟨a,j,k,hl,hr,hc,?_⟩
  intro b
  obtain ⟨v,l,m,hb⟩ := Atlas.G2.TernaryBorel.exists_positive_diagonal (a.leftMiddle b)
  refine ⟨v,l,m,hb,?_⟩
  have hd : a.difference (a.leftMiddle b)=a.rightMiddle b := by simp [difference]
  rw [←hd,hb,h]

end AlignedCubicPair.MiddleAlignment
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
