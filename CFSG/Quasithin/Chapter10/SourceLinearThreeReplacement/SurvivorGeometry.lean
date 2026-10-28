module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.FixedSpaceTI.HStarParameter.Source
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.Escape.Fusion.Orbits

/-!
# Centralizer geometry from the supplied linear-three survivor

After the global/local parameter contradiction kills the full fixed part,
the actual natural coordinates make L transitive on the nonidentity elements
of [V,L]. If a conjugate meets [V,L] nontrivially, choose l in L taking its
preimage to the intersection point. Then l⁻¹g centralizes that preimage, so
the survivor's point-centralizer bound puts g in M. The existing pair action
therefore gives the moved-factor TI property.

This argument supplies the full centralizer-geometry contract directly from
the original survivor and multiple-overgroup guard. It does not require the
general half-Sylow uniqueness theorem: the survivor already includes the
point-centralizer bounds needed here. The proved core and escape arguments
construct all remaining centralizer data on the same subgroup and action.

Source: Aschbacher--Smith 10.3.1--2, printed pp.755--756, using the natural
case of 10.1.1 and point-centralizer control of 10.2.9.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  (s : SourceLinearThreeSurvivor T D)

include s in
/-- Natural transitivity and the original point centralizers exclude every
outside-M intersection once the full fixed part vanishes. -/
theorem survivor_outside_intersection_of_fixed
    (hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥)
    {g : G} (hg : g ∉ D.maximalLocal) :
    ⁅D.fullModule,L⁆ ⊓ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥ := by
  apply eq_bot_iff.mpr
  rintro x ⟨hx,y,hy,hyx⟩
  change x = 1
  change (MulAut.conj g) y = x at hyx
  by_contra hx1
  have hy1 : y ≠ 1 := by
    intro he
    exact hx1 (hyx.symm.trans (by simp [he]))
  obtain ⟨l,hl,he⟩ := Geometry.Escape.Fusion.moved_transitive s hz hy hx hy1 hx1
  have hc : l⁻¹ * g ∈ centralizer ({y} : Set G) := by
    apply mem_centralizer_singleton_iff.mpr
    have hfix : (MulAut.conj (l⁻¹ * g)) y = y := by
      calc
        _ = (MulAut.conj l⁻¹) ((MulAut.conj g) y) := by
          simp [MulAut.conj_apply, mul_assoc]
        _ = (MulAut.conj l⁻¹) ((MulAut.conj l) y) := by rw [hyx, he]
        _ = y := by simp [MulAut.conj_apply, mul_assoc]
    exact mul_inv_eq_iff_eq_mul.mp hfix
  have hlM : l ∈ D.maximalLocal :=
    (le_componentOrbit L T).trans (localOrbit T L).le_normalizer hl
  exact hg (by simpa [mul_assoc] using
    D.maximalLocal.mul_mem hlM (s.pointCentralizers y hy hy1 hc))

include s in
/-- The two proved parameter bounds kill the literal full fixed part. -/
theorem survivor_fixed_part
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ :=
  Geometry.fixed_part_of_hStar_parameter
    Geometry.FixedSpaceTI.HStarParameter.hStarLocalAAt hmany D s

/-- Original fixed-space vanishing and moved-factor TI, with no further
source input beyond the supplied survivor and standing guard. -/
theorem fixedSpaceTI (T : Sylow 2 G) : Geometry.FixedSpaceTIAt T := by
  intro hmany L D s
  have hz := survivor_fixed_part s hmany
  exact ⟨hz,survivor_moved_ti_of_fixed_of_outside s hz
    (fun _ hg => survivor_outside_intersection_of_fixed s hz hg)⟩

/-- All original centralizer-geometry clauses, including the escaping
central involution, full-core containment and conditional reducedness. -/
theorem centralizerGeometry (T : Sylow 2 G) : CentralizerGeometryAt T :=
  Geometry.centralizerGeometry_of_source_inputs (fixedSpaceTI T)
    (Geometry.CoreReduced.coreReducedAt T) (Geometry.Escape.escapeAt T)
end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement
