module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Orbitals
/-!
# The central plane involution in the cycle argument

Two distinct plane neighbors force a point to be fixed, by stabilization of
its two joining lines. This proves the forward implication of (7.8). At the
end of (7.9), a moved point and its image determine a plane with any fixed
common neighbor. The plane incidence types leave three or five neighbors on
the line. In the three-point case a 27-function checked calculation supplies
a fixed point; regularity on the other four line points identifies it with
the line's plane point. The original involution and literal actions are used
throughout. The converse of (7.8) still requires native (3.8).

Source: AS91 (7.8) and the final paragraph of (7.9), p.605.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open Subgroup
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
namespace Input
variable (d : Input h)

/-- A point with two distinct neighbors in a plane is fixed by its marker.
The proof uses the two literal joining lines and relative point-core actions. -/
theorem marker_fixes_of_two_plane_neighbors {π : Plane z} {x u y : Point d.P}
    (hx : OnPlane d.P x π) (hu : OnPlane d.P u π) (hxu : x ≠ u)
    (hxy : Adj d.L x y) (huy : Adj d.L u y) : marker π • y = y := by
  classical
  by_contra hmove
  let l := d.joiningLine hxy
  let k := d.joiningLine huy
  have hxl : OnLine d.L x l := (d.joiningLine_incident hxy).1
  have hyl : OnLine d.L y l := (d.joiningLine_incident hxy).2
  have huk : OnLine d.L u k := (d.joiningLine_incident huy).1
  have hyk : OnLine d.L y k := (d.joiningLine_incident huy).2
  have hzl : marker π • l = l :=
    d.core_fixes_lines x ⟨marker π, (d.marker_mem_core π x).mpr hx⟩ l hxl
  have hzk : marker π • k = k :=
    d.core_fixes_lines u ⟨marker π, (d.marker_mem_core π u).mpr hu⟩ k huk
  have hzyl : OnLine d.L (marker π • y) l := by
    simpa only [OnLine, hzl] using incident_smul (marker π) hyl
  have hzyk : OnLine d.L (marker π • y) k := by
    simpa only [OnLine, hzk] using incident_smul (marker π) hyk
  have hlk := d.line_eq_of_incident (Ne.symm hmove) hyl hzyl hyk hzyk
  have hul : OnLine d.L u l := hlk ▸ huk
  have hlπ := d.plane_closed x u l π hxu hxl hul hx hu
  exact hmove (d.marker_fixes_point (d.string y l π hyl hlπ))

/-- The forward half of (7.8): being coplanar with a line of the plane's
point residue forces the original central involution to fix the neighbor. -/
theorem marker_fixes_of_coplanar_line {π : Plane z} {x y : Point d.P}
    (hxπ : OnPlane d.P x π) (hxy : Adj d.L x y) {l m : Line d.L}
    (hxl : OnLine d.L x l) (hlπ : LineOnPlane d.L l π)
    (hxm : OnLine d.L x m) (hym : OnLine d.L y m) (hcop : Coplanar d.L l m) :
    marker π • y = y := by
  obtain ⟨i, hi, ht⟩ := (d.delta_coplanar x m l hxm hxl).mp (by
    obtain ⟨σ, hl, hm⟩ := hcop
    exact ⟨σ, hm, hl⟩)
  have hin : i = 0 ∨ i = 1 ∨ i = 2 := by
    fin_cases i <;> simp_all
  rcases hin with rfl | rfl | rfl
  · obtain ⟨_, hlm⟩ := (d.delta_zero x m l).mp ht
    exact d.marker_fixes_point (d.string y l π (hlm.symm ▸ hym) hlπ)
  · have hc := d.delta_one_neighbors x y m l hxm hym hxy.1.symm ht
    obtain ⟨u, hu, hux⟩ := Set.exists_ne_of_one_lt_ncard (by omega :
      1 < {u | OnLine d.L u l ∧ Adj d.L y u}.ncard) x
    exact d.marker_fixes_of_two_plane_neighbors hxπ
      (d.string u l π hu.1 hlπ) hux.symm hxy (adj_symm hu.2)
  · obtain ⟨u, hul, hux⟩ := Set.exists_ne_of_one_lt_ncard (by
      rw [d.line_card l]; norm_num : 1 < {u | OnLine d.L u l}.ncard) x
    exact d.marker_fixes_of_two_plane_neighbors hxπ
      (d.string u l π hul hlπ) hux.symm hxy
      (adj_symm (d.delta_two_neighbors x y m l hxm hym hxy.1.symm ht u hul))

/-- The marker sends each point back after two applications. -/
theorem marker_involutive (π : Plane z) : Function.Involutive (fun x : Point d.P => marker π • x) := by
  intro x
  change marker π • (marker π • x) = x
  rw [← mul_smul, marker_sq h π, one_smul]

end Input

/-- The three-point involution calculation used in the last paragraph of
(7.9). This certificate has only 27 candidate functions. -/
theorem three_involution_fixed {X : Type*} [Finite X] (hc : Nat.card X = 3)
    (f : X → X) (hf : Function.Involutive f) : ∃ x, f x = x := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let e : X ≃ Fin 3 := Fintype.equivFinOfCardEq (by rwa [← Nat.card_eq_fintype_card])
  have small : ∀ f : Fin 3 → Fin 3, (∀ x, f (f x) = x) → ∃ x, f x = x := by decide +kernel
  have hi : ∀ x, (e ∘ f ∘ e.symm) ((e ∘ f ∘ e.symm) x) = x := by
    intro x
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    rw [hf, Equiv.apply_symm_apply]
  obtain ⟨x, hx⟩ := small (e ∘ f ∘ e.symm) hi
  refine ⟨e.symm x, e.injective ?_⟩
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hx

namespace Input
variable (d : Input h)

/-- The final involution step of (7.9), retaining the literal line and plane
marker. A fixed point adjacent to a moved point of the line is adjacent to
its unique fixed point, provided those two fixed points are distinct. -/
theorem marker_fixed_neighbor_on_moved_line {π : Plane z} {y w v : Point d.P} {l : Line d.L}
    (hyπ : OnPlane d.P y π) (hyl : OnLine d.L y l) (hwl : OnLine d.L w l)
    (hmove : marker π • w ≠ w) (hvfix : marker π • v = v)
    (hvw : Adj d.L v w) (hvy : v ≠ y) : Adj d.L v y := by
  classical
  have hzl : marker π • l = l :=
    d.core_fixes_lines y ⟨marker π, (d.marker_mem_core π y).mpr hyπ⟩ l hyl
  have hzwl : OnLine d.L (marker π • w) l := by
    simpa only [OnLine, hzl] using incident_smul (marker π) hwl
  have hvzw : Adj d.L v (marker π • w) := by
    simpa only [hvfix] using adj_smul (marker π) hvw
  have hwzw : Adj d.L w (marker π • w) := ⟨Ne.symm hmove, l, hwl, hzwl⟩
  obtain ⟨σ, hvσ, hwσ, hzwσ⟩ := d.triangles_in_plane v w (marker π • w) hvw hwzw (adj_symm hvzw)
  have hlσ := d.plane_closed w (marker π • w) l σ (Ne.symm hmove) hwl hzwl hwσ hzwσ
  obtain ⟨i, hi⟩ := d.plane_pair_types σ v l hvσ hlσ
  fin_cases i
  · exact (hvy ((d.marker_unique_fixed_on_line hyπ hyl hwl hmove hi).mp hvfix)).elim
  · exact hi y hyl
  · change {a | OnLine d.L a l ∧ Adj d.L v a}.ncard = 3 at hi
    let X := {a : Point d.P // OnLine d.L a l ∧ Adj d.L v a}
    let f : X → X := fun a => ⟨marker π • a.val, by
      constructor
      · simpa only [OnLine, hzl] using incident_smul (marker π) a.property.1
      · simpa only [hvfix] using adj_smul (marker π) a.property.2⟩
    have hf : Function.Involutive f := fun a => Subtype.ext (d.marker_involutive π a.val)
    obtain ⟨a, ha⟩ := three_involution_fixed (show Nat.card X = 3 from hi) f hf
    have hafix : marker π • a.val = a.val := congrArg Subtype.val ha
    have hay := (d.marker_unique_fixed_on_line hyπ hyl hwl hmove a.property.1).mp hafix
    exact hay ▸ a.property.2

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
