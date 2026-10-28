module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.PlaneMarker
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.RelationReduction.Application
/-!
# The original central-involution endgame

Native (3.8), transported to the actual point-plane residue, is exactly the
far-line transitivity condition below. Regularity of the point core extends
it to the other line points; conjugation of the literal marker proves (7.8).
The coplanar case of B3 is an intersection of two sets of at least three
points on a five-point line. In the other case, (7.6.2) provides a fixed
common neighbor, and the proved moved-line involution argument finishes B3.
The final theorem feeds these statements into the actual uniqueness-system
base. B2, native far-line transitivity and (7.6.2) remain explicit obligations;
none is a new field of the earlier-source Input.

Source: AS91 (3.8), (7.6.2), (7.8) and (7.9), pp.595,604–605.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open Subgroup SimpleGraph
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
namespace Input
variable (d : Input h)

def planeLineClose (π : Plane z) (x : Point d.P) (l : Line d.L) : Prop :=
  ∃ k, OnLine d.L x k ∧ LineOnPlane d.L k π ∧ Coplanar d.L k l

/-- The exact orbit statement needed from native (3.8), after the marked
point-plane residue transport. It does not assert anything about fixed points. -/
def FarLineTransitive : Prop := ∀ π x, OnPlane d.P x π → ∀ l m,
  OnLine d.L x l → OnLine d.L x m → ¬ d.planeLineClose π x l → ¬ d.planeLineClose π x m →
    ∃ g : G, g • x = x ∧ g • π = π ∧ g • l = m

/-- The component distance bound (7.6.2), keeping the source component. -/
def ComponentClose : Prop := ∀ x y w u, PlaneDistanceTwo d.L x y →
  DistanceTwo d.L x w → Adj d.L x u → Adj d.L u w →
    ∃ c v, Adj d.L x c ∧ Adj d.L y c ∧ v ∈ commonComponent (graph d.L) x u w ∧
      RelationReduction.Near (graph d.L) c v

theorem marker_fixes_smul {π : Plane z} {v : Point d.P} {g : G}
    (hg : g • π = π) (hv : marker π • v = v) : marker π • (g • v) = g • v := by
  have hc : g * marker π * g⁻¹ = marker π := by
    rw [← marker_smul, hg]
  calc
    marker π • (g • v) = (g * marker π * g⁻¹) • (g • v) := by rw [hc]
    _ = g • v := by simp only [mul_smul, inv_smul_smul, hv]

/-- AS91 (7.8), conditional only on its native (3.8) far-line orbit fact.
The fixed-point argument itself is proved using the actual plane marker. -/
theorem marker_fixed_iff_planeLineClose (far : d.FarLineTransitive)
    {π : Plane z} {x y : Point d.P} (hxπ : OnPlane d.P x π) (hxy : Adj d.L x y)
    {l : Line d.L} (hxl : OnLine d.L x l) (hyl : OnLine d.L y l) :
    marker π • y = y ↔ d.planeLineClose π x l := by
  classical
  have forward {v : Point d.P} {m : Line d.L} (hxv : Adj d.L x v)
      (hxm : OnLine d.L x m) (hvm : OnLine d.L v m)
      (hc : d.planeLineClose π x m) : marker π • v = v := by
    obtain ⟨k, hxk, hkπ, hkm⟩ := hc
    exact d.marker_fixes_of_coplanar_line hxπ hxv hxk hkπ hxm hvm hkm
  constructor
  · intro hyfix
    by_contra hn
    obtain ⟨v, hxv, hv⟩ := d.marker_moves_neighbor hxπ
    let m := d.joiningLine hxv
    have hxm : OnLine d.L x m := (d.joiningLine_incident hxv).1
    have hvm : OnLine d.L v m := (d.joiningLine_incident hxv).2
    have hnm : ¬ d.planeLineClose π x m := fun hc => hv (forward hxv hxm hvm hc)
    obtain ⟨g, hgx, hgπ, hgl⟩ := far π x hxπ l m hxl hxm hn hnm
    have hgym : OnLine d.L (g • y) m := by
      simpa only [OnLine, hgl] using incident_smul g hyl
    have hgyx : g • y ≠ x := by
      intro he
      exact hxy.1.symm ((MulAction.injective g) (he.trans hgx.symm))
    obtain ⟨e, he⟩ := d.core_transitive_other x m hxm (g • y) v hgym hgyx hvm hxv.1.symm
    have heπ := d.core_fixes_planes x e π hxπ
    have hfixed := d.marker_fixes_smul heπ (d.marker_fixes_smul hgπ hyfix)
    rw [he] at hfixed
    exact hv hfixed
  · exact forward hxy hxl hyl

/-- Coplanarity supplies at least three neighbors on the second line. -/
theorem three_le_neighbors_of_coplanar {y w : Point d.P} {l m : Line d.L}
    (hyl : OnLine d.L y l) (hym : OnLine d.L y m) (hwm : OnLine d.L w m)
    (hyw : y ≠ w) (hcop : Coplanar d.L l m) :
    3 ≤ {a | OnLine d.L a l ∧ Adj d.L w a}.ncard := by
  classical
  obtain ⟨i, hi, ht⟩ := (d.delta_coplanar y m l hym hyl).mp (by
    obtain ⟨π, hl, hm⟩ := hcop
    exact ⟨π, hm, hl⟩)
  have hin : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> simp_all
  rcases hin with rfl | rfl | rfl
  · have hlm := ((d.delta_zero y m l).mp ht).2
    have hwl : OnLine d.L w l := hlm.symm ▸ hwm
    let S := {a | OnLine d.L a l ∧ Adj d.L w a}
    have cover : {a | OnLine d.L a l} ⊆ S ∪ {w} := by
      intro a ha
      by_cases haw : a = w
      · exact Or.inr haw
      · exact Or.inl ⟨ha, ⟨Ne.symm haw, l, hwl, ha⟩⟩
    have hc := Set.ncard_le_ncard cover
    have hu := Set.ncard_union_le S {w}
    rw [d.line_card] at hc
    simp only [Set.ncard_singleton] at hu
    change 3 ≤ S.ncard
    omega
  · rw [d.delta_one_neighbors y w m l hym hwm hyw.symm ht]
  · have hall := d.delta_two_neighbors y w m l hym hwm hyw.symm ht
    have hs : {a | OnLine d.L a l ∧ Adj d.L w a} = {a | OnLine d.L a l} :=
      Set.ext fun a => ⟨fun ha => ha.1, fun ha => ⟨ha, hall a ha⟩⟩
    rw [hs, d.line_card]
    norm_num

/-- The easy, coplanar-line case of B3 in (7.9), from two subsets of size
at least three on the actual five-point line. -/
theorem tripleNeighbor_of_planeLineClose {x y w : Point d.P} {π : Plane z}
    (hxy : DistanceTwo d.L x y) (hxπ : OnPlane d.P x π) (hyπ : OnPlane d.P y π)
    (hyw : Adj d.L y w) (hc : d.planeLineClose π y (d.joiningLine hyw)) :
    ∃ c, Adj d.L x c ∧ Adj d.L y c ∧ Adj d.L c w := by
  obtain ⟨l, hyl, hlπ, hlm⟩ := hc
  let A := {c | Adj d.L y c ∧ Adj d.L x c ∧ OnLine d.L c l}
  let B := {c | OnLine d.L c l ∧ Adj d.L w c}
  have hyx : DistanceTwo d.L y x :=
    ⟨hxy.1.symm, fun h => hxy.2.1 (adj_symm h), by
      obtain ⟨u, hxu, huy⟩ := hxy.2.2
      exact ⟨u, adj_symm huy, adj_symm hxu⟩⟩
  have ha : 3 ≤ A.ncard := d.three_le_common_neighbors_on_line hyx hyπ hxπ hyl hlπ
  have hb : 3 ≤ B.ncard := d.three_le_neighbors_of_coplanar hyl
    (d.joiningLine_incident hyw).1 (d.joiningLine_incident hyw).2 hyw.1 hlm
  have hcover : A ∪ B ⊆ {c | OnLine d.L c l} := by
    rintro c (ha | hb)
    · exact ha.2.2
    · exact hb.1
  have hc := Set.ncard_le_ncard hcover
  rw [d.line_card] at hc
  have hsum := Set.ncard_union_add_ncard_inter A B
  have hn : 0 < (A ∩ B).ncard := by omega
  obtain ⟨c, hca, hcb⟩ := Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt hn)
  exact ⟨c, hca.2.1, hca.1, adj_symm hcb.2⟩

/-- The original involution proves B3 from exactly native (3.8) and the
already-identified component distance bound (7.6.2). -/
theorem tripleNeighbor_of_far_and_component (far : d.FarLineTransitive)
    (close : d.ComponentClose) : d.TripleNeighbor := by
  intro x y w hxy hyw hxw
  obtain ⟨hd, π, hxπ, hyπ⟩ := hxy
  classical
  by_cases hc : d.planeLineClose π y (d.joiningLine hyw)
  · obtain ⟨c, hxc, hyc, hcw⟩ := d.tripleNeighbor_of_planeLineClose hd hxπ hyπ hyw hc
    exact ⟨c, hxc, hyc, Or.inr hcw⟩
  have hmove : marker π • w ≠ w := fun hfix => hc
    ((d.marker_fixed_iff_planeLineClose far hyπ hyw
      (d.joiningLine_incident hyw).1 (d.joiningLine_incident hyw).2).mp hfix)
  obtain ⟨u, hxu, huw⟩ := hxw.2.2
  obtain ⟨c, v, hxc, hyc, hv, hcv⟩ := close x y w u ⟨hd, π, hxπ, hyπ⟩ hxw hxu huw
  have hxv := (commonComponent_subset (graph d.L) x u w hv).1
  have hvw := adj_symm (commonComponent_subset (graph d.L) x u w hv).2
  have hcπ := d.common_neighbors_in_plane x y π hd hxπ hyπ c hxc hyc
  have hvfix : marker π • v = v := by
    obtain rfl | hcv := hcv
    · exact d.marker_fixes_point hcπ
    · exact d.marker_fixes_of_two_plane_neighbors hxπ hcπ hxc.1 hxv hcv
  have hvy : v ≠ y := by
    rintro rfl
    exact hd.2.1 hxv
  have hneighbor := d.marker_fixed_neighbor_on_moved_line hyπ
    (d.joiningLine_incident hyw).1 (d.joiningLine_incident hyw).2 hmove hvfix hvw hvy
  exact ⟨v, hxv, adj_symm hneighbor, Or.inr hvw⟩

/-- The remaining incidence work feeds the actual ambient base consumer.
B2, native far-line transitivity, and (7.6.2) still require proof from Input. -/
theorem isBase_of_incidence_conditions (bridge : d.Bridge) (far : d.FarLineTransitive)
    (close : d.ComponentClose) : d.system.IsBase :=
  d.isBase_of_relation_conditions bridge (d.tripleNeighbor_of_far_and_component far close)

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
