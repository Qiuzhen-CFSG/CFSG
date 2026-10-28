module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.FarGeometry
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.FarTransitivity

/-!
# Removing the far branch from the remaining base premises

The component distance bound (7.6.2) implies (7.6.1): use a nonneighbor
of x in the plane, then the triangle on the resulting close pair. Coplanar
paths already satisfy plane hitting by (7.5). For the final stage, the proved
far-component dichotomy either reduces within the same component to stage
two or supplies the needed plane hitting directly. Thus B2 now requires
only (7.4.2) for δ₃ and (7.6.2). The conditional triangulability and base
exports keep both remaining obligations explicit, outside Input.

Source: Aschbacher–Segev (1991), (7.4)–(7.7), (7.9), pp.603–605.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open SimpleGraph
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
namespace Input
variable (d : Input h)

/-- The remaining δ₃ hitting assertion, precisely the (7.4.2) conclusion
on Rhat₂ minus Rhat₁. It is an obligation of this family, not an Input field. -/
def DeltaThreePlaneHitting : Prop := ∀ x u y, d.ternary 2 x u y → ¬ d.ternary 1 x u y →
  ∃ π, OnPlane d.P x π ∧ OnPlane d.P u π ∧
    ∀ m, OnLine d.L x m → LineOnPlane d.L m π →
      ∃ w ∈ d.neighborhoodExtension 1 x u y, OnLine d.L w m

/-- The component bound (7.6.2) also implies the R₁ distance bound (7.6.1).
Choose a nonneighbor of x in the plane and apply ComponentClose to it. Any
chosen point on the line through the resulting common neighbor is R₁-close
to the same component, by the plane on the resulting triangle. -/
theorem plane_hitting_reaches_component (close : d.ComponentClose)
    {x v y : Point d.P} {π : Plane z} (hxπ : OnPlane d.P x π)
    (S : Set (Point d.P))
    (hit : ∀ m, OnLine d.L x m → LineOnPlane d.L m π → ∃ s ∈ S, OnLine d.L s m)
    (hxy : DistanceTwo d.L x y) (hxv : Adj d.L x v) (hvy : Adj d.L v y) :
    ∃ s q, s ∈ S ∧ q ∈ commonComponent (graph d.L) x v y ∧
      RelationReduction.induced (Γ := graph d.L) d.chain 1 s q := by
  have hnon : {b | OnPlane d.P b π ∧ b ≠ x ∧ ¬ Adj d.L x b}.Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by rw [d.plane_nonneighbor_card π x hxπ]; decide)
  obtain ⟨b,hbπ,hbx,hxb⟩ := hnon
  obtain ⟨a,_,hxa,hba,_,_⟩ := d.four_plane_points_common_neighbor hxπ hbπ hxπ hbπ
  have hxb2 : PlaneDistanceTwo d.L x b := ⟨⟨hbx.symm,hxb,a,hxa,adj_symm hba⟩,π,hxπ,hbπ⟩
  obtain ⟨c,q,hxc,hbc,hq,hcq⟩ := close x b y v hxb2 hxy hxv hvy
  have hcπ := d.common_neighbors_in_plane x b π hxb2.1 hxπ hbπ c hxc hbc
  let k := d.joiningLine hxc
  have hxk := (d.joiningLine_incident hxc).1
  have hck := (d.joiningLine_incident hxc).2
  have hkπ := d.plane_closed x c k π hxc.1 hxk hck hxπ hcπ
  obtain ⟨s,hs,hsk⟩ := hit k hxk hkπ
  refine ⟨s,q,hs,hq,?_⟩
  by_cases hsc : s = c
  · subst s
    exact Or.inl hcq
  have hsc' : Adj d.L s c := ⟨hsc,k,hsk,hck⟩
  obtain rfl | hcq := hcq
  · exact Or.inl (Or.inr hsc')
  · have hxq := (commonComponent_subset (graph d.L) x v y hq).1
    obtain ⟨σ,hxσ,hcσ,hqσ⟩ := d.triangles_in_plane x c q hxc hcq (adj_symm hxq)
    have hkσ := d.plane_closed x c k σ hxc.1 hxk hck hxσ hcσ
    have hsσ := d.string s k σ hsk hkσ
    exact Or.inr ⟨c,hsc',hcq,(d.coplanarStep_iff_plane hsc' hcq).mpr ⟨σ,hsσ,hcσ,hqσ⟩⟩

/-- The already proved (7.5) supplies the coplanar part of plane hitting.
Only the δ₃ difference remains in the explicit (7.4.2) premise. -/
theorem ternary_two_plane_hitting (three : d.DeltaThreePlaneHitting)
    {x u y : Point d.P} (ht : d.ternary 2 x u y)
    (hn : ¬ RelationReduction.Near (graph d.L) x y) :
    ∃ π, OnPlane d.P x π ∧ OnPlane d.P u π ∧
      ∀ m, OnLine d.L x m → LineOnPlane d.L m π →
        ∃ w ∈ d.neighborhoodExtension 1 x u y, OnLine d.L w m := by
  classical
  by_cases hc : d.ternary 1 x u y
  · obtain ⟨π,hxπ,huπ,hyπ⟩ := (d.coplanarStep_iff_plane hc.1 hc.2.1).mp hc.2.2
    have hd : DistanceTwo d.L x y :=
      ⟨fun he => hn (Or.inl he),fun ha => hn (Or.inr ha),u,ht.1,ht.2.1⟩
    have hp : PlaneDistanceTwo d.L x y := ⟨hd,π,hxπ,hyπ⟩
    refine ⟨π,hxπ,huπ,?_⟩
    intro m hxm hmπ
    have hb := d.three_le_common_neighbors_on_line hd hxπ hyπ hxm hmπ
    obtain ⟨w,hwx,hwy,hwm⟩ := Set.nonempty_of_ncard_ne_zero (by omega :
      {w | Adj d.L x w ∧ Adj d.L y w ∧ OnLine d.L w m}.ncard ≠ 0)
    refine ⟨w,Or.inl ?_,hwm⟩
    rw [d.planeDistanceTwo_component hp ht.1 ht.2.1]
    exact ⟨hwx,hwy⟩
  · exact three x u y ht hc

private theorem bridge_one (three : d.DeltaThreePlaneHitting) (close : d.ComponentClose)
    {x u y v w : Point d.P} (ht : d.ternary 2 x u y)
    (hn : ¬ RelationReduction.Near (graph d.L) x y)
    (hxv : Adj d.L x v) (hvw : Adj d.L v w)
    (hnw : ¬ RelationReduction.Near (graph d.L) x w) :
    ∃ a b, a ∈ d.neighborhoodExtension 1 x u y ∧
      b ∈ commonComponent (graph d.L) x v w ∧
        RelationReduction.induced (Γ := graph d.L) d.chain 1 a b := by
  obtain ⟨π,hxπ,_,hit⟩ := d.ternary_two_plane_hitting three ht hn
  exact d.plane_hitting_reaches_component close hxπ _ hit
    ⟨fun he => hnw (Or.inl he),fun ha => hnw (Or.inr ha),v,hxv,hvw⟩ hxv hvw

/-- All of B2 reduces to the δ₃ plane-hitting argument and ComponentClose.
The δ₄ branch is discharged by the native oval and nonfar-hitting theorems;
a lower middle vertex is carried within the original induced component. -/
theorem bridge_of_deltaThree_componentClose (three : d.DeltaThreePlaneHitting)
    (close : d.ComponentClose) : d.Bridge := by
  intro k hk x u y v w ht hn hxv hvw hnw
  interval_cases k
  · change d.ternary 1 x u y at ht
    change ∃ a b, a ∈ d.neighborhoodExtension 0 x u y ∧
      b ∈ commonComponent (graph d.L) x v w ∧
      RelationReduction.induced (Γ := graph d.L) d.chain 0 a b
    have hd : DistanceTwo d.L x y :=
      ⟨fun he => hn (Or.inl he),fun ha => hn (Or.inr ha),u,ht.1,ht.2.1⟩
    have hp := (d.binary_one_iff_planeDistanceTwo hd).mp ⟨u,ht⟩
    obtain ⟨a,b,hxa,hya,hb,hab⟩ := close x y w v hp
      ⟨fun he => hnw (Or.inl he),fun ha => hnw (Or.inr ha),v,hxv,hvw⟩ hxv hvw
    refine ⟨a,b,?_,hb,Or.inl hab⟩
    rw [d.neighborhoodExtension_zero,d.planeDistanceTwo_component hp ht.1 ht.2.1]
    exact ⟨hxa,hya⟩
  · exact d.bridge_one three close ht hn hxv hvw hnw
  · change d.ternary 3 x u y at ht
    change ∃ a b, a ∈ d.neighborhoodExtension 2 x u y ∧
      b ∈ commonComponent (graph d.L) x v w ∧
      RelationReduction.induced (Γ := graph d.L) d.chain 1 a b
    rcases d.component_lower_or_plane_hitting ht.1 ht.2.1 with ⟨c,hc,hct⟩ | ⟨π,hxπ,_,hit⟩
    · obtain ⟨a,b,ha,hb,hab⟩ := d.bridge_one three close hct hn hxv hvw hnw
      refine ⟨a,b,?_,hb,hab⟩
      rcases ha with ha | ⟨hxa,q,hq,hqt⟩
      · exact Or.inl (RelationReduction.commonComponent_trans hc ha)
      · exact Or.inr ⟨hxa,q,RelationReduction.commonComponent_trans hc hq,
          d.ternary_one_le_two hqt⟩
    · exact d.plane_hitting_reaches_component close hxπ _ hit
        ⟨fun he => hnw (Or.inl he),fun ha => hnw (Or.inr ha),v,hxv,hvw⟩ hxv hvw

/-- The same ambient graph, with the far B2 branch now proved. The two
remaining conclusions are (7.4.2) for δ₃ and (7.6.2). -/
theorem triangulable_of_deltaThree_componentClose (three : d.DeltaThreePlaneHitting)
    (close : d.ComponentClose) : WalkClosure.Triangulable d.system.graph :=
  d.triangulable_of_relation_conditions (d.bridge_of_deltaThree_componentClose three close)
    (d.tripleNeighbor_of_far_and_component d.farLineTransitive close)

/-- Actual uniqueness-system base under the two remaining source geometry
obligations. Neither obligation is inserted into Input. -/
theorem isBase_of_deltaThree_componentClose (three : d.DeltaThreePlaneHitting)
    (close : d.ComponentClose) : d.system.IsBase :=
  d.isBase_of_triangulable (d.triangulable_of_deltaThree_componentClose three close)

end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
