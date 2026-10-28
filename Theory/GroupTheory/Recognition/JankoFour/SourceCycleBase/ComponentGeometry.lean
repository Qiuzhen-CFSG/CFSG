module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.Native.PlaneOrbit
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.CommonOvals
/-!
# The component-distance argument and the ambient source base

Transport native (3.11.2) through the original Todd residue chart. The
coplanar, δ₃ disc, and δ₄ oval cases all retain the specified common-neighbor
component. Two subsets of at least three points on the same five-point line
prove (7.6.2), completing B2 and the original-involution proof of B3.
The nonabelian relation-chain reduction gives triangulability and the base
of the actual ambient uniqueness system, from the unchanged earlier-source
Input alone. Construction of that Input and section 8 comparison remain with
the source-recognition producer.

Source: Aschbacher–Segev (1991), (3.11.2), (7.4.1), (7.6), pp.596,604.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open SimpleGraph Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
namespace Input
variable (d : Input h)

/-- The native (3.11.2) under the same original Todd marking at x. -/
theorem residue_hits_plane {x : Point d.P} {σ π : Plane z}
    (hxσ : OnPlane d.P x σ) (hxπ : OnPlane d.P x π)
    (S : Finset Syntheme) (hS : Native.Polar.Oval S ∨ ∃ s, S = Native.Polar.disc s) :
    ∃ l : {l : Line d.L // OnLine d.L x l ∧ LineOnPlane d.L l σ},
      d.residue.flagLines x σ hxσ l ∈ S ∧ d.planeLineClose π x l.val := by
  let U := d.residue.planesAt x ⟨σ,hxσ⟩
  let P := d.residue.planesAt x ⟨π,hxπ⟩
  obtain ⟨l,hl,k,hk,hkl⟩ := Native.residue_hits_plane U P (ResidueChart.tetradLabel U) S hS
  let m := (d.residue.flagLinesNative x σ hxσ).symm l
  have he := (d.residue.flagLinesNative x σ hxσ).apply_symm_apply l
  have hm : d.residue.linesAt x ⟨m.val,m.property.1⟩ = l.val := congrArg Subtype.val he
  let n := (d.residue.linesAt x).symm k
  have hnk : d.residue.linesAt x n = k := (d.residue.linesAt x).apply_symm_apply k
  refine ⟨m,?_,n.val,n.property,?_,?_⟩
  · change Native.residueEquiv U _ (d.residue.flagLinesNative x σ hxσ m) ∈ S
    rw [he]
    exact hl
  · apply (d.residue.incidenceAt x n ⟨π,hxπ⟩).mpr
    simpa only [hnk] using hk
  · apply (d.coplanar_iff_native n ⟨m.val,m.property.1⟩).mpr
    simpa only [hnk,hm] using hkl

/-- The disc witness of (7.4.1), proved below from the earlier-source Input.
It concerns the specified common-neighbor component. -/
def DeltaThreeComponentDisc : Prop := ∀ x u y, d.ternary 2 x u y → ¬ d.ternary 1 x u y →
  ∃ (σ : Plane z) (hxσ : OnPlane d.P x σ) (s : Syntheme),
    ∀ l : {l : Line d.L // OnLine d.L x l ∧ LineOnPlane d.L l σ},
      d.residue.flagLines x σ hxσ l ∈ Native.Polar.disc s →
      ∃ v ∈ commonComponent (graph d.L) x u y, OnLine d.L v l.val

/-- AS91 (7.4.1) supplies the actual disc inside the originally chosen
common-neighbor component, with no additional input premise. -/
theorem deltaThreeComponentDisc : d.DeltaThreeComponentDisc := by
  intro x u y ht hn
  obtain ⟨π,hxπ,s,_,hs,hcomp,_⟩ := d.delta_three_common_disc ht hn
  refine ⟨π,hxπ,s,?_⟩
  intro l hl
  rw [←hs] at hl
  obtain ⟨v,hv⟩ := (d.mem_commonSynthemes hxπ _).mp hl
  have he : d.joiningLine v.property.2.1 = l.val :=
    congrArg Subtype.val ((d.residue.flagLines x π hxπ).injective hv)
  exact ⟨v.val,hcomp v.val v.property,he ▸ (d.joiningLine_incident v.property.2.1).2⟩

/-- The observation in (7.6), retaining the chosen common-neighbor component.
The δ₄ oval and the coplanar case are proved; the δ₃ disc is explicit. -/
theorem component_directions (three : d.DeltaThreeComponentDisc)
    {x u y : Point d.P} (hxy : DistanceTwo d.L x y)
    (hxu : Adj d.L x u) (huy : Adj d.L u y) :
    ∃ (σ : Plane z) (hxσ : OnPlane d.P x σ) (S : Finset Syntheme),
      (Native.Polar.Oval S ∨ ∃ s, S = Native.Polar.disc s) ∧
      ∀ l : {l : Line d.L // OnLine d.L x l ∧ LineOnPlane d.L l σ},
        d.residue.flagLines x σ hxσ l ∈ S →
        ∃ v ∈ commonComponent (graph d.L) x u y, OnLine d.L v l.val := by
  classical
  by_cases ht : d.ternary 2 x u y
  · by_cases hc : d.ternary 1 x u y
    · obtain ⟨σ,hxσ,huσ,hyσ⟩ := (d.coplanarStep_iff_plane hxu huy).mp hc.2.2
      refine ⟨σ,hxσ,Native.Polar.ovalTable 0,Or.inl (Native.Polar.ovalTable_oval 0),?_⟩
      intro l _
      have hcard := d.three_le_common_neighbors_on_line hxy hxσ hyσ l.property.1 l.property.2
      obtain ⟨v,hxv,hyv,hvl⟩ := Set.nonempty_of_ncard_ne_zero (by omega :
        {v | Adj d.L x v ∧ Adj d.L y v ∧ OnLine d.L v l.val}.ncard ≠ 0)
      refine ⟨v,?_,hvl⟩
      rw [d.planeDistanceTwo_component ⟨hxy,σ,hxσ,hyσ⟩ hxu huy]
      exact ⟨hxv,hyv⟩
    · obtain ⟨σ,hxσ,s,hit⟩ := three x u y ht hc
      exact ⟨σ,hxσ,Native.Polar.disc s,Or.inr ⟨s,rfl⟩,hit⟩
  · obtain ⟨σ,k,hxσ,hkσ,_,hkc,ho⟩ := d.component_oval_of_not_ternary_two hxu huy ht
    refine ⟨σ,hxσ,d.visibleSynthemes hxσ hkσ,Or.inl ho,?_⟩
    intro l hl
    obtain ⟨m,hm⟩ := (d.mem_visibleSynthemes hxσ hkσ _).mp hl
    have he : m.val = l.val := congrArg Subtype.val ((d.residue.flagLines x σ hxσ).injective hm)
    obtain ⟨v,hvk,_,_,hvm⟩ := m.property
    exact ⟨v,hkc v hvk,he ▸ hvm⟩

/-- AS91 (7.6.2) from its exact δ₃ disc observation. Two subsets of at
least three points intersect on the same literal five-point line. -/
theorem componentClose_of_deltaThree_disc (three : d.DeltaThreeComponentDisc) : d.ComponentClose := by
  intro x y w u hxy hxw hxu huw
  obtain ⟨hxy,π,hxπ,hyπ⟩ := hxy
  obtain ⟨σ,hxσ,S,hS,hit⟩ := d.component_directions three hxw hxu huw
  obtain ⟨l,hl,k,hxk,hkπ,hkl⟩ := d.residue_hits_plane hxσ hxπ S hS
  obtain ⟨v,hvc,hvl⟩ := hit l hl
  have hxv := (commonComponent_subset (graph d.L) x u w hvc).1
  let A := {c | Adj d.L x c ∧ Adj d.L y c ∧ OnLine d.L c k}
  let B := {c | OnLine d.L c k ∧ Adj d.L v c}
  have ha : 3 ≤ A.ncard := d.three_le_common_neighbors_on_line hxy hxπ hyπ hxk hkπ
  have hb : 3 ≤ B.ncard := d.three_le_neighbors_of_coplanar hxk l.property.1 hvl hxv.1 hkl
  have hcover : A ∪ B ⊆ {c | OnLine d.L c k} := by
    rintro c (ha|hb)
    · exact ha.2.2
    · exact hb.1
  have hc := Set.ncard_le_ncard hcover
  rw [d.line_card] at hc
  have hsum := Set.ncard_union_add_ncard_inter A B
  have hn : (A ∩ B).ncard ≠ 0 := by omega
  obtain ⟨c,hca,hcb⟩ := Set.nonempty_of_ncard_ne_zero hn
  exact ⟨c,v,hca.1,hca.2.1,hvc,Or.inr (adj_symm hcb.2)⟩

/-- The original conditional adapter, retaining its public interface.
The disc premise is now supplied by `deltaThreeComponentDisc`. -/
theorem isBase_of_deltaThree_disc (three : d.DeltaThreeComponentDisc) : d.system.IsBase :=
  d.isBase_of_componentClose (d.componentClose_of_deltaThree_disc three)
/-- AS91 (7.6.2), now with every source incidence premise discharged. -/
theorem componentClose : d.ComponentClose :=
  d.componentClose_of_deltaThree_disc d.deltaThreeComponentDisc

/-- AS91 (7.9): the actual nonabelian walk closure is generated by triangles. -/
theorem triangulable_of_input : WalkClosure.Triangulable d.system.graph :=
  d.triangulable_of_componentClose d.componentClose

/-- The base of the same literal ambient uniqueness system, from the
unchanged earlier-source incidence package. -/
theorem source_isBase : d.system.IsBase :=
  d.isBase_of_triangulable d.triangulable_of_input
end Input

/-- AS91 §7 for the actual system attached to the original type-J₄ witness.
The earlier-source Input is the sole extra premise; its existence and §8
comparison are retained by the source-recognition construction. -/
theorem source_isBase (h : IsTypeJ4 z) (d : Input h) : d.system.IsBase :=
  d.source_isBase

/-- The corresponding triangulability statement with the original witness. -/
theorem triangulable_of_input (h : IsTypeJ4 z) (d : Input h) :
    WalkClosure.Triangulable d.system.graph := d.triangulable_of_input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
