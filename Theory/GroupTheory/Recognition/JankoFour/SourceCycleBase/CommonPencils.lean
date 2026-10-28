module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.PlanePencils
/-!
# Common-neighbor rechoice in the δ₃ associated plane

The δ₃ path determines a plane containing its first edge and a common δ₁
line. The other endpoint is outside every plane on the two endpoints.
The common neighbors in this plane are a clique in the originally selected
component. The native outside-line pencil and the triangle-label identity
supply the same marked pencil at every rechoice. Its three lines give the
bound 1 + 3 · 2 = 7 and the two δ₂ lines underlying the source ovals.

Source: Aschbacher–Segev (1991), proof of (7.4.1), pp.603–604.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open SimpleGraph Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
namespace Input
variable (d : Input h)

def planeCommon (x y : Point d.P) (π : Plane z) : Set (Point d.P) :=
  {v | OnPlane d.P v π ∧ Adj d.L x v ∧ Adj d.L y v}

/-- A plane common-neighbor clique stays in the originally chosen component. -/
theorem planeCommon_mem_component {x u y v : Point d.P} {π : Plane z}
    (hyπ : ¬ OnPlane d.P y π) (hu : u ∈ d.planeCommon x y π)
    (hv : v ∈ d.planeCommon x y π) : v ∈ commonComponent (graph d.L) x u y := by
  have huc := mem_commonComponent_self (graph d.L) hu.2.1 hu.2.2
  by_cases he : u = v
  · exact he ▸ huc
  · exact commonComponent_step (graph d.L) huc hv.2
      (d.common_neighbors_off_plane_clique hyπ hu.1 hv.1 hu.2.1 hu.2.2 hv.2.1 hv.2.2 he)

/-- Rechoosing a middle point in the plane preserves a δ₁ direction to
the outside endpoint line, by the actual triangle-label identity. -/
theorem planeCommon_rechoice {x u y v : Point d.P} {π : Plane z} {b k : Line d.L}
    (hyπ : ¬ OnPlane d.P y π) (hu : u ∈ d.planeCommon x y π)
    (hv : v ∈ d.planeCommon x y π)
    (hub : OnLine d.L u b) (hyb : OnLine d.L y b)
    (hbk : LineType d.residue 1 u b k) (hkπ : LineOnPlane d.L k π) :
    ∃ n, OnLine d.L v n ∧ LineOnPlane d.L n π ∧
      LineType d.residue 1 v (d.joiningLine hv.2.2) n := by
  have hbπ : ¬ LineOnPlane d.L b π := fun hh => hyπ (d.string y b π hyb hh)
  by_cases he : v = u
  · subst v
    have hb : d.joiningLine hu.2.2 = b := d.line_eq_of_incident hu.2.2.1
      (d.joiningLine_incident hu.2.2).1 (d.joiningLine_incident hu.2.2).2 hyb hub
    exact ⟨k,(lineType_incident hbk).2,hkπ,hb.symm ▸ hbk⟩
  · have huv := d.common_neighbors_off_plane_clique hyπ hu.1 hv.1
      hu.2.1 hu.2.2 hv.2.1 hv.2.2 (Ne.symm he)
    let n := d.joiningLine huv
    have hun := (d.joiningLine_incident huv).1
    have hvn := (d.joiningLine_incident huv).2
    have hnπ := d.plane_closed u v n π huv.1 hun hvn hu.1 hv.1
    obtain ⟨σ,hyσ,huσ,hvσ⟩ := d.triangles_in_plane y u v hu.2.2 huv (adj_symm hv.2.2)
    have hbσ := d.plane_closed y u b σ hu.2.2.1 hyb hub hyσ huσ
    have hnσ := d.plane_closed u v n σ huv.1 hun hvn huσ hvσ
    obtain ⟨a,ha⟩ := d.outside_plane_pencil hu.1 hbk hkπ hbπ
    have hbn : LineType d.residue 1 u b n :=
      (ha ⟨n,hun,hnπ⟩).2.mpr ((ha ⟨n,hun,hnπ⟩).1.mp ⟨σ,hbσ,hnσ⟩)
    exact ⟨n,hvn,hnπ,d.delta_one_at_common_on_line (adj_symm hu.2.2) hv.2.2
      hub hyb hun hvn hbn⟩

/-- The associated plane of a δ₃ path, with the original component and
all rechoices retained. No common plane of the endpoints exists. -/
theorem delta_three_plane_configuration {x u y : Point d.P}
    (ht : d.ternary 2 x u y) (hn : ¬ d.ternary 1 x u y) :
    ∃ π : Plane z, OnPlane d.P x π ∧ u ∈ d.planeCommon x y π ∧
      ¬ OnPlane d.P y π ∧ (¬ ∃ σ, OnPlane d.P x σ ∧ OnPlane d.P y σ) ∧
      (∀ v ∈ d.planeCommon x y π, v ∈ commonComponent (graph d.L) x u y) ∧
      ∀ v (hv : v ∈ d.planeCommon x y π), ∃ k,
        OnLine d.L v k ∧ LineOnPlane d.L k π ∧
        LineType d.residue 1 v (d.joiningLine hv.2.2) k := by
  have hxu := ht.1
  have huy := ht.2.1
  obtain ⟨a,b,hua,hxa,hub,hyb,hab⟩ := ht.2.2.resolve_left (fun hc => hn ⟨hxu,huy,hc⟩)
  obtain ⟨k,hak,hbk⟩ := d.delta_three_common_delta_one hab
  have huk := (lineType_incident hak).2
  obtain ⟨π,haπ,hkπ⟩ := (d.delta_coplanar u a k hua huk).mpr ⟨1,by decide,hak⟩
  have hxπ := d.string x a π hxa haπ
  have huπ := d.string u a π hua haπ
  have hyπ : ¬ OnPlane d.P y π := fun hyπ => hn
    ⟨hxu,huy,(d.coplanarStep_iff_plane hxu huy).mpr ⟨π,hxπ,huπ,hyπ⟩⟩
  have hxy : DistanceTwo d.L x y := by
    refine ⟨?_,?_,u,hxu,huy⟩
    · rintro rfl
      exact hyπ hxπ
    · intro hxy
      exact hn (d.ternary_zero_le_one ⟨hxu,huy,hxy⟩)
  have hnone : ¬ ∃ σ, OnPlane d.P x σ ∧ OnPlane d.P y σ := by
    rintro ⟨σ,hxσ,hyσ⟩
    have huσ := d.common_neighbors_in_plane x y σ hxy hxσ hyσ u hxu (adj_symm huy)
    exact hn ⟨hxu,huy,(d.coplanarStep_iff_plane hxu huy).mpr ⟨σ,hxσ,huσ,hyσ⟩⟩
  have hu : u ∈ d.planeCommon x y π := ⟨huπ,hxu,adj_symm huy⟩
  exact ⟨π,hxπ,hu,hyπ,hnone,fun v hv => d.planeCommon_mem_component hyπ hu hv,
    fun v hv => d.planeCommon_rechoice hyπ hu hv hub hyb hbk hkπ⟩

/-- Each rechoice has the two source ovals: their supporting lines lie in
the same plane and have exactly three common neighbors. -/
theorem planeCommon_two_lines {x y v : Point d.P} {π : Plane z}
    (hxπ : OnPlane d.P x π) (hv : v ∈ d.planeCommon x y π)
    (hnone : ¬ ∃ σ, OnPlane d.P x σ ∧ OnPlane d.P y σ)
    {k : Line d.L} (hkπ : LineOnPlane d.L k π)
    (hbk : LineType d.residue 1 v (d.joiningLine hv.2.2) k) :
    ∃ m n : {l : Line d.L // OnLine d.L v l ∧ LineOnPlane d.L l π},
      m ≠ n ∧ LineType d.residue 1 v m.val n.val ∧
      LineType d.residue 1 v (d.joiningLine hv.2.2) m.val ∧
      LineType d.residue 1 v (d.joiningLine hv.2.2) n.val ∧
      (∀ w, OnLine d.L w m.val → Adj d.L x w) ∧
      (∀ w, OnLine d.L w n.val → Adj d.L x w) ∧
      {w | OnLine d.L w m.val ∧ Adj d.L y w}.ncard = 3 ∧
      {w | OnLine d.L w n.val ∧ Adj d.L y w}.ncard = 3 := by
  let a := d.joiningLine hv.2.1
  let b := d.joiningLine hv.2.2
  have hxa := (d.joiningLine_incident hv.2.1).1
  have hva := (d.joiningLine_incident hv.2.1).2
  have hyb := (d.joiningLine_incident hv.2.2).1
  have hvb := (d.joiningLine_incident hv.2.2).2
  have haπ := d.plane_closed x v a π hv.2.1.1 hxa hva hxπ hv.1
  have hbπ : ¬ LineOnPlane d.L b π := fun hh => hnone ⟨π,hxπ,d.string y b π hyb hh⟩
  have hab : ¬ Coplanar d.L a b := by
    rintro ⟨σ,haσ,hbσ⟩
    exact hnone ⟨σ,d.string x a σ hxa haσ,d.string y b σ hyb hbσ⟩
  obtain ⟨m,n,hmn,ham,han,hbm,hbn,hmn'⟩ :=
    d.outside_plane_two_lines hv.1 hva haπ hbk hkπ hbπ hab
  exact ⟨m,n,hmn,hmn',hbm,hbn,d.delta_two_neighbors v x a m.val hva hxa hv.2.1.1 ham,
    d.delta_two_neighbors v x a n.val hva hxa hv.2.1.1 han,
    d.delta_one_neighbors v y b m.val hvb hyb hv.2.2.1 hbm,
    d.delta_one_neighbors v y b n.val hvb hyb hv.2.2.1 hbn⟩

/-- The common neighbors in the associated plane occupy at most three lines
through the chosen middle point, with at most two other points on each. -/
theorem planeCommon_card_le_seven {x u y : Point d.P} {π : Plane z} {k : Line d.L}
    (hyπ : ¬ OnPlane d.P y π) (hu : u ∈ d.planeCommon x y π)
    (hkπ : LineOnPlane d.L k π)
    (hbk : LineType d.residue 1 u (d.joiningLine hu.2.2) k) :
    (d.planeCommon x y π).ncard ≤ 7 := by
  classical
  let := Fintype.ofFinite (Point d.P)
  let b := d.joiningLine hu.2.2
  have hyb := (d.joiningLine_incident hu.2.2).1
  have hub := (d.joiningLine_incident hu.2.2).2
  have hbπ : ¬ LineOnPlane d.L b π := fun hh => hyπ (d.string y b π hyb hh)
  obtain ⟨a,ha⟩ := d.outside_plane_pencil hu.1 hbk hkπ hbπ
  let e := d.residue.flagLines u π hu.1
  let F : Syntheme → Finset (Point d.P) := fun s =>
    {w | OnLine d.L w (e.symm s).val ∧ Adj d.L y w}.toFinset.erase u
  have hc (s : Syntheme) (hs : s ∈ Native.Polar.pencil a) : (F s).card = 2 := by
    have hinc : incident a (e (e.symm s)) := by
      simpa only [Equiv.apply_symm_apply] using (Finset.mem_filter.mp hs).2
    have ht := (ha (e.symm s)).2.mpr hinc
    have hcard := d.delta_one_neighbors u y b (e.symm s).val hub hyb hu.2.2.1 ht
    have hmem : u ∈ {w | OnLine d.L w (e.symm s).val ∧ Adj d.L y w}.toFinset := by
      exact Set.mem_toFinset.mpr ⟨(e.symm s).property.1,hu.2.2⟩
    change ({w | OnLine d.L w (e.symm s).val ∧ Adj d.L y w}.toFinset.erase u).card = 2
    rw [Finset.card_erase_of_mem hmem,←Set.ncard_eq_toFinset_card',hcard]
  have hsub : (d.planeCommon x y π).toFinset ⊆
      insert u ((Native.Polar.pencil a).biUnion F) := by
    intro v hv
    have hv := Set.mem_toFinset.mp hv
    by_cases he : v = u
    · exact Finset.mem_insert.mpr (Or.inl he)
    · have huv := d.common_neighbors_off_plane_clique hyπ hu.1 hv.1
        hu.2.1 hu.2.2 hv.2.1 hv.2.2 (Ne.symm he)
      let n := d.joiningLine huv
      have hun := (d.joiningLine_incident huv).1
      have hvn := (d.joiningLine_incident huv).2
      have hnπ := d.plane_closed u v n π huv.1 hun hvn hu.1 hv.1
      obtain ⟨σ,hyσ,huσ,hvσ⟩ := d.triangles_in_plane y u v hu.2.2 huv (adj_symm hv.2.2)
      have hbσ := d.plane_closed y u b σ hu.2.2.1 hyb hub hyσ huσ
      have hnσ := d.plane_closed u v n σ huv.1 hun hvn huσ hvσ
      let N : {l : Line d.L // OnLine d.L u l ∧ LineOnPlane d.L l π} := ⟨n,hun,hnπ⟩
      have hs := (ha N).1.mp ⟨σ,hbσ,hnσ⟩
      apply Finset.mem_insert.mpr ∘ Or.inr
      refine Finset.mem_biUnion.mpr ⟨e N,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩,?_⟩
      apply Finset.mem_erase.mpr
      refine ⟨he,Set.mem_toFinset.mpr ⟨?_,hv.2.2⟩⟩
      simpa only [Equiv.symm_apply_apply] using hvn
  have hle := Finset.card_le_card hsub
  have hi := Finset.card_insert_le u ((Native.Polar.pencil a).biUnion F)
  have hu := Finset.card_biUnion_le (s := Native.Polar.pencil a) (t := F)
  have hsum : ∑ s ∈ Native.Polar.pencil a, (F s).card = 6 := by
    rw [Finset.sum_congr rfl hc]
    simp [Native.Polar.pencil_card]
  rw [hsum] at hu
  rw [Set.ncard_eq_toFinset_card']
  omega
end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
