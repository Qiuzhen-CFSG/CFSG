module
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.ResidueHitting
public import Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase.RelationReduction.Application

/-!
# The far component and its oval

The native common δ₂ line lies wholly in the chosen common-neighbor
component and gives the oval of AS91 (7.6). An oval selects a δ₂ direction
relative to any line of its plane. Applying (3.11.1) again gives the D₂
hitting assertion whenever the component has no lower-stage middle vertex.
The final dichotomy is the form needed by B2: if a lower middle exists,
the level-two case applies inside that same component instead.

Source: Aschbacher–Segev (1991), (7.6), (7.7), pp.604–605.
-/
@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
open SimpleGraph Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsTypeJ4 z}
namespace Input
variable (d : Input h)

/-- A δ₄ path has a five-point line entirely inside its chosen common-neighbor
component. Its visible lines are the oval used in (7.6) and (7.7). -/
theorem delta_four_component_oval {x u y : Point d.P} {l m : Line d.L}
    (hxu : Adj d.L x u) (huy : Adj d.L u y)
    (hul : OnLine d.L u l) (hxl : OnLine d.L x l)
    (hum : OnLine d.L u m) (hym : OnLine d.L y m)
    (ht : LineType d.residue 4 u l m) :
    ∃ (π : Plane z) (k : Line d.L) (hxπ : OnPlane d.P x π)
      (hkπ : LineOnPlane d.L k π), OnPlane d.P u π ∧
      (∀ v, OnLine d.L v k → v ∈ commonComponent (graph d.L) x u y) ∧
      Native.Polar.Oval (d.visibleSynthemes hxπ hkπ) := by
  obtain ⟨k,hlk,hmk⟩ := d.delta_four_common_delta_two ht
  have huk := (lineType_incident hlk).2
  obtain ⟨π,hlπ,hkπ⟩ := (d.delta_coplanar u l k hul huk).mpr ⟨2,by decide,hlk⟩
  have hxπ := d.string x l π hxl hlπ
  have huπ := d.string u l π hul hlπ
  have hxall := d.delta_two_neighbors u x l k hul hxl hxu.1 hlk
  have hyall := d.delta_two_neighbors u y m k hum hym huy.1.symm hmk
  refine ⟨π,k,hxπ,hkπ,huπ,?_,d.lineView_five_oval hxπ hkπ hxall⟩
  intro v hv
  by_cases he : v = u
  · subst v
    exact mem_commonComponent_self (graph d.L) hxu (adj_symm huy)
  · exact commonComponent_step (graph d.L)
      (mem_commonComponent_self (graph d.L) hxu (adj_symm huy))
      ⟨hxall v hv,hyall v hv⟩ ⟨Ne.symm he,k,huk,hv⟩

theorem delta_four_of_not_ternary_two {x u y : Point d.P}
    (hxu : Adj d.L x u) (huy : Adj d.L u y) (hn : ¬ d.ternary 2 x u y) :
    LineType d.residue 4 u (d.joiningLine hxu) (d.joiningLine huy) := by
  by_contra ht
  exact hn (d.ternary_two_of_not_delta_four hxu huy
    (d.joiningLine_incident hxu).2 (d.joiningLine_incident hxu).1
    (d.joiningLine_incident huy).1 (d.joiningLine_incident huy).2 ht)

/-- The far branch of the observation in (7.6), with membership in CΔ
rather than just the full common-neighbor set. -/
theorem component_oval_of_not_ternary_two {x u y : Point d.P}
    (hxu : Adj d.L x u) (huy : Adj d.L u y) (hn : ¬ d.ternary 2 x u y) :
    ∃ (π : Plane z) (k : Line d.L) (hxπ : OnPlane d.P x π)
      (hkπ : LineOnPlane d.L k π), OnPlane d.P u π ∧
      (∀ v, OnLine d.L v k → v ∈ commonComponent (graph d.L) x u y) ∧
      Native.Polar.Oval (d.visibleSynthemes hxπ hkπ) :=
  d.delta_four_component_oval hxu huy
    (d.joiningLine_incident hxu).2 (d.joiningLine_incident hxu).1
    (d.joiningLine_incident huy).1 (d.joiningLine_incident huy).2
    (d.delta_four_of_not_ternary_two hxu huy hn)

private theorem oval_has_noncollinear {S : Finset Syntheme} (hS : Native.Polar.Oval S)
    (t : Syntheme) : ∃ s ∈ S, s ≠ t ∧ ¬ synthemeCollinear s t := by
  obtain ⟨i,rfl⟩ := Native.Polar.ovalTable_complete hS
  have hc : ∀ (i : Fin 6) (t : Syntheme), ∃ s ∈ Native.Polar.ovalTable i,
      s ≠ t ∧ ¬ synthemeCollinear s t := by decide
  exact hc i t

/-- An oval visible from k supplies a δ₂ direction relative to any line
of the point-plane flag. -/
theorem oval_visible_delta_two {x : Point d.P} {π : Plane z} {k m : Line d.L}
    (hxπ : OnPlane d.P x π) (hkπ : LineOnPlane d.L k π)
    (ho : Native.Polar.Oval (d.visibleSynthemes hxπ hkπ))
    (hxm : OnLine d.L x m) (hmπ : LineOnPlane d.L m π) :
    ∃ v n, OnLine d.L v k ∧ Adj d.L x v ∧ OnLine d.L x n ∧ OnLine d.L v n ∧
      LineType d.residue 2 x n m := by
  obtain ⟨s,hs,hne,hnc⟩ := oval_has_noncollinear ho
    (d.residue.flagLines x π hxπ ⟨m,hxm,hmπ⟩)
  obtain ⟨n,rfl⟩ := (d.mem_visibleSynthemes hxπ hkπ s).mp hs
  obtain ⟨v,hvk,hxv,hxn,hvn⟩ := n.property
  have hnπ := (d.lineView_in_plane hxπ hkπ n.property).2
  have hnm : n.val ≠ m := by
    intro he
    apply hne
    exact congrArg (d.residue.flagLines x π hxπ) (Subtype.ext he)
  have hnt : ¬ LineType d.residue 1 x n.val m := by
    intro ht
    exact hnc ((d.residue.flagLines_collinear_iff x π hxπ
      ⟨n.val,d.lineView_in_plane hxπ hkπ n.property⟩ ⟨m,hxm,hmπ⟩).mpr ht)
  obtain ⟨i,hi,ht⟩ := (d.delta_coplanar x n.val m hxn hxm).mp ⟨π,hnπ,hmπ⟩
  have htype : LineType d.residue 2 x n.val m := by
    fin_cases i
    · exact (hnm ((d.delta_zero x n.val m).mp ht).2.symm).elim
    · exact (hnt ht).elim
    · exact ht
    · norm_num at hi
    · norm_num at hi
  exact ⟨v,n.val,hvk,hxv,hxn,hvn,htype⟩

/-- The far branch of (7.7) when the chosen component has no lower-stage
middle vertex. This form avoids silently replacing CΔ by all common neighbors. -/
theorem far_component_plane_hitting {x u y : Point d.P}
    (hxu : Adj d.L x u) (huy : Adj d.L u y)
    (hfar : ∀ v ∈ commonComponent (graph d.L) x u y, ¬ d.ternary 2 x v y) :
    ∃ π, OnPlane d.P x π ∧ OnPlane d.P u π ∧
      ∀ m, OnLine d.L x m → LineOnPlane d.L m π →
        ∃ w ∈ d.neighborhoodExtension 2 x u y, OnLine d.L w m := by
  have hnu := hfar u (mem_commonComponent_self (graph d.L) hxu (adj_symm huy))
  obtain ⟨π,k,hxπ,hkπ,huπ,hkc,ho⟩ := d.component_oval_of_not_ternary_two hxu huy hnu
  refine ⟨π,hxπ,huπ,?_⟩
  intro m hxm hmπ
  obtain ⟨v,n,hvk,hxv,hxn,hvn,hnm⟩ := d.oval_visible_delta_two hxπ hkπ ho hxm hmπ
  have hvc := hkc v hvk
  have hyv := (commonComponent_subset (graph d.L) x u y hvc).2
  have hvπ := d.string v k π hvk hkπ
  have hm_all := d.delta_two_neighbors x v n m hxn hvn hxv.1.symm hnm
  have hov := d.lineView_five_oval hvπ hmπ hm_all
  let vy := d.joiningLine hyv
  obtain ⟨q,hq,hqfar⟩ := d.residue_hits_nonfar hvπ _ (Or.inl hov)
    (d.joiningLine_incident hyv).2
  have hqm : d.residue.flagLines v π hvπ q ∈ d.visibleSynthemes hvπ hmπ := hq
  obtain ⟨a,ha⟩ := (d.mem_visibleSynthemes hvπ hmπ _).mp hqm
  have haq : a.val = q.val := by
    exact congrArg Subtype.val ((d.residue.flagLines v π hvπ).injective ha)
  obtain ⟨w,hwm,hvw,hva,hwa⟩ := a.property
  have ht : d.ternary 2 y v w := d.ternary_two_of_not_delta_four hyv hvw
    (d.joiningLine_incident hyv).2 (d.joiningLine_incident hyv).1 hva hwa
    (by simpa only [haq] using hqfar)
  have hwx : w ≠ x := by
    rintro rfl
    exact hfar v hvc (d.ternary_two_symm ht)
  exact ⟨w,Or.inr ⟨⟨hwx.symm,m,hxm,hwm⟩,v,hvc,ht⟩,hwm⟩

/-- The last-stage dichotomy used in B2: either the same component already
has a level-two middle vertex, or its D₂ meets every line of a plane through x. -/
theorem component_lower_or_plane_hitting {x u y : Point d.P}
    (hxu : Adj d.L x u) (huy : Adj d.L u y) :
    (∃ v ∈ commonComponent (graph d.L) x u y, d.ternary 2 x v y) ∨
      ∃ π, OnPlane d.P x π ∧ OnPlane d.P u π ∧
        ∀ m, OnLine d.L x m → LineOnPlane d.L m π →
          ∃ w ∈ d.neighborhoodExtension 2 x u y, OnLine d.L w m := by
  classical
  by_cases hl : ∃ v ∈ commonComponent (graph d.L) x u y, d.ternary 2 x v y
  · exact Or.inl hl
  · exact Or.inr (d.far_component_plane_hitting hxu huy (by simpa using hl))
end Input
end Theory.GroupTheory.Recognition.JankoFour.SourceCycleBase
