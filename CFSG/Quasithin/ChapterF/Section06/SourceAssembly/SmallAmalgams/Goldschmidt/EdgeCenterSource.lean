module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.RadiusOneSource
public import Theory.GroupTheory.PGroup.UniqueInvolution

/-!
# Cyclic edge centers in the original large source action

All central involutions on an edge have the same center vertex and radius.
Two different ones would have a product fixing one more vertex, contradicting
the exact interval. Thus the finite abelian edge center has a unique
involution and is cyclic. The radius-one obstruction is discharged by the
original source action.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.8),
printed pp.399--400.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem equal_margins (h : CubicTreeAction F) {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z) (hw : d.centralRight-d.centralLeft=2)
    (he : Even (d.fixedRight-d.fixedLeft)) : d.leftMargin=d.rightMargin := by
  have hm := h.central_margin_comparison hs hshort t hz hz d d
  have hl := d.leftMargin_cast
  have hr := d.rightMargin_cast
  obtain ⟨k,hk⟩ := he
  omega

private theorem equal_radius (h : CubicTreeAction F) {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z u : G}
    (hz : t.CentralInvolution z) (hu : t.CentralInvolution u)
    (d : t.CentralInterval z) (e : t.CentralInterval u)
    (hdw : d.centralRight-d.centralLeft=2) (hew : e.centralRight-e.centralLeft=2)
    (hdm : d.leftMargin=d.rightMargin) (hem : e.leftMargin=e.rightMargin)
    (hc : d.centralLeft=e.centralLeft)
    (hdr : d.rightMargin=2 ∨ (Odd d.rightMargin ∧ 3≤d.rightMargin))
    (her : e.rightMargin=2 ∨ (Odd e.rightMargin ∧ 3≤e.rightMargin)) :
    d.rightMargin=e.rightMargin := by
  have hm := h.central_margin_comparison hs hshort t hz hu d e
  have hdl := d.leftMargin_cast
  have hdr' := d.rightMargin_cast
  have hel := e.leftMargin_cast
  have her' := e.rightMargin_cast
  have exclude {z u : G} (hz : t.CentralInvolution z) (hu : t.CentralInvolution u)
      (d : t.CentralInterval z) (e : t.CentralInterval u)
      (hdw : d.centralRight-d.centralLeft=2) (hew : e.centralRight-e.centralLeft=2)
      (hdm : d.leftMargin=d.rightMargin) (hem : e.leftMargin=e.rightMargin)
      (hc : d.centralLeft=e.centralLeft) (hdr : d.rightMargin=2) (her : e.rightMargin=3) :
      False := by
    have hdl := d.leftMargin_cast
    have hdr' := d.rightMargin_cast
    have hel := e.leftMargin_cast
    have her' := e.rightMargin_cast
    let f := e.shift 2
    have hb := (h.central_boundaries_iff hs hshort t hz (hu.shift 2) d f).mpr (by
      dsimp only [f, Track.CentralInterval.shift]
      omega)
    dsimp only [f, Track.CentralInterval.shift] at hb
    omega
  rcases hdr with hdr | ⟨⟨k,hk⟩,hkr⟩ <;>
    rcases her with her | ⟨⟨l,hl⟩,hlr⟩
  · omega
  · exact (exclude hz hu d e hdw hew hdm hem hc hdr (by omega)).elim
  · exact (exclude hu hz e d hew hdw hem hdm hc.symm her (by omega)).elim
  · omega

private theorem unique_central_involution
    (h : CubicTreeAction F) {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G)
    (hfinite : ∀ u, t.CentralInvolution u → u ∉ t.fixer)
    (hwidth : ∀ u, t.CentralInvolution u → ∀ d : t.CentralInterval u,
      d.centralRight-d.centralLeft=2)
    (heven : ∀ u, t.CentralInvolution u → ∀ d : t.CentralInterval u,
      Even (d.fixedRight-d.fixedLeft))
    (hradius : ∀ u, t.CentralInvolution u → ∀ d : t.CentralInterval u,
      d.rightMargin=2 ∨ (Odd d.rightMargin ∧ 3≤d.rightMargin))
    {z : G} (hz : t.CentralInvolution z) (d : t.CentralInterval z)
    (hcenter : ∀ u (_hu : t.CentralInvolution u) (e : t.CentralInterval u),
      t.CentralEdge u (d.centralLeft+1) → e.centralLeft=d.centralLeft)
    {u : G} (hu : orderOf u=2) (hue : t.CentralEdge u (d.centralLeft+1)) : u=z := by
  by_contra hne
  have hu' : t.CentralInvolution u := ⟨hu,⟨_,hue⟩⟩
  obtain ⟨e⟩ := h.exists_centralInterval_of_not_mem_fixer t u hu' (hfinite u hu')
  have hec := hcenter u hu' e hue
  have hdw := hwidth z hz d
  have hew := hwidth u hu' e
  have hdm := equal_margins h hs hshort t hz d hdw (heven z hz d)
  have hem := equal_margins h hs hshort t hu' e hew (heven u hu' e)
  have her := equal_radius h hs hshort t hz hu' d e hdw hew hdm hem
    hec.symm (hradius z hz d) (hradius u hu' e)
  have hzedge := d.central (d.centralLeft+1) (by omega) (by omega)
  have hcomm := hzedge.2 u hue.1
  have hz2 : z^2=1 := (orderOf_eq_prime_iff.mp hz.1).1
  have hu2 : u^2=1 := (orderOf_eq_prime_iff.mp hu).1
  have hprod2 : orderOf (z*u)=2 := by
    apply orderOf_eq_prime
    · rw [hcomm.mul_pow, hz2, hu2, one_mul]
    · intro he
      apply hne
      have hh := congrArg (z * ·) he
      simpa only [← mul_assoc, ← pow_two, hz2, one_mul, mul_one] using hh
  have hprodedge : t.CentralEdge (z*u) (d.centralLeft+1) :=
    ⟨(t.edgeStabilizer _).mul_mem hzedge.1 hue.1,
      fun x hx => (hzedge.2 x hx).mul_left (hue.2 x hx)⟩
  have hprod : t.CentralInvolution (z*u) := ⟨hprod2,⟨_,hprodedge⟩⟩
  obtain ⟨f⟩ := h.exists_centralInterval_of_not_mem_fixer t (z*u) hprod (hfinite _ hprod)
  have hfc := hcenter (z*u) hprod f hprodedge
  have hfw := hwidth (z*u) hprod f
  have hfm := equal_margins h hs hshort t hprod f hfw (heven _ hprod f)
  have hfr := equal_radius h hs hshort t hz hprod d f hdw hfw hdm hfm
    hfc.symm (hradius z hz d) (hradius _ hprod f)
  have hdl := d.leftMargin_cast
  have hdr := d.rightMargin_cast
  have hel := e.leftMargin_cast
  have her' := e.rightMargin_cast
  have hfl := f.leftMargin_cast
  have hfr' := f.rightMargin_cast
  have hdL := d.centralLeft_mem
  have hdR := d.centralRight_mem
  have hL : e.fixedLeft=d.fixedLeft := by omega
  have hR : e.fixedRight=d.fixedRight := by omega
  have hadj : (RankTwo.graph F).Adj (t.vertex (d.fixedRight-1)) (t.vertex d.fixedRight) := by
    simpa only [sub_add_cancel] using t.adjacent (d.fixedRight-1)
  let p : BasedWalk (RankTwo.graph F) 1 (t.vertex (d.fixedRight-1)) :=
    ⟨⟨t.vertex d.fixedRight,hadj⟩,PUnit.unit⟩
  have hfix (w : G) (dw : t.CentralInterval w)
      (hwL : dw.fixedLeft=d.fixedLeft) (hwR : dw.fixedRight=d.fixedRight) :
      ∀ v ∈ p.vertices, w • v=v := by
    change ∀ v ∈ [t.vertex (d.fixedRight-1),t.vertex d.fixedRight], w • v=v
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact (dw.fixed_iff _).2 ⟨by omega,by omega⟩
    · obtain rfl := List.mem_singleton.mp hv
      exact (dw.fixed_iff _).2 ⟨by omega,by omega⟩
  have hmove (w : G) (dw : t.CentralInterval w) (hwR : dw.fixedRight=d.fixedRight) :
      w • t.vertex (d.fixedRight+1) ≠ t.vertex (d.fixedRight+1) := by
    intro hh
    have hf := (dw.fixed_iff _).mp hh
    omega
  have hforward : Forward p (t.vertex (d.fixedRight+1)) := by
    refine ⟨t.adjacent _,?_⟩
    intro hh
    have hi := t.injective hh
    omega
  have hfixprod := forward_mul_fixes_of_both_move trackGraphAction p
    (h.card_neighbor _) z u (hfix z d rfl rfl) (hfix u e hL hR) hforward
    (hmove z d rfl) (hmove u e hR)
  have hh := (f.fixed_iff _).mp hfixprod
  omega

private theorem edge_equiv_overlap {a b : RankTwo.Vertex F}
    (hab : (RankTwo.graph F).Adj a b) :
    Nonempty ((F false ⊓ F true : Subgroup G) ≃* (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b : Subgroup G)) := by
  obtain ⟨g,ha,hb⟩ := RankTwo.incident_common_translate F hab.2
  have he : (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b) =
      (F a.type ⊓ F b.type).map (MulAut.conj g).toMonoidHom := by
    calc
      _ = RankTwo.stabilizer F (g • RankTwo.base F a.type) ⊓
          RankTwo.stabilizer F (g • RankTwo.base F b.type) := by rw [ha,hb]
      _ = _ := by
        rw [RankTwo.stabilizer, RankTwo.stabilizer, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
          MulAction.stabilizer_smul_eq_stabilizer_map_conj,
          ← Subgroup.map_inf _ _ _ (MulAut.conj g).injective]
        congr 1
        simp only [RankTwo.base, stabilizer_base]
  have hbase : F a.type ⊓ F b.type = F false ⊓ F true := by
    have ht := hab.1
    cases ha : a.type <;> cases hb : b.type <;> simp_all only [ne_eq, not_true_eq_false, inf_comm]
  rw [hbase] at he
  exact ⟨((MulAut.conj g).subgroupMap (F false ⊓ F true)).trans
    (MulEquiv.subgroupCongr he.symm)⟩

private theorem cyclic_center_all_edges
    {a b : RankTwo.Vertex F} (hab : (RankTwo.graph F).Adj a b)
    (hc : IsCyclic (Subgroup.center (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b : Subgroup G))) :
    ∀ {v w : RankTwo.Vertex F}, (RankTwo.graph F).Adj v w →
      IsCyclic (Subgroup.center (RankTwo.stabilizer F v ⊓ RankTwo.stabilizer F w : Subgroup G)) := by
  obtain ⟨e⟩ := edge_equiv_overlap hab
  intro v w hvw
  obtain ⟨f⟩ := edge_equiv_overlap hvw
  exact (centerCongr (e.symm.trans f)).isCyclic.mp hc


private theorem central_left_eq_of_common_edge
    {s : ℕ} (h : LargeTreeSource F s) (t : Track (RankTwo.graph F) G)
    (hfinite : ∀ u, t.CentralInvolution u → u ∉ t.fixer)
    (hwidth : ∀ u, t.CentralInvolution u → ∀ d : t.CentralInterval u,
      d.centralRight-d.centralLeft=2)
    {z u : G} (hz : t.CentralInvolution z) (hu : t.CentralInvolution u)
    (d : t.CentralInterval z) (e : t.CentralInterval u)
    (hue : t.CentralEdge u (d.centralLeft+1)) : e.centralLeft=d.centralLeft := by
  let ht := h.action.toCubicTreeAction
  have hdw := hwidth z hz d
  have hew := hwidth u hu e
  have he := (ht.centralEdge_iff_in_centralInterval h.five_le h.regular t hu e _).1 hue
  by_contra hne
  have hshift : e.centralLeft=d.centralLeft+1 := by omega
  have hzc := ht.centralizes_vertex_of_two_centralEdges
    (by have := h.five_le; omega) h.regular t (d.centralLeft+1)
    (by simpa only [add_sub_cancel_right] using d.central d.centralLeft le_rfl d.central_lt)
    (d.central (d.centralLeft+1) (by omega) (by omega))
  have huc := ht.centralizes_vertex_of_two_centralEdges
    (by have := h.five_le; omega) h.regular t (d.centralLeft+1+1)
    (e.central (d.centralLeft+1+1-1) (by omega) (by omega))
    (e.central (d.centralLeft+1+1) (by omega) (by omega))
  exact no_adjacent_central_involutions_on_track h t hfinite hwidth
    (d.centralLeft+1) hz.1 hu.1
    (d.central (d.centralLeft+1) (by omega) (by omega)).1 hue.1 hzc huc

/-- The original source hypotheses force cyclicity of every edge center.
The finite local groups suffice; the ambient tree group need not be finite. -/
theorem LargeTreeSource.edge_center_cyclic
    {s : ℕ} (h : LargeTreeSource F s) {v : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) s v) (hp : p.Nonbacktracking)
    (hn : ¬ RightRegular (A := G) p) (hv : v.type=false) :
    ∀ (a b : RankTwo.Vertex F), (RankTwo.graph F).Adj a b →
      IsCyclic (Subgroup.center (RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b : Subgroup G)) := by
  let ht := h.action.toCubicTreeAction
  obtain ⟨t,h0,h1,href⟩ := ht.exists_preferred_track
  have hfinite : ∀ u, t.CentralInvolution u → u ∉ t.fixer :=
    ht.centralInvolution_not_mem_trackFixer h.not_cubic h.not_alternating t h0 h1
      h.five_le h.odd h.regular p hp hn hv
  have hwidth : ∀ u, t.CentralInvolution u → ∀ d : t.CentralInterval u,
      d.centralRight-d.centralLeft=2 := fun u hu d =>
    ht.centralInterval_length_eq_two h.five_le h.regular p hp hn
      h.not_cubic h.not_alternating t hfinite href hu d
  have heven : ∀ u, t.CentralInvolution u → ∀ d : t.CentralInterval u,
      Even (d.fixedRight-d.fixedLeft) := fun u hu d =>
    ht.centralInterval_fixedLength_even h.five_le h.regular p hp hn
      h.not_cubic h.not_alternating t hfinite href hu d
  have hradius : ∀ u, t.CentralInvolution u → ∀ d : t.CentralInterval u,
      d.rightMargin=2 ∨ Odd d.rightMargin ∧ 3≤d.rightMargin := by
    intro u hu d
    have hne := h.centralInterval_rightMargin_ne_one p hp hn hv t hfinite href hu d
    rcases Nat.even_or_odd d.rightMargin with he | ho
    · exact Or.inl (ht.centered_even_radius_eq_two h.five_le h.regular
        h.not_cubic h.not_alternating t hfinite hu d (hwidth u hu d)
        (equal_margins ht h.five_le h.regular t hu d (hwidth u hu d) (heven u hu d)) he)
    · have hpos := (ht.centralInterval_chiefBounds_of_large_residual
        h.not_cubic h.not_alternating t hu d).2.2.1
      exact Or.inr ⟨ho, by obtain ⟨k,hk⟩ := ho; omega⟩
  obtain ⟨z,hz⟩ := h.exists_centralInvolution t h0 h1
  obtain ⟨d⟩ := ht.exists_centralInterval_of_not_mem_fixer t z hz (hfinite z hz)
  let a := t.vertex (d.centralLeft+1)
  let b := t.vertex (d.centralLeft+1+1)
  have hab : (RankTwo.graph F).Adj a b := t.adjacent (d.centralLeft+1)
  let E := RankTwo.stabilizer F a ⊓ RankTwo.stabilizer F b
  let : Finite (RankTwo.stabilizer F a) := ht.finite_stabilizer a
  let : Finite E := Finite.of_injective (Subgroup.inclusion
    (show E ≤ RankTwo.stabilizer F a from inf_le_left)) (Subgroup.inclusion_injective _)
  obtain ⟨eE⟩ := edge_equiv_overlap hab
  have hE : IsPGroup 2 E := ht.primitive.sylow.isPGroup.of_equiv eE
  have hedge : t.CentralEdge z (d.centralLeft+1) :=
    d.central (d.centralLeft+1) (by omega) (by have := hwidth z hz d; omega)
  let zE : E := ⟨z,hedge.1⟩
  have hzE : zE ∈ Subgroup.center E := mem_center_iff.mpr fun x =>
    Subtype.ext (hedge.2 x x.property).symm.eq
  let zZ : Subgroup.center E := ⟨zE,hzE⟩
  have hzZ : orderOf zZ=2 := by
    rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    exact hz.1
  have hcyclic : IsCyclic (Subgroup.center E) :=
    (hE.to_subgroup _).isCyclic_of_unique_involution_of_isMulCommutative ⟨zZ,hzZ,by
      intro u hu
      apply Subtype.ext
      apply Subtype.ext
      apply unique_central_involution ht h.five_le h.regular t hfinite hwidth heven
        hradius hz d
        (fun u hu e hue => central_left_eq_of_common_edge h t hfinite hwidth hz hu d e hue)
      · simpa only [Subgroup.orderOf_coe] using hu
      · exact ⟨u.val.property, fun x hx =>
          (congrArg Subtype.val (mem_center_iff.mp u.property ⟨x,hx⟩)).symm⟩⟩
  intro x y hxy
  exact cyclic_center_all_edges hab hcyclic hxy

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
