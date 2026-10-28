module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralVertexAction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralCompanion
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.EvenCentralIntervals
public import Theory.GroupAction.CubicTree.TrackArcs

/-!
# Two-edge central blocks

If a central block had one edge, (6.6) and local arc reflections would
produce two adjacent one-edge central blocks with the same fixed interval.
Their product centralizes two vertex stabilizers at distance two. The short
arc-generation theorem makes these stabilizers generate the acting group,
and faithful action then contradicts the distinct central blocks.

The final source application discharges the even-fixed-interval premise with
(6.5)--(6.6). All intervals and conjugations belong to the original action.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), (6.7),
printed pp.398--399.
-/

@[expose] public section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

theorem forward_mul_fixes_of_both_move
    {V A : Type*} [Group A] [MulAction A V] {Γ : SimpleGraph V}
    (h : GraphAction Γ A) {n : ℕ} {v : V} (p : BasedWalk Γ (n+1) v)
    (hcard : Nat.card (Γ.neighborSet p.endpoint) = 3)
    (a b : A) (ha : ∀ x ∈ p.vertices, a • x = x)
    (hb : ∀ x ∈ p.vertices, b • x = x)
    {x : V} (hx : Forward p x) (hax : a • x ≠ x) (hbx : b • x ≠ x) :
    (a*b) • x = x := by
  have htwo : ({y : V | Forward p y} : Set V).ncard = 2 := by
    rw [← Nat.card_coe_set_eq]
    exact card_forward_of_cubic p hcard
  obtain ⟨u,w,_,he⟩ := Set.ncard_eq_two.mp htwo
  have hx' : x = u ∨ x = w := by
    have hh : x ∈ {y : V | Forward p y} := hx
    simpa only [he, Set.mem_insert_iff, Set.mem_singleton_iff] using hh
  have hax' : a • x = u ∨ a • x = w := by
    have hh := forward_smul_of_fixes h p a ha hx
    change a • x ∈ {y : V | Forward p y} at hh
    simpa only [he, Set.mem_insert_iff, Set.mem_singleton_iff] using hh
  have habx' : (a*b) • x = u ∨ (a*b) • x = w := by
    have hh := forward_smul_of_fixes h p (a*b)
      (fun y hy => by rw [mul_smul, hb y hy, ha y hy]) hx
    change (a*b) • x ∈ {y : V | Forward p y} at hh
    simpa only [he, Set.mem_insert_iff, Set.mem_singleton_iff] using hh
  have hne : (a*b) • x ≠ a • x := by
    rw [mul_smul]
    exact fun hh => hbx ((MulAction.toPerm a).injective hh)
  aesop

/-- Folding a two-edge arc about its endpoint promotes centralization of its
fixer to centralization of the endpoint stabilizer. -/
theorem CubicTreeAction.centralizes_vertex_of_folded_two_arc (h : CubicTreeAction F)
    {s : ℕ} (hs : 4 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) (a : ℤ) {w x : G}
    (hx : x • t.vertex (a+2) = t.vertex (a+2))
    (hxm : x • t.vertex (a+1) ≠ t.vertex (a+1))
    (hw : ∀ g ∈ t.segmentFixer a 2, Commute w g) (hwx : Commute w x) :
    ∀ g ∈ RankTwo.stabilizer F (t.vertex (a+2)), Commute w g := by
  have h01 := t.adjacent a
  have h12 : (RankTwo.graph F).Adj (t.vertex (a+1)) (t.vertex (a+2)) := by
    simpa only [show a+1+1=a+2 by omega] using t.adjacent (a+1)
  have h23 : (RankTwo.graph F).Adj (t.vertex (a+2)) (x • t.vertex (a+1)) := by
    simpa only [hx] using trackGraphAction.map_adj x h12.symm
  have h34 := trackGraphAction.map_adj x h01.symm
  let p : BasedWalk (RankTwo.graph F) 4 (t.vertex a) :=
    ⟨⟨t.vertex (a+1), h01⟩, ⟨⟨t.vertex (a+2), h12⟩,
      ⟨⟨x • t.vertex (a+1), h23⟩, ⟨⟨x • t.vertex a, h34⟩, PUnit.unit⟩⟩⟩⟩
  have hp : p.Nonbacktracking := by
    refine ⟨?_, hxm, ?_, trivial⟩
    · intro he
      have hi := t.injective he
      omega
    · intro he
      have hi := t.injective ((MulAction.toPerm x).injective (he.trans hx.symm))
      omega
  have hgen := h.arc_stabilizers_generate_overlap hshort hs p hp
    (i:=2) (j:=2) le_rfl (by decide)
  let C := centralizer ({w} : Set G)
  have hleft : arcIntervalStabilizer p.toWalk 0 2 ≤ C := by
    intro g hg y hy
    have hey : y=w := Set.mem_singleton_iff.mp hy
    subst y
    apply hw g
    rw [t.mem_segmentFixer]
    intro i hi hir
    have hic : i=a ∨ i=a+1 ∨ i=a+2 := by omega
    rcases hic with rfl | rfl | rfl
    · exact hg 0 (by decide) (by decide)
    · exact hg 1 (by decide) (by decide)
    · exact hg 2 (by decide) (by decide)
  have hright : arcIntervalStabilizer p.toWalk 2 4 ≤ C := by
    intro g hg y hy
    have hey : y=w := Set.mem_singleton_iff.mp hy
    subst y
    have hg2 : g • t.vertex (a+2) = t.vertex (a+2) := hg 2 (by decide) (by decide)
    have hg3 : g • (x • t.vertex (a+1)) = x • t.vertex (a+1) := hg 3 (by decide) (by decide)
    have hg4 : g • (x • t.vertex a) = x • t.vertex a := hg 4 (by decide) (by decide)
    have hconj : x⁻¹*g*x ∈ t.segmentFixer a 2 := by
      rw [t.mem_segmentFixer]
      intro i hi hir
      have hic : i=a ∨ i=a+1 ∨ i=a+2 := by omega
      rcases hic with rfl | rfl | rfl
      · simp only [mul_smul, hg4, inv_smul_smul]
      · simp only [mul_smul, hg3, inv_smul_smul]
      · simp only [mul_smul, hg2, inv_smul_eq_iff, hx]
    have hh := (hw _ hconj).conj x
    have hxw : x*w*x⁻¹=w := by
      rw [hwx.symm.eq, mul_assoc, mul_inv_cancel, mul_one]
    simpa only [hxw, mul_assoc, mul_inv_cancel_left, inv_mul_cancel_right,
      mul_inv_cancel, mul_one] using hh.eq
  intro g hg
  have hgin : g ∈ arcIntervalStabilizer p.toWalk 2 2 := by
    intro k hk hk'
    have he : k=2 := by omega
    subst k
    exact hg
  rw [← hgen] at hgin
  exact (sup_le hleft hright hgin) w (Set.mem_singleton w)

private theorem CubicTreeAction.companion_product_centralizes_right (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z z' : G}
    (d : t.CentralInterval z) (e : t.CentralInterval z')
    (hw : d.centralRight-d.centralLeft=1) (hew : e.centralRight-e.centralLeft=1)
    (he : e.centralRight=d.centralLeft)
    (hL : d.fixedLeft=e.fixedLeft) (hR : d.fixedRight=e.fixedRight)
    (hmid : d.fixedLeft+d.fixedRight=2*d.centralLeft)
    (hodd : Odd (d.fixedRight-d.centralLeft)) :
    ∀ g ∈ RankTwo.stabilizer F (t.vertex d.centralRight), Commute (z'*z) g := by
  let a := d.centralLeft
  have hdc : d.centralRight=a+1 := by dsimp only [a]; omega
  have hec : e.centralLeft=a-1 := by dsimp only [a]; omega
  obtain ⟨j,hj⟩ := hodd
  let k := j+1
  let x := (MulAut.conj (t.translation^k)) z'
  let f := e.shift k
  have hfL : f.fixedLeft=a+1 := by dsimp only [f, Track.CentralInterval.shift, k, a]; omega
  have hfc : f.centralLeft=d.fixedRight := by
    dsimp only [f, Track.CentralInterval.shift, k, a]; omega
  have hdL := d.centralLeft_mem
  have hdR := d.centralRight_mem
  have heL := e.centralLeft_mem
  have heR := e.centralRight_mem
  have hfixR (u : G) (du : t.CentralInterval u)
      (huL : du.fixedLeft=d.fixedLeft) (huR : du.fixedRight=d.fixedRight) :
      u • t.vertex d.fixedRight = t.vertex d.fixedRight :=
    (du.fixed_iff _).2 ⟨by omega, by omega⟩
  have hfixPrev (u : G) (du : t.CentralInterval u)
      (huL : du.fixedLeft=d.fixedLeft) (huR : du.fixedRight=d.fixedRight) :
      u • t.vertex (d.fixedRight-1) = t.vertex (d.fixedRight-1) :=
    (du.fixed_iff _).2 ⟨by omega, by omega⟩
  have hmove (u : G) (du : t.CentralInterval u) (huR : du.fixedRight=d.fixedRight) :
      u • t.vertex (d.fixedRight+1) ≠ t.vertex (d.fixedRight+1) := by
    intro hh
    have hi := (du.fixed_iff _).1 hh
    omega
  have hadj : (RankTwo.graph F).Adj (t.vertex (d.fixedRight-1)) (t.vertex d.fixedRight) := by
    simpa only [sub_add_cancel] using t.adjacent (d.fixedRight-1)
  let p : BasedWalk (RankTwo.graph F) 1 (t.vertex (d.fixedRight-1)) :=
    ⟨⟨t.vertex d.fixedRight, hadj⟩, PUnit.unit⟩
  have hpfix (u : G) (du : t.CentralInterval u)
      (huL : du.fixedLeft=d.fixedLeft) (huR : du.fixedRight=d.fixedRight) :
      ∀ v ∈ p.vertices, u • v = v := by
    change ∀ v ∈ [t.vertex (d.fixedRight-1), t.vertex d.fixedRight], _
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hfixPrev u du huL huR
    · obtain rfl := List.mem_singleton.mp hv
      exact hfixR u du huL huR
  have hpforward : Forward p (t.vertex (d.fixedRight+1)) := by
    refine ⟨t.adjacent _, ?_⟩
    intro heq
    have hi := t.injective heq
    omega
  have hproduct := forward_mul_fixes_of_both_move trackGraphAction p
    (h.card_neighbor _) z' z (hpfix z' e hL.symm hR.symm)
    (hpfix z d rfl rfl) hpforward (hmove z' e hR.symm) (hmove z d rfl)
  have hwx : Commute (z'*z) x := by
    have hc := f.central f.centralLeft le_rfl f.central_lt
    apply (hc.2 (z'*z) ?_).symm
    refine ⟨?_, ?_⟩
    · change (z'*z) • t.vertex f.centralLeft = t.vertex f.centralLeft
      rw [hfc, mul_smul, hfixR z d rfl rfl, hfixR z' e hL.symm hR.symm]
    · change (z'*z) • t.vertex (f.centralLeft+1) = t.vertex (f.centralLeft+1)
      simpa only [hfc] using hproduct
  have hx : x • t.vertex (a+1) = t.vertex (a+1) := by
    exact (f.fixed_iff _).2 ⟨by omega, by have hh:=f.centralLeft_mem; omega⟩
  have hxm : x • t.vertex a ≠ t.vertex a := by
    intro hh
    have hi := (f.fixed_iff _).1 hh
    omega
  have hwfix : ∀ g ∈ t.segmentFixer (a-1) 2, Commute (z'*z) g := by
    intro g hg
    rw [t.mem_segmentFixer] at hg
    apply Commute.mul_left
    · apply (e.central e.centralLeft le_rfl e.central_lt).2
      refine ⟨hg _ ?_ ?_, hg _ ?_ ?_⟩ <;> omega
    · apply (d.central a (by rfl) (by omega)).2
      refine ⟨hg _ ?_ ?_, hg _ ?_ ?_⟩ <;> omega
  have hh := h.centralizes_vertex_of_folded_two_arc (by omega : 4≤s) hshort t (a-1)
    (w:=z'*z) (x:=x) (by simpa only [show a-1+2=a+1 by omega] using hx)
    (by simpa only [sub_add_cancel] using hxm) hwfix hwx
  simpa only [show a-1+2=a+1 by omega, ← hdc] using hh

/-- Adjacent one-edge central blocks cannot have the same fixed interval.
The companion product centralizes two vertices at distance two, whose
stabilizers generate the actual acting group. -/
theorem CubicTreeAction.no_central_companions (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z z' : G}
    (hz : t.CentralInvolution z) (hz' : t.CentralInvolution z')
    (d : t.CentralInterval z) (e : t.CentralInterval z')
    (hw : d.centralRight-d.centralLeft=1) (hew : e.centralRight-e.centralLeft=1)
    (he : e.centralRight=d.centralLeft)
    (hL : d.fixedLeft=e.fixedLeft) (hR : d.fixedRight=e.fixedRight) : False := by
  have hdm := h.central_margin_comparison hs hshort t hz hz d d
  have hem := h.central_margin_comparison hs hshort t hz' hz' e e
  have hdleft := d.leftMargin_cast
  have hdright := d.rightMargin_cast
  have heleft := e.leftMargin_cast
  have heright := e.rightMargin_cast
  have hmid : d.fixedLeft+d.fixedRight=2*d.centralLeft := by omega
  have hdL := d.centralLeft_mem
  have hdR := d.centralRight_mem
  have heL := e.centralLeft_mem
  have heR := e.centralRight_mem
  have hodd : Odd (d.fixedRight-d.centralLeft) := by
    rcases Int.even_or_odd (d.fixedRight-d.centralLeft) with hEven | hOdd
    · obtain ⟨k,hk⟩ := hEven
      let f := d.shift k
      have hfL : f.fixedLeft=d.centralLeft := by
        dsimp only [f, Track.CentralInterval.shift]; omega
      have hfc : f.centralLeft=d.fixedRight := by
        dsimp only [f, Track.CentralInterval.shift]; omega
      have hnc := h.not_commute_centralLeft t f
        (show z • t.vertex f.centralLeft = t.vertex f.centralLeft from
          (d.fixed_iff _).2 ⟨by omega, by omega⟩)
        (show z • t.vertex (f.centralLeft+1) ≠ t.vertex (f.centralLeft+1) from by
          intro hh
          have hi := (d.fixed_iff _).1 hh
          omega)
      apply False.elim
      apply hnc
      have hc := d.central d.centralLeft le_rfl d.central_lt
      apply (hc.2 _ ?_).symm
      refine ⟨(f.fixed_iff _).2 ⟨by omega, ?_⟩, (f.fixed_iff _).2 ⟨by omega, ?_⟩⟩ <;>
        dsimp only [f, Track.CentralInterval.shift] <;> omega
    · exact hOdd
  have hright := h.companion_product_centralizes_right hs hshort t d e hw hew he hL hR hmid hodd
  have hcomm : Commute z z' := by
    apply (d.central d.centralLeft le_rfl d.central_lt).2
    exact ⟨(e.fixed_iff _).2 ⟨by omega, by omega⟩,
      (e.fixed_iff _).2 ⟨by omega, by omega⟩⟩
  have hleft : ∀ g ∈ RankTwo.stabilizer F (t.vertex e.centralLeft), Commute (z'*z) g := by
    have hh := h.companion_product_centralizes_right hs hshort t.reverse e.reverse d.reverse
      (by change -e.centralLeft- -e.centralRight=1; omega)
      (by change -d.centralLeft- -d.centralRight=1; omega)
      (by change -d.centralLeft= -e.centralRight; omega)
      (by change -e.fixedRight= -d.fixedRight; omega)
      (by change -e.fixedLeft= -d.fixedLeft; omega)
      (by change -e.fixedRight+ -e.fixedLeft=2*(-e.centralRight); omega)
      (show Odd (-e.fixedLeft- -e.centralRight) from by
        convert hodd using 1
        omega)
    simpa only [Track.CentralInterval.reverse, Track.reverse, neg_neg, hcomm.eq] using hh
  let a := e.centralLeft
  have hd : d.centralRight=a+2 := by dsimp only [a]; omega
  have h01 := t.adjacent a
  have h12 : (RankTwo.graph F).Adj (t.vertex (a+1)) (t.vertex (a+2)) := by
    simpa only [show a+1+1=a+2 by omega] using t.adjacent (a+1)
  let p : BasedWalk (RankTwo.graph F) 2 (t.vertex a) :=
    ⟨⟨t.vertex (a+1), h01⟩, ⟨⟨t.vertex (a+2), h12⟩, PUnit.unit⟩⟩
  have hp : p.Nonbacktracking := by
    refine ⟨?_, trivial⟩
    intro hh
    have hi:=t.injective hh
    omega
  have hgen := h.arc_stabilizers_generate_separated hshort (by omega : 2≤s) p hp
    (i:=0) (j:=2) (by decide) (by decide)
  let C := centralizer ({z'*z} : Set G)
  have hCle : arcIntervalStabilizer p.toWalk 0 0 ≤ C := by
    intro g hg u hu
    obtain rfl := Set.mem_singleton_iff.mp hu
    exact hleft g (hg 0 le_rfl le_rfl)
  have hCre : arcIntervalStabilizer p.toWalk 2 2 ≤ C := by
    intro g hg u hu
    obtain rfl := Set.mem_singleton_iff.mp hu
    apply hright g
    have hh : g • t.vertex (a+2) = t.vertex (a+2) := hg 2 le_rfl le_rfl
    change g • t.vertex d.centralRight = t.vertex d.centralRight
    simpa only [hd] using hh
  have hCtop : C=⊤ := top_unique (by rw [← hgen]; exact sup_le hCle hCre)
  have hwall : ∀ g:G, Commute (z'*z) g := by
    intro g
    have hg:g∈C := by rw [hCtop]; trivial
    exact hg _ (Set.mem_singleton _)
  have hwone : z'*z=1 := h.eq_one_of_centralizes_of_fixed_edge hwall (t.adjacent d.centralLeft)
    (by rw [mul_smul, (d.fixed_iff _).2 ⟨by omega, by omega⟩,
      (e.fixed_iff _).2 ⟨by omega, by omega⟩])
    (by rw [mul_smul, (d.fixed_iff _).2 ⟨by omega, by omega⟩,
      (e.fixed_iff _).2 ⟨by omega, by omega⟩])
  have hzz : z'=z := by
    have hz2 : z*z=1 := by simpa only [pow_two, hz.1] using pow_orderOf_eq_one z
    exact mul_right_cancel (hwone.trans hz2.symm)
  have hc := e.central e.centralLeft le_rfl e.central_lt
  have hc' : t.CentralEdge z e.centralLeft :=
    (congrArg (fun u => t.CentralEdge u e.centralLeft) hzz).mp hc
  have hi := (h.centralEdge_iff_in_centralInterval hs hshort t hz d _).1 hc'
  omega

/-- Goldschmidt (6.7): after exclusion of odd fixed intervals, every central
involution has a central block consisting of exactly two edges. -/
theorem CubicTreeAction.centralInterval_length_eq_two_of_even_fixed
    (h : CubicTreeAction F) {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G)
    (hfinite : ∀ u, t.CentralInvolution u → u ∉ t.fixer)
    (heven : ∀ u, t.CentralInvolution u → ∀ d : t.CentralInterval u,
      Even (d.fixedRight-d.fixedLeft))
    {z : G} (hz : t.CentralInvolution z) (d : t.CentralInterval z) :
    d.centralRight-d.centralLeft=2 := by
  have hle := h.centralInterval_length_le_two hs hshort t hz d
  have hpos := d.central_lt
  by_contra hh
  have hw : d.centralRight-d.centralLeft=1 := by omega
  obtain ⟨u,w,hu,hw',du,dw,hL,hR,huwidth,hwwidth,hadj⟩ :=
    h.exists_central_companions hs hshort p hp hn t hfinite heven hz d hw
  exact h.no_central_companions hs hshort t hu hw' du dw huwidth hwwidth hadj hL hR

/-- The actual large-residual source consumer of (6.7); the preceding
odd-interval exclusion supplies every evenness premise. -/
theorem CubicTreeAction.centralInterval_length_eq_two
    (h : CubicTreeAction F) {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬ RightRegular (A := G) p)
    (hC : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* Multiplicative (ZMod 3)))
    (hA : ∀ i, ¬ Nonempty ((pResidual 2 (F i)) ≃* alternatingGroup (Fin 4)))
    (t : Track (RankTwo.graph F) G)
    (hfinite : ∀ u, t.CentralInvolution u → u ∉ t.fixer)
    (hpreferred : AdjacentInvolutionMovers (RankTwo.graph F) G → t.HasReflections)
    {z : G} (hz : t.CentralInvolution z) (d : t.CentralInterval z) :
    d.centralRight-d.centralLeft=2 :=
  h.centralInterval_length_eq_two_of_even_fixed hs hshort p hp hn t hfinite
    (fun _ hu du => h.centralInterval_fixedLength_even hs hshort p hp hn hC hA t
      hfinite hpreferred hu du) hz d

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
