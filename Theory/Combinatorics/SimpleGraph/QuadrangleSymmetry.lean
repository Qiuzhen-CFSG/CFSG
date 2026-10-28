module
public import Theory.Combinatorics.SimpleGraph.QuadrangleCollinearity.Basic

/-!
# Rigidity of generalized-quadrangle symmetries

A symmetry fixes every point collinear with its center. If it also fixes a
nonincident line, projections onto a second center line show that it fixes
that line pointwise. A fixed noncollinear point becomes another symmetry
center. Three such centers, with two collinear, force every point and line
to be fixed by projection uniqueness and the absence of short cycles.

Thus evaluation on any nonincident line is injective on symmetries. This
is the geometric rigidity used to identify the literal midpoint root images
in the r=4 case of DGS, Groups and Graphs (1985), (3.6)--(3.7), pp.77--80,
and (10.5), p.156. No transitive automorphism group or BN-pair is assumed.
-/

@[expose] public noncomputable section
namespace SimpleGraph.QuadrangleSymmetry
open QuadrangleCollinearity
variable {V : Type*} {Γ : SimpleGraph V}

def Col (a b : V) : Prop := ∃ l, Γ.Adj a l ∧ Γ.Adj b l

theorem Col.symm {a b : V} (h : Col (Γ := Γ) a b) : Col (Γ := Γ) b a := by
  obtain ⟨l,ha,hb⟩ := h
  exact ⟨l,hb,ha⟩

theorem Col.map {a b : V} (h : Col (Γ := Γ) a b) (f : Γ ≃g Γ) :
    Col (Γ := Γ) (f a) (f b) := by
  obtain ⟨l,ha,hb⟩ := h
  exact ⟨f l,f.map_adj_iff.mpr ha,f.map_adj_iff.mpr hb⟩

variable (color : V → Bool)
variable (hcolor : ∀ {a b}, Γ.Adj a b → color a ≠ color b)
variable (hg : ∀ v (p : Γ.Walk v v),p.IsCycle → 8 ≤ p.length)
variable (hconn : Γ.Connected) (hdiam : ∀ a b, Γ.dist a b ≤ 4)
variable (hthick : ∀ (v a b : V), ∃ z, Γ.Adj v z ∧ z≠a ∧ z≠b)

include hcolor hconn hdiam in
theorem projection_exists {a l : V} (ht : color a ≠ color l) (hn : ¬Γ.Adj a l) :
    ∃ z, Γ.Adj z l ∧ Col (Γ := Γ) a z := by
  obtain ⟨p,hp,hlen⟩ := hconn.exists_path_of_dist a l
  have he : ¬Even p.length := fun he => ht
    ((PathTransitivePolygon.QuadrangleRecognition.even_length_iff color hcolor p).mp he)
  obtain ⟨k,hk⟩ := Nat.not_even_iff_odd.mp he
  have hd := hdiam a l
  have hne : Γ.dist a l ≠ 1 := fun he => hn (dist_eq_one_iff_adj.mp he)
  have hl : p.length=3 := by omega
  let q : BasedWalk Γ 3 a := hl ▸ BasedWalk.ofWalk p
  have hend : q.endpoint=l := by simp only [q,BasedWalk.endpoint_cast,BasedWalk.endpoint_ofWalk]
  refine ⟨q.2.1,?_,q.1,q.1.property,q.2.1.property.symm⟩
  exact hend ▸ q.2.2.1.property

include hg in
theorem projection_unique {a l z w : V} (hn : ¬Γ.Adj a l)
    (hz : Γ.Adj z l) (hcz : Col (Γ := Γ) a z)
    (hw : Γ.Adj w l) (hcw : Col (Γ := Γ) a w) : z=w := by
  obtain ⟨m,ham,hzm⟩ := hcz
  obtain ⟨n,han,hwn⟩ := hcw
  let p : BasedWalk Γ 3 a := ⟨⟨m,ham⟩,⟨⟨z,hzm.symm⟩,⟨⟨l,hz⟩,PUnit.unit⟩⟩⟩
  let q : BasedWalk Γ 3 a := ⟨⟨n,han⟩,⟨⟨w,hwn.symm⟩,⟨⟨l,hw⟩,PUnit.unit⟩⟩⟩
  have he := short_endpoint_injective hg (by decide : 3≤3) p q
    ⟨fun he => hn (he ▸ hz),by intro he; change l=m at he; exact hn (he.symm ▸ ham),trivial⟩
    ⟨fun he => hn (he ▸ hw),by intro he; change l=n at he; exact hn (he.symm ▸ han),trivial⟩ rfl
  exact congrArg (fun p : BasedWalk Γ 3 a => (p.2.1 : V)) he

def IsSymmetry (f : Γ ≃g Γ) (a : V) : Prop :=
  ∀ b, Col (Γ := Γ) a b → f b=b

include hg in
theorem fixed_line_of_points (f : Γ ≃g Γ) {a b l : V}
    (hab : a≠b) (ha : Γ.Adj a l) (hb : Γ.Adj b l)
    (hfa : f a=a) (hfb : f b=b) : f l=l := by
  apply common_vertex_unique hg hab
    (show Γ.Adj a (f l) by simpa only [hfa] using f.map_adj_iff.mpr ha)
    (show Γ.Adj b (f l) by simpa only [hfb] using f.map_adj_iff.mpr hb) ha hb

include hg hcolor hconn hdiam hthick in
theorem fixed_line_points (f : Γ ≃g Γ) {a l : V}
    (hs : IsSymmetry f a) (ht : color a≠color l) (hn : ¬Γ.Adj a l)
    (hfl : f l=l) : ∀ y, Γ.Adj y l → f y=y := by
  obtain ⟨z,hzl,m,ham,hzm⟩ := projection_exists color hcolor hconn hdiam ht hn
  obtain ⟨n,han,hnm,_⟩ := hthick a m m
  have hdis : ∀ x, Γ.Adj x n → ¬Γ.Adj x l := by
    intro x hxn hxl
    have hxz := projection_unique hg hn hxl ⟨n,han,hxn⟩ hzl ⟨m,ham,hzm⟩
    have hza : z≠a := fun he => hn (he ▸ hzl)
    have he := common_vertex_unique hg hza (hxz ▸ hxn) han hzm ham
    exact hnm he
  intro y hyl
  by_cases hc : Col (Γ := Γ) a y
  · exact hs y hc
  have hyn : ¬Γ.Adj y n := fun hh => hc ⟨n,han,hh⟩
  have ht' : color y≠color n := by
    have hay := color_eq_of_common hcolor hzl hyl
    have hza := color_eq_of_common hcolor hzm ham
    rw [←hay,hza]
    exact hcolor han
  obtain ⟨x,hxn,hxy⟩ := projection_exists color hcolor hconn hdiam ht' hyn
  have hfx := hs x ⟨n,han,hxn⟩
  apply projection_unique hg (hdis x hxn)
    (show Γ.Adj (f y) l by simpa only [hfl] using f.map_adj_iff.mpr hyl)
    (show Col (Γ := Γ) x (f y) by simpa only [hfx] using hxy.symm.map f)
    hyl hxy.symm

include hg hcolor hconn hdiam hthick in
theorem symmetry_at_fixed_noncollinear (f : Γ ≃g Γ) {a b : V}
    (hs : IsSymmetry f a) (ht : color a=color b) (hn : ¬Col (Γ := Γ) a b)
    (hfb : f b=b) : IsSymmetry f b := by
  intro y ⟨l,hbl,hyl⟩
  have hal : ¬Γ.Adj a l := fun hh => hn ⟨l,hh,hbl⟩
  have htl : color a≠color l := ht ▸ hcolor hbl
  obtain ⟨z,hzl,haz⟩ := projection_exists color hcolor hconn hdiam htl hal
  have hzb : z≠b := fun he => hn (he ▸ haz)
  have hfl := fixed_line_of_points hg f hzb hzl hbl (hs z haz) hfb
  exact fixed_line_points color hcolor hg hconn hdiam hthick f hs htl hal hfl y hyl

include hg hcolor hconn hdiam hthick in
/-- A symmetry fixing a noncollinear point fixes the entire quadrangle. -/
theorem symmetry_fixed_noncollinear (f : Γ ≃g Γ) {a b : V}
    (hs : IsSymmetry f a) (ht : color a=color b) (hn : ¬Col (Γ := Γ) a b)
    (hfb : f b=b) : ∀ v, f v=v := by
  have hsb := symmetry_at_fixed_noncollinear color hcolor hg hconn hdiam hthick f hs ht hn hfb
  obtain ⟨l,hbl,_,_⟩ := hthick b b b
  have hal : ¬Γ.Adj a l := fun hh => hn ⟨l,hh,hbl⟩
  have htl : color a≠color l := ht ▸ hcolor hbl
  obtain ⟨z,hzl,n,han,hzn⟩ := projection_exists color hcolor hconn hdiam htl hal
  obtain ⟨w,hlw,hwb,hwz⟩ := hthick l b z
  have haw : color a=color w := ht.trans (color_eq_of_common hcolor hbl hlw.symm)
  have hnw : ¬Col (Γ := Γ) a w := by
    intro hh
    exact hwz (projection_unique hg hal hlw.symm hh hzl ⟨n,han,hzn⟩)
  have hfw := hsb w ⟨l,hbl,hlw.symm⟩
  have hsw := symmetry_at_fixed_noncollinear color hcolor hg hconn hdiam hthick f hs haw hnw hfw
  have hpoints : ∀ p, color a=color p → f p=p := by
    intro p hap
    by_contra hfp
    have hnp : ¬Col (Γ := Γ) a p := fun hh => hfp (hs p hh)
    have hbp : ¬Col (Γ := Γ) b p := fun hh => hfp (hsb p hh)
    have hwp : ¬Col (Γ := Γ) w p := fun hh => hfp (hsw p hh)
    obtain ⟨m,ham,hmn,_⟩ := hthick a n n
    have hpm : ¬Γ.Adj p m := fun hh => hnp ⟨m,ham,hh⟩
    have htp : color p≠color m := hap ▸ hcolor ham
    obtain ⟨x,hxm,hpx⟩ := projection_exists color hcolor hconn hdiam htp hpm
    have hax := color_eq_of_common hcolor ham hxm
    have hfx := hs x ⟨m,ham,hxm⟩
    have hcol (t : V) (hat : color a=color t) (hst : IsSymmetry f t) :
        Col (Γ := Γ) t x := by
      by_contra htx
      have hsx := symmetry_at_fixed_noncollinear color hcolor hg hconn hdiam hthick f hst
        (hat.symm.trans hax) htx hfx
      exact hfp (hsx p hpx.symm)
    obtain ⟨j,hbj,hxj⟩ := hcol b ht hsb
    obtain ⟨k,hwk,hxk⟩ := hcol w haw hsw
    have hxb : x≠b := fun he => hbp (he ▸ hpx.symm)
    have hxw : x≠w := fun he => hwp (he ▸ hpx.symm)
    have hxl := triangle_on_line hg hwb.symm hxw.symm hxb hbl hlw.symm hbj hxj hwk hxk
    have hxz := projection_unique hg hal hxl ⟨m,ham,hxm⟩ hzl ⟨n,han,hzn⟩
    have hza : z≠a := fun he => hal (he ▸ hzl)
    exact hmn (common_vertex_unique hg hza (hxz ▸ hxm) ham hzn han)
  intro v
  by_cases hav : color a=color v
  · exact hpoints v hav
  obtain ⟨x,hvx,_,_⟩ := hthick v v v
  obtain ⟨y,hvy,hyx,_⟩ := hthick v x x
  have htx : color a=color x := by
    have hh := hcolor hvx
    cases ha : color a <;> cases hv : color v <;> cases hx : color x <;> simp_all
  have hty := htx.trans (color_eq_of_common hcolor hvx.symm hvy.symm)
  exact fixed_line_of_points hg f hyx.symm hvx.symm hvy.symm (hpoints x htx) (hpoints y hty)

include hg hcolor hconn hdiam hthick in
/-- A symmetry fixing a line not incident with its center is trivial. -/
theorem symmetry_fixed_nonincident (f : Γ ≃g Γ) {a l : V}
    (hs : IsSymmetry f a) (ht : color a≠color l) (hn : ¬Γ.Adj a l)
    (hfl : f l=l) : ∀ v, f v=v := by
  obtain ⟨z,hzl,haz⟩ := projection_exists color hcolor hconn hdiam ht hn
  obtain ⟨b,hlb,hbz,_⟩ := hthick l z z
  have hab : color a=color b := by
    obtain ⟨m,ham,hzm⟩ := haz
    exact (color_eq_of_common hcolor ham hzm).trans (color_eq_of_common hcolor hzl hlb.symm)
  have hnb : ¬Col (Γ := Γ) a b := fun hh =>
    hbz (projection_unique hg hn hlb.symm hh hzl haz)
  exact symmetry_fixed_noncollinear color hcolor hg hconn hdiam hthick f hs hab hnb
    (fixed_line_points color hcolor hg hconn hdiam hthick f hs ht hn hfl b hlb.symm)

end SimpleGraph.QuadrangleSymmetry

