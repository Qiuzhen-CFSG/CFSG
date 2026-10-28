module
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortFix
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.QuadrangleRecognition

/-!
# Root automorphism rigidity in a generalized quadrangle

An automorphism fixing every neighbor of the three interior vertices of a
length-four root is determined by its value on any exit at the final vertex.
In particular, fixing one such exit makes the automorphism trivial.

A fixed star transfers to any fixed opposite vertex: project its neighbors
along the unique paths of length three. A thickness choice and another
projection turn the three interior fixed stars into four consecutive fixed
stars. These propagate along nonbacktracking paths, and connectedness gives
identity everywhere. No transitive group action or finiteness is assumed.

This is the geometric rigidity needed for the root-image comparison in DGS,
Groups and Graphs (1985), (3.6)--(3.7), pp.77--80, in the quadrangle case s=5.
-/

@[expose] public noncomputable section

open SimpleGraph
namespace SimpleGraph.GeneralizedQuadrangle
variable {V : Type*} {Γ : SimpleGraph V}

/-- Bipartite diameter-four geometry with uniqueness below the eight-cycle bound. -/
structure Geometry (Γ : SimpleGraph V) where
  color : V → Bool
  color_adj : ∀ {x y}, Γ.Adj x y → color x ≠ color y
  connected : Γ.Connected
  diameter : ∀ x y, Γ.dist x y ≤ 4
  short_paths : ∀ {x y} (p q : Γ.Walk x y), p.IsPath → q.IsPath →
    p.length + q.length < 8 → p = q

variable (D : Geometry Γ)
include D

theorem Geometry.path_geodesic {x y : V} (p : Γ.Walk x y)
    (hp : p.IsPath) (hlen : p.length ≤ 4) : Γ.dist x y = p.length := by
  have hd := Γ.dist_le p
  obtain ⟨q,hq,hlq⟩ := D.connected.exists_path_of_dist x y
  by_contra hn
  have he := D.short_paths p q hp hq (by omega)
  have hh := congrArg Walk.length he
  omega

theorem Geometry.short_fixed (f : Γ ≃g Γ) {x y : V} (p : Γ.Walk x y)
    (hp : p.IsPath) (hlen : p.length ≤ 3) (hx : f x=x) (hy : f y=y) :
    ∀ z ∈ p.support, f z=z := by
  let q := (p.map f.toHom).copy hx hy
  have hq : q.IsPath := (Walk.isPath_copy ..).mpr (hp.map f.injective)
  have he := D.short_paths q p hq hp (by simp only [q,Walk.length_copy,Walk.length_map]; omega)
  have hs := congrArg Walk.support he
  simp only [q,Walk.support_copy,Walk.support_map] at hs
  simpa only [List.map_id,id_eq] using
    (List.map_inj_left (l:=p.support) (f:=f) (g:=id)).mp (hs.trans (List.map_id _).symm)

theorem Geometry.neighbor_opposite_distance {a b z : V}
    (hab : Γ.dist a b=4) (hbz : Γ.Adj b z) : Γ.dist a z=3 := by
  have htri := D.connected.dist_triangle (u:=a) (v:=z) (w:=b)
  rw [dist_eq_one_iff_adj.mpr hbz.symm,hab] at htri
  obtain ⟨p,hp,hlen⟩ := D.connected.exists_path_of_dist a b
  have hcolor : D.color a=D.color b :=
    (PathTransitivePolygon.QuadrangleRecognition.even_length_iff D.color D.color_adj p).mp
      (by rw [hlen,hab]; decide)
  obtain ⟨q,hq,hlq⟩ := D.connected.exists_path_of_dist a z
  have hodd : ¬Even q.length := fun he => D.color_adj hbz (hcolor.symm.trans
    ((PathTransitivePolygon.QuadrangleRecognition.even_length_iff D.color D.color_adj q).mp he))
  have hb := D.diameter a z
  have hne : Γ.dist a z ≠ 4 := by intro he; apply hodd; rw [hlq,he]; decide
  omega

def FixesStar (f : Γ ≃g Γ) (a : V) : Prop := f a=a ∧ ∀ z, Γ.Adj a z → f z=z

/-- Fixing a star and an opposite vertex fixes the opposite star. -/
theorem Geometry.fixesStar_opposite (f : Γ ≃g Γ) {a b : V}
    (ha : FixesStar f a) (hb : f b=b) (hab : Γ.dist a b=4) : FixesStar f b := by
  refine ⟨hb,fun z hbz => ?_⟩
  obtain ⟨p,hp,hlen⟩ := D.connected.exists_path_of_dist a z
  have hl : p.length=3 := hlen.trans (D.neighbor_opposite_distance hab hbz)
  cases p with
  | nil => simp at hl
  | @cons a u z hau p =>
    have hpl : p.length=2 := by simp only [Walk.length_cons] at hl; omega
    let q := p.concat hbz.symm
    have hgeo : q.length=Γ.dist u b := by
      have hu := D.connected.dist_triangle (u:=a) (v:=u) (w:=b)
      rw [dist_eq_one_iff_adj.mpr hau,hab] at hu
      have hq := Γ.dist_le q
      simp only [q,Walk.length_concat,hpl] at hq ⊢
      omega
    exact D.short_fixed f q (q.isPath_of_length_eq_dist hgeo)
      (by simp only [q,Walk.length_concat,hpl]; decide)
      (ha.2 u hau) hb z (by simp only [q,Walk.support_concat,List.mem_append]; exact Or.inl p.end_mem_support)

theorem Geometry.cycle_bound {a : V} (p : Γ.Walk a a) (hp : p.IsCycle) :
    7 < p.length := by
  by_contra hn
  have hthree := hp.three_le_length
  have he := D.short_paths (p.take 1) (p.drop 1).reverse
    (hp.isPath_take (by omega)) (hp.isPath_drop (by omega)).reverse (by
      simp only [Walk.take_length,Walk.length_reverse,Walk.drop_length]
      omega)
  have hh := congrArg Walk.length he
  simp only [Walk.take_length,Walk.length_reverse,Walk.drop_length] at hh
  omega

theorem Geometry.four_distance {a b c d e : V}
    (hab : Γ.Adj a b) (hbc : Γ.Adj b c) (hcd : Γ.Adj c d) (hde : Γ.Adj d e)
    (hac : c ≠ a) (hbd : d ≠ b) (hce : e ≠ c) : Γ.dist a e = 4 := by
  let p : BasedWalk Γ 4 a :=
    ⟨⟨b,hab⟩,⟨⟨c,hbc⟩,⟨⟨d,hcd⟩,⟨⟨e,hde⟩,PUnit.unit⟩⟩⟩⟩
  have hp : p.Nonbacktracking := ⟨hac,hbd,hce,trivial⟩
  exact D.path_geodesic p.toWalk
    (PathTransitivePolygon.isPath_of_nonbacktracking_of_cycle_bound
      (fun _ q hq => D.cycle_bound q hq) p hp (by decide))
    (by simp only [BasedWalk.length_toWalk]; decide)

/-- Four consecutive vertices whose entire stars are fixed. -/
structure StarChain (f : Γ ≃g Γ) (a b c d : V) : Prop where
  ab : Γ.Adj a b
  bc : Γ.Adj b c
  cd : Γ.Adj c d
  ac : c ≠ a
  bd : d ≠ b
  fa : FixesStar f a
  fb : FixesStar f b
  fc : FixesStar f c
  fd : FixesStar f d

omit D in
theorem StarChain.reverse {f : Γ ≃g Γ} {a b c d : V}
    (h : StarChain f a b c d) : StarChain f d c b a :=
  ⟨h.cd.symm,h.bc.symm,h.ab.symm,h.bd.symm,h.ac.symm,h.fd,h.fc,h.fb,h.fa⟩

theorem Geometry.chain_extend {f : Γ ≃g Γ} {a b c d e : V}
    (h : StarChain f a b c d) (hde : Γ.Adj d e) (hce : e ≠ c) :
    StarChain f b c d e := by
  have hdist := D.four_distance h.ab h.bc h.cd hde h.ac h.bd hce
  exact ⟨h.bc,h.cd,hde,h.bd,hce,h.fb,h.fc,h.fd,
    D.fixesStar_opposite f h.fa (h.fd.2 e hde) hdist⟩

def GoodVertex (f : Γ ≃g Γ) (x : V) : Prop := ∃ a b c, StarChain f a b c x

theorem Geometry.good_neighbor
    (hthick : ∀ v a b, ∃ z, Γ.Adj v z ∧ z ≠ a ∧ z ≠ b)
    {f : Γ ≃g Γ} {x y : V} (hx : GoodVertex f x) (hxy : Γ.Adj x y) :
    GoodVertex f y := by
  obtain ⟨a,b,c,h⟩ := hx
  by_cases he : y=c
  · subst y
    obtain ⟨t,hat,htb,_⟩ := hthick a b b
    have ht := (D.chain_extend h.reverse hat htb).reverse
    exact ⟨t,a,b,ht⟩
  · exact ⟨b,c,x,D.chain_extend h hxy he⟩

/-- Four consecutive fixed stars force identity throughout the connected graph. -/
theorem Geometry.identity_of_chain
    (hthick : ∀ v a b, ∃ z, Γ.Adj v z ∧ z ≠ a ∧ z ≠ b)
    {f : Γ ≃g Γ} {a b c d : V} (h : StarChain f a b c d) :
    ∀ y, f y=y := by
  have hw : ∀ {u v : V} (p : Γ.Walk u v), GoodVertex f u → GoodVertex f v := by
    intro u v p
    induction p with
    | nil => exact id
    | cons huv p ih =>
      intro hu
      exact ih (D.good_neighbor hthick hu huv)
  intro y
  obtain ⟨p⟩ := D.connected d y
  obtain ⟨_,_,_,hy⟩ := hw p ⟨a,b,c,h⟩
  exact hy.fd.1

theorem Geometry.root_rigidity_chain
    (hthick : ∀ v a b, ∃ z, Γ.Adj v z ∧ z ≠ a ∧ z ≠ b)
    (f : Γ ≃g Γ) {b c d e z : V}
    (hbc : Γ.Adj b c) (hcd : Γ.Adj c d) (hde : Γ.Adj d e) (hez : Γ.Adj e z)
    (hbd : d ≠ b) (hce : e ≠ c) (hdz : z ≠ d)
    (hb : FixesStar f b) (hc : FixesStar f c) (hd : FixesStar f d) (hz : f z=z) :
    ∀ v, f v=v := by
  have hbz := D.four_distance hbc hcd hde hez hbd hce hdz
  obtain ⟨a,hba,hac,_⟩ := hthick b c c
  have hae := D.four_distance hba.symm hbc hcd hde hac.symm hbd hce
  have haz := D.neighbor_opposite_distance hae hez
  obtain ⟨p,hp,hlen⟩ := D.connected.exists_path_of_dist a z
  have hl : p.length=3 := hlen.trans haz
  let q : BasedWalk Γ 3 a := hl ▸ BasedWalk.ofWalk p
  have hqend : q.endpoint=z := by
    simp only [q,BasedWalk.endpoint_cast,BasedWalk.endpoint_ofWalk]
  have hqnb : q.Nonbacktracking := BasedWalk.nonbacktracking_of_geodesic q (by rw [hqend,haz])
  have hqpath : q.toWalk.IsPath := q.toWalk.isPath_of_length_eq_dist (by
    rw [BasedWalk.length_toWalk,hqend,haz])
  let w : V := q.2.1
  have hwz : Γ.Adj w z := by
    have hh := q.2.2.1.property
    change Γ.Adj w q.endpoint at hh
    rwa [hqend] at hh
  have hfw : f w=w := D.short_fixed f q.toWalk hqpath
    (by rw [BasedWalk.length_toWalk]) (hb.2 a hba) (by rw [hqend]; exact hz)
    w (by
      rw [BasedWalk.support_toWalk]
      change w ∈ [a,(q.1 : V),w,q.endpoint]
      simp)
  let q₂ : BasedWalk Γ 2 a := ⟨q.1,⟨q.2.1,PUnit.unit⟩⟩
  have haw : Γ.dist a w ≤ 2 := Γ.dist_le q₂.toWalk
  have hwe : w ≠ e := by intro hh; rw [hh,hae] at haw; omega
  have hcw := D.four_distance hcd hde hez hwz.symm hce hdz hwe
  have hsw := D.fixesStar_opposite f hc hfw hcw
  have hqfirst : (q.1 : V) ≠ b := by
    have hh := Γ.dist_le q.2.toWalk
    change Γ.dist (q.1 : V) q.endpoint ≤ 2 at hh
    rw [hqend] at hh
    intro heq
    rw [heq,hbz] at hh
    omega
  obtain ⟨t,hbt,hta,htc⟩ := hthick b a c
  have htw := D.four_distance hbt.symm hba q.1.property q.2.1.property hta.symm hqfirst hqnb.1
  have hst := D.fixesStar_opposite f hsw (hb.2 t hbt) (by rw [Γ.dist_comm]; exact htw)
  exact D.identity_of_chain hthick ⟨hbt.symm,hbc,hcd,htc.symm,hbd,hst,hb,hc,hd⟩

/-- An automorphism fixing the interior stars of a root and one exit is trivial. -/
theorem Geometry.root_rigidity
    (hthick : ∀ v a b, ∃ z, Γ.Adj v z ∧ z ≠ a ∧ z ≠ b)
    (f : Γ ≃g Γ) {a b : V} (p : Γ.Walk a b)
    (hp : p.IsPath) (hlen : p.length=4)
    (hstars : ∀ j, 0<j → j<4 → ∀ z, Γ.Adj (p.getVert j) z → f z=z)
    (z : V) (hadj : Γ.Adj b z) (hprev : z ≠ p.getVert 3) (hfix : f z=z) :
    ∀ v, f v=v := by
  have hedge (j : ℕ) (hj : j<4) : Γ.Adj (p.getVert j) (p.getVert (j+1)) :=
    p.adj_getVert_succ (by omega)
  have hne (i j : ℕ) (hi : i≤4) (hj : j≤4) (hij : i≠j) : p.getVert i ≠ p.getVert j := by
    intro heq
    exact hij (hp.getVert_injOn (by change i≤p.length; omega)
      (by change j≤p.length; omega) heq)
  have hb : p.getVert 4=b := by rw [←hlen,Walk.getVert_length]
  have h1 : FixesStar f (p.getVert 1) :=
    ⟨hstars 2 (by decide) (by decide) _ (hedge 1 (by decide)).symm,
      hstars 1 (by decide) (by decide)⟩
  have h2 : FixesStar f (p.getVert 2) :=
    ⟨hstars 1 (by decide) (by decide) _ (hedge 1 (by decide)),
      hstars 2 (by decide) (by decide)⟩
  have h3 : FixesStar f (p.getVert 3) :=
    ⟨hstars 2 (by decide) (by decide) _ (hedge 2 (by decide)),
      hstars 3 (by decide) (by decide)⟩
  exact D.root_rigidity_chain hthick f (hedge 1 (by decide)) (hedge 2 (by decide))
    (hedge 3 (by decide)) (by simpa only [hb] using hadj)
    (hne 3 1 (by decide) (by decide) (by decide))
    (hne 4 2 (by decide) (by decide) (by decide)) hprev h1 h2 h3 hfix

end SimpleGraph.GeneralizedQuadrangle
