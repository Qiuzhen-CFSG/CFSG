module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CentralFixedRegular
public import Theory.GroupAction.CubicTree.TrackArcTransport
public import Theory.GroupAction.CubicTree.CentralLocalConjugation

/-!
# Companion pairs for one-edge central blocks

A finite even track arc of length at most the first singular length can be
reflected by the group action. Reflecting a short fixed interval gives the
companion immediately. Otherwise, reflect a four-edge arc around a central
endpoint. The margin comparison puts the new fixed endpoints within one step
of the old ones; regularity forces their vertex types to agree, hence the
endpoints coincide. The resulting pair has adjacent one-edge central blocks.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), first half of
(6.7), printed pp.398–399.
-/

@[expose] public section

open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
open Subgroup.CosetGeometry
variable {G : Type*} [Group G] {F : Bool → Subgroup G}

private theorem track_arc_getElem? (t : Track (RankTwo.graph F) G)
    (a : ℤ) (n k : ℕ) (hk : k ≤ n) :
    (t.arc a n).vertices[k]? = some (t.vertex (a+k)) := by
  rw [← BasedWalk.support_toWalk, ← Walk.getVert_eq_support_getElem? _ (by simpa only [BasedWalk.length_toWalk] using hk),
    t.arc_getVert a n k hk]

theorem CubicTreeAction.exists_track_interval_reflection (h : CubicTreeAction F)
    {s : ℕ}
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) (a b : ℤ) (hab : a ≤ b)
    (heven : Even (b-a)) (hlen : (b-a).toNat ≤ s) :
    ∃ g : G, ∀ i, a ≤ i → i ≤ b → g • t.vertex i = t.vertex (a+b-i) := by
  let n := (b-a).toNat
  have hn : (n : ℤ) = b-a := by dsimp only [n]; omega
  have hevenN : Even n := by
    obtain ⟨k, hk⟩ := heven
    refine ⟨k.toNat, ?_⟩
    omega
  have ht : (t.vertex a).type = (t.vertex b).type := by
    have hh := (RankTwo.even_walk_iff F (t.arc a n).toWalk).1
      (by simpa only [BasedWalk.length_toWalk] using hevenN)
    simpa only [t.arc_endpoint, show a+(n:ℤ)=b by omega] using hh
  obtain ⟨g, hg⟩ := h.congruent_arcs s hshort hlen (t.arc a n)
    (t.reverse.arc (-b) n) (t.arc_nonbacktracking _ _)
    (t.reverse.arc_nonbacktracking _ _) (by simpa only [Track.reverse, neg_neg] using ht)
  refine ⟨g, ?_⟩
  intro i hai hib
  let k := (i-a).toNat
  have hk : k ≤ n := by dsimp only [k]; omega
  have hkcast : (k : ℤ) = i-a := by dsimp only [k]; omega
  have he := congrArg (fun l : List (RankTwo.Vertex F) => l[k]?) hg
  simp only [List.getElem?_map, track_arc_getElem? _ _ _ _ hk, Option.map_some,
    Option.some.injEq] at he
  simpa only [Track.reverse, show a+(k:ℤ)=i by omega,
    show -(-b+(k:ℤ))=a+b-i by omega] using he

private theorem graphAction : GraphAction (RankTwo.graph F) G :=
  ⟨fun g _ _ h => (translationGraphIso F g).toHom.map_adj h⟩

private theorem equal_indices_of_near_of_type_eq (t : Track (RankTwo.graph F) G)
    {a b : ℤ} (hnear : a-1 ≤ b ∧ b ≤ a+1)
    (ht : (t.vertex a).type = (t.vertex b).type) : a=b := by
  by_contra hn
  have he : b=a-1 ∨ b=a+1 := by omega
  rcases he with he | he
  · have ha := (t.adjacent b).1
    rw [show b+1=a by omega] at ha
    exact ha ht.symm
  · exact (t.adjacent a).1 (by simpa only [he] using ht)

private theorem centralInterval_bounds_of_central_neighbor_failures
    (h : CubicTreeAction F) {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z) (j : ℤ)
    (hj : t.CentralEdge z j) (hm : ¬t.CentralEdge z (j-1))
    (hp : ¬t.CentralEdge z (j+1)) :
    d.centralLeft=j ∧ d.centralRight=j+1 := by
  have hc := (h.centralEdge_iff_in_centralInterval hs hshort t hz d j).1 hj
  have hl : ¬(d.centralLeft ≤ j-1 ∧ j-1<d.centralRight) := by
    intro hi
    exact hm ((h.centralEdge_iff_in_centralInterval hs hshort t hz d _).2 hi)
  have hr : ¬(d.centralLeft ≤ j+1 ∧ j+1<d.centralRight) := by
    intro hi
    exact hp ((h.centralEdge_iff_in_centralInterval hs hshort t hz d _).2 hi)
  omega


private theorem exists_short_central_companions (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G) {z : G} (hz : t.CentralInvolution z)
    (d : t.CentralInterval z) (hw : d.centralRight-d.centralLeft=1)
    (heven : Even (d.fixedRight-d.fixedLeft))
    (hlen : (d.fixedRight-d.fixedLeft).toNat ≤ s) :
    ∃ u v : G, ∃ _hu : t.CentralInvolution u, ∃ _hv : t.CentralInvolution v,
      ∃ du : t.CentralInterval u, ∃ dv : t.CentralInterval v,
      du.fixedLeft=dv.fixedLeft ∧ du.fixedRight=dv.fixedRight ∧
      du.centralRight-du.centralLeft=1 ∧ dv.centralRight-dv.centralLeft=1 ∧
      dv.centralRight=du.centralLeft := by
  have hL := d.centralLeft_mem
  have hR := d.centralRight_mem
  obtain ⟨g, hg⟩ := h.exists_track_interval_reflection hshort t d.fixedLeft d.fixedRight
    (by omega) heven hlen
  let e := d.localReflection h.tree.2 graphAction h.card_neighbor g hg
  have hz' := hz.localReflection h.tree.2 graphAction h.card_neighbor d g hg
  have hm := h.central_margin_comparison hs hshort t hz hz d d
  have hml := d.leftMargin_cast
  have hmr := d.rightMargin_cast
  obtain ⟨k, hk⟩ := heven
  have hew : e.centralRight-e.centralLeft=1 := by
    dsimp only [e, Track.CentralInterval.localReflection]
    omega
  have hadj : e.centralRight=d.centralLeft ∨ d.centralRight=e.centralLeft := by
    dsimp only [e, Track.CentralInterval.localReflection]
    omega
  rcases hadj with hadj | hadj
  · exact ⟨z, _, hz, hz', d, e, rfl, rfl, hw, hew, hadj⟩
  · exact ⟨_, z, hz', hz, e, d, rfl, rfl, hew, hw, hadj⟩

/-- A width-one central block yields a companion pair with the same fixed
interval and adjacent central edges. The pair may replace the initial
involution, as in the source's short-fixed-interval alternative. -/
theorem CubicTreeAction.exists_central_companions (h : CubicTreeAction F)
    {s : ℕ} (hs : 5 ≤ s)
    (hshort : ∀ (k : ℕ) (v : RankTwo.Vertex F) (p : BasedWalk (RankTwo.graph F) k v),
      k < s → p.Nonbacktracking → RightRegular (A := G) p)
    {v : RankTwo.Vertex F} (p : BasedWalk (RankTwo.graph F) s v)
    (hp : p.Nonbacktracking) (hn : ¬RightRegular (A := G) p)
    (t : Track (RankTwo.graph F) G)
    (hfinite : ∀ u, t.CentralInvolution u → u ∉ t.fixer)
    (heven : ∀ u, t.CentralInvolution u → ∀ d : t.CentralInterval u,
      Even (d.fixedRight-d.fixedLeft))
    {z : G} (hz : t.CentralInvolution z) (d : t.CentralInterval z)
    (hw : d.centralRight-d.centralLeft=1) :
    ∃ u v : G, ∃ _hu : t.CentralInvolution u, ∃ _hv : t.CentralInvolution v,
      ∃ du : t.CentralInterval u, ∃ dv : t.CentralInterval v,
      du.fixedLeft=dv.fixedLeft ∧ du.fixedRight=dv.fixedRight ∧
      du.centralRight-du.centralLeft=1 ∧ dv.centralRight-dv.centralLeft=1 ∧
      dv.centralRight=du.centralLeft := by
  classical
  by_cases hsmall : ∃ u, ∃ hu : t.CentralInvolution u, ∃ du : t.CentralInterval u,
      du.centralRight-du.centralLeft=1 ∧ (du.fixedRight-du.fixedLeft).toNat ≤ s
  · obtain ⟨u, hu, du, hwu, hlen⟩ := hsmall
    exact exists_short_central_companions h hs hshort t hu du hwu (heven u hu du) hlen
  have hlong (u : G) (hu : t.CentralInvolution u) (du : t.CentralInterval u)
      (hwu : du.centralRight-du.centralLeft=1) :
      s ≤ (du.fixedRight-du.fixedLeft).toNat := by
    by_contra hh
    exact hsmall ⟨u, hu, du, hwu, by omega⟩
  have hm := h.central_margin_comparison hs hshort t hz hz d d
  have hml := d.leftMargin_cast
  have hmr := d.rightMargin_cast
  obtain ⟨k, hk⟩ := heven z hz d
  obtain ⟨a, ha⟩ : ∃ a : ℤ,
      (a=d.centralLeft ∧ d.leftMargin=d.rightMargin+1) ∨
      (a=d.centralLeft+1 ∧ d.rightMargin=d.leftMargin+1) := by
    by_cases hle : d.leftMargin ≤ d.rightMargin
    · exact ⟨d.centralLeft+1, Or.inr ⟨rfl, by omega⟩⟩
    · exact ⟨d.centralLeft, Or.inl ⟨rfl, by omega⟩⟩
  obtain ⟨g, hg⟩ := h.exists_track_interval_reflection hshort t (a-2) (a+2)
    (by omega) ⟨2, by omega⟩ (by omega)
  have hab : a-2 ≤ d.centralLeft-1 ∧ d.centralLeft+2 ≤ a+2 := by
    rcases ha with ha | ha <;> omega
  have htransport (i : ℤ) (hi : d.centralLeft-1 ≤ i) (hir : i ≤ d.centralLeft+1) :
      t.CentralEdge ((MulAut.conj g) z) (2*a-i-1) ↔ t.CentralEdge z i := by
    apply t.centralEdge_local_reflection_iff g i (2*a-i-1)
    · convert hg i (by omega) (by omega) using 1
      congr 1
      omega
    · convert hg (i+1) (by omega) (by omega) using 1
      congr 1
      omega
  let j := 2*a-d.centralLeft-1
  have hj : t.CentralEdge ((MulAut.conj g) z) j :=
    (htransport d.centralLeft (by omega) (by omega)).2
      (d.central d.centralLeft le_rfl (by omega))
  have hjm : ¬t.CentralEdge ((MulAut.conj g) z) (j-1) := by
    intro hh
    apply d.not_central_right
    have ht := htransport d.centralRight (by omega) (by omega)
    apply ht.1
    convert hh using 1
    dsimp only [j]
    omega
  have hjp : ¬t.CentralEdge ((MulAut.conj g) z) (j+1) := by
    intro hh
    apply d.not_central_left
    apply (htransport (d.centralLeft-1) (by omega) (by omega)).1
    convert hh using 1
    dsimp only [j]
    omega
  have hz' : t.CentralInvolution ((MulAut.conj g) z) :=
    ⟨(orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective z).trans hz.1,
      j, hj⟩
  obtain ⟨e⟩ := h.exists_centralInterval_of_not_mem_fixer t _ hz' (hfinite _ hz')
  obtain ⟨heL, heR⟩ := centralInterval_bounds_of_central_neighbor_failures
    h hs hshort t hz' e j hj hjm hjp
  have hew : e.centralRight-e.centralLeft=1 := by omega
  have hdends := h.regular_endpoints (by omega : 0<s) hshort p hp hn
    (hlong z hz d hw) (t.arc d.fixedLeft (d.fixedRight-d.fixedLeft).toNat)
    (t.arc_nonbacktracking _ _) (h.centralInterval_arc_regular t d)
  have heends := h.regular_endpoints (by omega : 0<s) hshort p hp hn
    (hlong _ hz' e hew) (t.arc e.fixedLeft (e.fixedRight-e.fixedLeft).toNat)
    (t.arc_nonbacktracking _ _) (h.centralInterval_arc_regular t e)
  have dL := d.centralLeft_mem
  have dR := d.centralRight_mem
  have eL := e.centralLeft_mem
  have eR := e.centralRight_mem
  have hdcast : d.fixedLeft+((d.fixedRight-d.fixedLeft).toNat:ℤ)=d.fixedRight := by omega
  have hecast : e.fixedLeft+((e.fixedRight-e.fixedLeft).toNat:ℤ)=e.fixedRight := by omega
  simp only [t.arc_endpoint, hdcast, hecast] at hdends heends
  have hem := h.central_margin_comparison hs hshort t hz hz' d e
  have hdm := h.central_margin_comparison hs hshort t hz' hz e d
  have hel := e.leftMargin_cast
  have her := e.rightMargin_cast
  have hnearL : d.fixedLeft-1 ≤ e.fixedLeft ∧ e.fixedLeft ≤ d.fixedLeft+1 := by
    dsimp only [j] at heL heR
    rcases ha with ha | ha <;> omega
  have hnearR : d.fixedRight-1 ≤ e.fixedRight ∧ e.fixedRight ≤ d.fixedRight+1 := by
    dsimp only [j] at heL heR
    rcases ha with ha | ha <;> omega
  have hfixL := equal_indices_of_near_of_type_eq t hnearL (hdends.1.trans heends.1.symm)
  have hfixR := equal_indices_of_near_of_type_eq t hnearR (hdends.2.1.trans heends.2.1.symm)
  rcases ha with ha | ha
  · exact ⟨z, _, hz, hz', d, e, hfixL, hfixR, hw, hew, by dsimp only [j] at heR; omega⟩
  · exact ⟨_, z, hz', hz, e, d, hfixL.symm, hfixR.symm, hew, hw,
      by dsimp only [j] at heL; omega⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt
