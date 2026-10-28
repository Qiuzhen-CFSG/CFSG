module
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.ReeFour
public import Theory.SpecificGroups.ReeF4.SourceCompletion.LocalGeometry
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.OverlapCover
public import Theory.GroupTheory.Amalgam.Reversal
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.SevenGirth

/-!
# Local geometry in every whole-overlap general Ree completion

The two canonical pushout coverings transfer the native nine-path actions and
valences q+1, q²+1 to a faithful completion with its marked whole overlap.
Thickness and the short-complement argument then exclude all cycles below
sixteen. Neither finite ambient order nor generation of an ambient overgroup
is assumed; generation is only in the supplied completion.

These prove the local geometric part of F.4.6 for positive Ree parameters.
A sixteen-cycle, an order bound and group recognition are further obligations.
Source: Aschbacher–Smith F.3.3–6 and F.4.5–6, printed pp.270–272,275–277
(`refs/quasithin.pdf`). The long-prefix argument extends the checked
PathTransitivePolygon.SevenGirth proof to prefix lengths eight and nine.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour
open Theory.GroupTheory Subgroup Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
open GreenBook.LieModels

/-- A faithful completion in the surviving linear/Suzuki orientation. -/
abbrev Completion (m : ℕ) (G : Type*) [Group G] :=
  RankTwoAmalgam.FaithfulCompletion
    (RankTwoAmalgam.ofSubgroups
      (ReeF4.Parabolics.parabolic m .linear) (ReeF4.Parabolics.borel m)
      (ReeF4.Parabolics.parabolic m .suzuki)
      (ReeF4.Parabolics.borel_le_parabolic m .linear)
      (ReeF4.Parabolics.borel_le_parabolic m .suzuki)) (G := G)

/-- The actual native parabolic inclusions supply the comparison completion. -/
@[expose] def modelCompletion (m : ℕ) : Completion m (ReeF4.Model m) :=
  RankTwoAmalgam.FaithfulCompletion.ofSubgroups
    (ReeF4.Parabolics.parabolic m .linear) (ReeF4.Parabolics.borel m)
    (ReeF4.Parabolics.parabolic m .suzuki)
    (ReeF4.Parabolics.borel_le_parabolic m .linear)
    (ReeF4.Parabolics.borel_le_parabolic m .suzuki)
    (by rw [sup_comm]; exact ReeFour.parabolics_generate m)

/-- The native middle is the independently defined whole root Borel. -/
theorem model_overlap (m : ℕ) :
    (modelCompletion m).left.range ⊓ (modelCompletion m).right.range =
      (modelCompletion m).middle.range := by
  rw [modelCompletion, RankTwoAmalgam.FaithfulCompletion.ofSubgroups_left_range,
    RankTwoAmalgam.FaithfulCompletion.ofSubgroups_right_range,
    RankTwoAmalgam.FaithfulCompletion.ofSubgroups_middle_range, inf_comm]
  exact ReeFour.overlap m

/-- The native vertex family retains the marked source orientation. -/
theorem model_family (m : ℕ) :
    (modelCompletion m).cosetFamily = ReeF4.SourceCompletion.family m := by
  funext i
  cases i <;> exact range_subtype _

namespace Girth
open SimpleGraph.BasedWalk
variable {V A : Type*} [Group A] [MulAction A V] {G : SimpleGraph V}

-- The complementary-path argument of PathTransitivePolygon.SevenGirth,
-- used here at k=6 and k=7 for the Ree octagon.
private def actionIso (ha : GraphAction G A) (a : A) : G ≃g G where
  toEquiv := MulAction.toPerm a
  map_rel_iff' := ha.adj_iff a

private theorem no_cycle_of_transitive_long_prefix
    (ha : GraphAction G A)
    (hthick : ∀ v a b : V,∃z,G.Adj v z ∧ z≠a ∧ z≠b)
    {k : ℕ} (hk : 3 ≤ k)
    (ht : ∀v,RootPathTransitive G A v (k+2))
    (hg : ∀v(c:G.Walk v v),c.IsCycle → 2*k-2<c.length)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hl : c.length=2*k) : False := by
  have hlen : (c.take (k+1)).length=k+1 := by rw [Walk.take_length,hl,Nat.min_eq_left (by omega)]
  let p : BasedWalk G (k+1) u := hlen ▸ BasedWalk.ofWalk (c.take (k+1))
  have hp : p.Nonbacktracking := (BasedWalk.nonbacktracking_cast hlen _).mpr
    (BasedWalk.nonbacktracking_ofWalk_of_isPath _ (hc.isPath_take (by omega)))
  have hpend : p.endpoint=c.getVert (k+1) := by
    simp only [p,BasedWalk.endpoint_cast,BasedWalk.endpoint_ofWalk]
  have hprev : p.penultimate=c.getVert k := by
    have hget (n : ℕ) {x : V} (w : BasedWalk G (n+1) x) :
        w.penultimate=w.toWalk.getVert n := by
      induction n generalizing x with
      | zero => rfl
      | succ n ih => exact ih w.2
    rw [hget]
    have he : p.toWalk = (c.take (k+1)).copy rfl hpend.symm := by
      apply Walk.support_injective
      simp only [Walk.support_copy,BasedWalk.support_toWalk,p,BasedWalk.vertices_cast,
        BasedWalk.vertices_ofWalk]
    rw [he,Walk.getVert_copy,Walk.take_getVert,Nat.min_eq_right (by omega)]
  let z := c.getVert (k+2)
  have hz : G.Adj p.endpoint z := by
    rw [hpend]
    exact c.adj_getVert_succ (by omega)
  have hzprev : z ≠ p.penultimate := by
    rw [hprev]
    intro he
    have hi := hc.getVert_injOn' (by dsimp; omega) (by dsimp; omega) he
    omega
  obtain ⟨w,hw,hwz,hwprev⟩ := hthick p.endpoint z p.penultimate
  obtain ⟨a,hau,he⟩ := ht u (p.snoc hz) (p.snoc hw)
    ((nonbacktracking_snoc_iff p hz).mpr ⟨hp,hzprev⟩)
    ((nonbacktracking_snoc_iff p hw).mpr ⟨hp,hwprev⟩)
  have haend : a • z=w := by
    have hh := endpoint_smul_of_vertices ha a (p.snoc hz) (p.snoc hw) he
    simpa only [endpoint_snoc] using hh
  have heprefix : p.vertices.map (a • ·)=p.vertices := by
    have hh := congrArg (List.take (k+2)) he
    have htake (z : V) (hz : G.Adj p.endpoint z) :
        (p.snoc hz).vertices.take (k+2) = p.vertices := by
      rw [vertices_snoc,←length_vertices p,List.take_left]
    rw [←List.map_take,htake z hz,htake w hw] at hh
    exact hh
  have hafix : a • p.endpoint=p.endpoint := endpoint_smul_of_vertices ha a p p heprefix
  let q := BasedWalk.ofWalk (c.drop (k+1))
  have hq : q.Nonbacktracking := nonbacktracking_ofWalk_of_isPath _ (hc.isPath_drop (by omega))
  have hfix := BasedWalk.fixes_short_walk hg q hq (by
    simp only [Walk.drop_length,hl]
    omega) (actionIso ha a) (by
      change a • c.getVert (k+1)=c.getVert (k+1)
      simpa only [hpend] using hafix)
    (by
      change a • q.endpoint=q.endpoint
      simpa only [q,BasedWalk.endpoint_ofWalk] using hau)
  have hzmem : z ∈ q.vertices := by
    change z ∈ (BasedWalk.ofWalk (c.drop (k+1))).vertices
    rw [BasedWalk.vertices_ofWalk]
    have hh := (c.drop (k+1)).getVert_mem_support 1
    simpa only [Walk.drop_getVert,Nat.add_assoc] using hh
  exact hwz (haend.symm.trans (hfix z hzmem))


private theorem bound (ha : GraphAction G A)
    (hthick : ∀ v a b : V, ∃ z, G.Adj v z ∧ z ≠ a ∧ z ≠ b)
    (ht : ∀ v, RootPathTransitive G A v 9)
    (color : V → Bool) (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (v : V) (c : G.Walk v v) (hc : c.IsCycle) : 16 ≤ c.length := by
  have hdeg : HasTwoNeighbors G := by
    intro x y
    obtain ⟨z,hz,hy,_⟩ := hthick x y y
    exact ⟨z,hz,hy⟩
  have hg12 := cycle_bound_of_seven_transitive ha hthick
    (fun x => (ht x).mono hdeg (by decide)) color hcolor
  have heven (x : V) (w : G.Walk x x) : Even w.length :=
    (QuadrangleRecognition.even_length_iff color hcolor w).mpr rfl
  have hg14 : ∀ x (w : G.Walk x x), w.IsCycle → 14 ≤ w.length := by
    intro x w hw
    have h12 := hg12 x w hw
    obtain ⟨k,hk⟩ := heven x w
    by_contra h
    have hh : w.length = 12 := by omega
    exact no_cycle_of_transitive_long_prefix ha hthick (by decide : 3 ≤ 6)
      (fun x => (ht x).mono hdeg (by decide))
      (fun x w hw => by have := hg12 x w hw; omega) w hw hh
  have h14 := hg14 v c hc
  obtain ⟨k,hk⟩ := heven v c
  by_contra h
  have hh : c.length = 14 := by omega
  exact no_cycle_of_transitive_long_prefix ha hthick (by decide : 3 ≤ 7) ht
    (fun x w hw => by have := hg14 x w hw; omega) c hc hh
end Girth

namespace Completion
variable {m : ℕ} {G : Type*} [Group G] (c : Completion m G)

abbrev Vertex := RankTwo.Vertex c.cosetFamily
abbrev graph := RankTwo.graph c.cosetFamily

theorem connected : c.graph.Connected := RankTwo.connected c.cosetFamily c.generated

theorem graphAction : GraphAction c.graph G where
  map_adj g := (translationGraphIso c.cosetFamily g).toHom.map_adj

/-- Both vertex types inherit nine-path transitivity through the common pushout. -/
theorem nine_transitive (hm : 0 < m)
    (hc : c.left.range ⊓ c.right.range = c.middle.range) (v : c.Vertex) :
    RootPathTransitive c.graph G v 9 := by
  obtain ⟨g,hg⟩ := exists_smul_base c.cosetFamily v
  have hmodel : RootPathTransitive (RankTwo.graph (modelCompletion m).cosetFamily)
      (ReeF4.Model m) (RankTwo.base (modelCompletion m).cosetFamily v.type) 9 := by
    rw [model_family]
    exact ReeF4.SourceCompletion.nine_transitive m hm _
  have hb := (RankTwoAmalgam.Universal.rootPathTransitive_iff_of_overlap
    _ c (modelCompletion m) hc (model_overlap m) v.type 9).mpr hmodel
  simpa only [hg] using RootPathTransitive.smul c.graphAction hb g

/-- Coverings preserve the two literal full-parabolic valences. -/
theorem card_neighbors (hm : 0 < m)
    (hc : c.left.range ⊓ c.right.range = c.middle.range) (v : c.Vertex) :
    Nat.card (c.graph.neighborSet v) =
      (if v.type then (2^(2*m+1))^2 else 2^(2*m+1)) + 1 := by
  obtain ⟨g,hg⟩ := exists_smul_base c.cosetFamily v
  have hbase : Nat.card (c.graph.neighborSet (RankTwo.base c.cosetFamily v.type)) =
      (if v.type then (2^(2*m+1))^2 else 2^(2*m+1)) + 1 := by
    have cover := RankTwoAmalgam.Universal.coverData_of_overlap _ c hc
    have native := RankTwoAmalgam.Universal.coverData_of_overlap _
      (modelCompletion m) (model_overlap m)
    have h1 := Nat.card_congr (Equiv.ofBijective _
      (cover.neighbor_bijective (RankTwo.base _ v.type)))
    have h2 := Nat.card_congr (Equiv.ofBijective _
      (native.neighbor_bijective (RankTwo.base _ v.type)))
    change Nat.card _ = Nat.card ((RankTwo.graph c.cosetFamily).neighborSet
      (cover.vertex (RankTwo.base _ v.type))) at h1
    change Nat.card _ = Nat.card ((RankTwo.graph (modelCompletion m).cosetFamily).neighborSet
      (native.vertex (RankTwo.base _ v.type))) at h2
    rw [CoverData.vertex_base] at h1 h2
    rw [←h1,h2,model_family]
    exact ReeF4.SourceCompletion.card_neighbors m hm _
  have hh := Nat.card_congr
    ((translationGraphIso c.cosetFamily g).mapNeighborSet (RankTwo.base c.cosetFamily v.type))
  change Nat.card (c.graph.neighborSet (RankTwo.base c.cosetFamily v.type)) =
    Nat.card (c.graph.neighborSet (g • RankTwo.base c.cosetFamily v.type)) at hh
  rw [hg] at hh
  exact hh.symm.trans hbase

/-- Every vertex has a neighbor outside any prescribed pair. -/
theorem thick (hm : 0 < m) (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (v a b : c.Vertex) : ∃ z, c.graph.Adj v z ∧ z ≠ a ∧ z ≠ b := by
  classical
  have hq : 1 < 2^(2*m+1) := Nat.one_lt_pow (by omega) (by decide)
  have hcard : 2 < Nat.card (c.graph.neighborSet v) := by
    rw [c.card_neighbors hm hc]
    cases v.type <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith
  let : Finite (c.graph.neighborSet v) := Nat.finite_of_card_ne_zero (by omega)
  let := Fintype.ofFinite (c.graph.neighborSet v)
  rw [Nat.card_eq_fintype_card] at hcard
  obtain ⟨x,y,z,hxy,hxz,hyz⟩ := Fintype.two_lt_card_iff.mp hcard
  by_contra hh
  push Not at hh
  have choices (w : c.graph.neighborSet v) : w.val = a ∨ w.val = b := by
    by_cases ha : w.val = a
    · exact Or.inl ha
    · exact Or.inr (hh w.val w.property ha)
  have hxy' : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
  have hxz' : x.val ≠ z.val := fun h => hxz (Subtype.ext h)
  have hyz' : y.val ≠ z.val := fun h => hyz (Subtype.ext h)
  rcases choices x with hx | hx <;> rcases choices y with hy | hy <;>
    rcases choices z with hz | hz <;> simp_all

/-- The literal completion has no simple cycle shorter than sixteen. -/
theorem cycle_length_ge_sixteen (hm : 0 < m)
    (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (v : c.Vertex) (p : c.graph.Walk v v) (hp : p.IsCycle) : 16 ≤ p.length :=
  Girth.bound c.graphAction (c.thick hm hc) (c.nine_transitive hm hc)
    (·.type) (fun h => h.1) v p hp

end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.GeneralReeFour
