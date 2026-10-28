module
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.Pair
public import Theory.GroupAction.RankTwoCosetCover.SmallCover
public import Theory.GroupAction.DihedralPolygon
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.QuadrangleRecognition
public import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Recognition through matching quadrangle completions

A common marked reflection relation produces an eight-cycle in the paired
completion. Five-path transitivity makes its diameter four. The whole
endpoint overlap gives actual covers to both factors, and girth eight in
the factors makes both projections injective. Thus the two marked group
completions are isomorphic. Smallness of the two factors alone is not used
to assert smallness of their pair.

This common-cover argument is the direct Cartan route of Aschbacher–Smith
F.4.10,16–17, pp.279,282–283; the U₄ application supplies the reflection
relation from the full-extension order bound.
-/

@[expose] public noncomputable section
open Subgroup Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
open SimpleGraph.PathTransitivePolygon.QuadrangleRecognition
namespace Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
universe u v w
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable {G : Type v} [Group G] {H : Type w} [Group H]
variable {α : RankTwoAmalgam L B R}
variable (c : FaithfulCompletion α (G := G)) (d : FaithfulCompletion α (G := H))

/-- Whole overlap passes to the actual paired image by its faithful first marking. -/
theorem pair_whole_overlap (hc : c.left.range ⊓ c.right.range=c.middle.range) :
    (c.pairCompletion d).left.range ⊓ (c.pairCompletion d).right.range=
      (c.pairCompletion d).middle.range := by
  let e := c.pairCompletion d
  apply le_antisymm _ (le_inf e.middle_le_left e.middle_le_right)
  rintro z ⟨⟨x,hx⟩,⟨y,hy⟩⟩
  have hxy : c.left x=c.right y := by
    have he := congrArg (c.pairFst d) (hx.trans hy.symm)
    simpa only [e,pairFst_left,pairFst_right] using he
  obtain ⟨b,hb⟩ := hc.le (show c.left x∈c.left.range⊓c.right.range from
    ⟨⟨x,rfl⟩,⟨y,hxy.symm⟩⟩)
  have hbx : α.left b=x := c.left_injective hb
  exact ⟨b,by change e.left _=z; rw [hbx]; exact hx⟩

private theorem cover_cycle_bound {X Y : Type*} [Group X] [Group Y]
    {P : Bool → Subgroup X} {Q : Bool → Subgroup Y} {f : X →* Y}
    (h : CoverData P Q f)
    (hg : ∀v (p : (graph Q).Walk v v),p.IsCycle → 8≤p.length) :
    ∀v (p : (graph P).Walk v v),p.IsCycle → 8≤p.length := by
  intro v p hp
  by_contra hn
  let q := (BasedWalk.ofWalk p).map h.hom
  have hq : q.Nonbacktracking :=
    (BasedWalk.nonbacktracking_map_iff h.hom (fun v => (h.neighbor_bijective v).1) _).mpr
      (BasedWalk.nonbacktracking_ofWalk_of_isCycle p hp)
  have hpath := isPath_of_nonbacktracking_of_cycle_bound
    (N:=7) (fun v p hp => by have := hg v p hp; omega) q hq (by omega)
  have he : q.endpoint=h.vertex v := by
    simp only [q,BasedWalk.endpoint_map,BasedWalk.endpoint_ofWalk]
    rfl
  have hh := (hpath.nil_iff_eq.mpr he.symm).length_eq_zero
  have hz : p.length=0 := by simpa only [BasedWalk.length_toWalk] using hh
  have := hp.three_le_length
  omega

private theorem eight_cycle {X : Type*} [Group X]
    {P : Bool → Subgroup X}
    (hg : ∀v (p : (graph P).Walk v v),p.IsCycle → 8≤p.length)
    (s t : X) (hs : s∈P false) (ht : t∈P true)
    (hsout : s∉P true) (htout : t∉P false)
    (hs2 : s^2=1) (ht2 : t^2=1) (hst : (s*t)^4=1) :
    ∃v,∃p : (graph P).Walk v v,p.IsCycle ∧ p.length=8 := by
  have hu : (graph P).UniqueGeodesicsBelow 4 := by
    intro x y p q hp hq hd
    by_contra hh
    obtain ⟨v,_,_,r,hr,hlen⟩ := (p.isPath_of_length_eq_dist hp).exists_isCycle_length_le_add_of_ne
      (q.isPath_of_length_eq_dist hq) hh
    have hb := hg v r hr
    omega
  let act : GroupAction.DihedralPolygon.BipartiteAction X (graph P) :=
    ⟨(·.type),(fun h => h.1),(fun g _ _ h => (translationGraphIso P g).toHom.map_adj h),
      (fun _ _ => rfl)⟩
  have hsx : s • RankTwo.base P false=RankTwo.base P false := by
    change s∈RankTwo.stabilizer P (RankTwo.base P false)
    simpa only [RankTwo.stabilizer,RankTwo.base,stabilizer_base] using hs
  have htl : t • RankTwo.base P true=RankTwo.base P true := by
    change t∈RankTwo.stabilizer P (RankTwo.base P true)
    simpa only [RankTwo.stabilizer,RankTwo.base,stabilizer_base] using ht
  have hsl : s • RankTwo.base P true≠RankTwo.base P true := by
    intro hh
    apply hsout
    change s∈RankTwo.stabilizer P (RankTwo.base P true) at hh
    simpa only [RankTwo.stabilizer,RankTwo.base,stabilizer_base] using hh
  have htx : t • RankTwo.base P false≠RankTwo.base P false := by
    intro hh
    apply htout
    change t∈RankTwo.stabilizer P (RankTwo.base P false) at hh
    simpa only [RankTwo.stabilizer,RankTwo.base,stabilizer_base] using hh
  let e : cycleGraph 8 ↪g (graph P) := GroupAction.DihedralPolygon.edgeEmbedding act
    (by decide : 1<4) hu (by decide : 0<4) le_rfl
    ⟨Bool.false_ne_true,incident_base P false true⟩ hs2 ht2 hsx hsl htl htx
    (by rw [hst,one_smul]) (by rw [hst,one_smul])
  exact (cycleGraph_isContained_iff (by decide : 2<8)).mp ⟨e.toCopy⟩

/-- Matching marked reflection relations make the paired completion small.
Five-path transitivity of that pair, together with girth eight in each
factor, then makes both projections isomorphisms. -/
theorem nonempty_mulEquiv_of_matching_quadrangle
    (hcO : c.left.range ⊓ c.right.range=c.middle.range)
    (hdO : d.left.range ⊓ d.right.range=d.middle.range)
    (hcG : ∀v (p : (graph c.cosetFamily).Walk v v),p.IsCycle → 8≤p.length)
    (hdG : ∀v (p : (graph d.cosetFamily).Walk v v),p.IsCycle → 8≤p.length)
    (htrans : ∀v,RootPathTransitive (graph (c.pairCompletion d).cosetFamily) (c.Pair d) v 5)
    (s : L) (t : R) (hs : s^2=1) (ht : t^2=1)
    (hsout : c.left s∉c.middle.range) (htout : c.right t∉c.middle.range)
    (hc : (c.left s*c.right t)^4=1) (hd : (d.left s*d.right t)^4=1) :
    Nonempty (G ≃* H) := by
  let e := c.pairCompletion d
  have heO := c.pair_whole_overlap d hcO
  have hf : CoverData e.cosetFamily c.cosetFamily (c.pairFst d) :=
    coverData_of_hom _ (by ext x; exact c.pairFst_left d x)
      (by ext x; exact c.pairFst_right d x) heO hcO
  have hg : CoverData e.cosetFamily d.cosetFamily (c.pairSnd d) :=
    coverData_of_hom _ (by ext x; exact c.pairSnd_left d x)
      (by ext x; exact c.pairSnd_right d x) heO hdO
  have hes : e.left s∉e.cosetFamily true := by
    intro hh
    obtain ⟨b,hb⟩ := heO.le ⟨⟨s,rfl⟩,hh⟩
    apply hsout
    refine ⟨b,?_⟩
    have hh := congrArg (c.pairFst d) hb
    simpa only [middle,MonoidHom.comp_apply,e,pairFst_left] using hh
  have het : e.right t∉e.cosetFamily false := by
    intro hh
    obtain ⟨b,hb⟩ := heO.le ⟨hh,⟨t,rfl⟩⟩
    apply htout
    refine ⟨b,?_⟩
    have hh := congrArg (c.pairFst d) hb
    simpa only [middle,MonoidHom.comp_apply,e,pairFst_left,pairFst_right] using hh
  have he4 : (e.left s*e.right t)^4=1 := by
    apply Subtype.ext
    apply Prod.ext
    · have h : c.pairFst d ((e.left s*e.right t)^4)=c.pairFst d 1 := by
        simpa only [map_pow,map_mul,map_one,e,pairFst_left,pairFst_right] using hc
      exact h
    · have h : c.pairSnd d ((e.left s*e.right t)^4)=c.pairSnd d 1 := by
        simpa only [map_pow,map_mul,map_one,e,pairSnd_left,pairSnd_right] using hd
      exact h
  have hex := eight_cycle (cover_cycle_bound hf hcG) (e.left s) (e.right t)
    ⟨s,rfl⟩ ⟨t,rfl⟩ hes het (by rw [←map_pow,hs,map_one]) (by rw [←map_pow,ht,map_one]) he4
  have conn := Subgroup.CosetGeometry.RankTwo.connected e.cosetFamily e.generated
  have hdiam : ∀v w,(graph e.cosetFamily).dist v w≤4 := by
    apply diameter_bound_of_five_endpoint_bound conn
    intro v p hp
    exact five_endpoint_bound
      (⟨fun g _ _ h => (translationGraphIso e.cosetFamily g).toHom.map_adj h⟩ :
        GraphAction (graph e.cosetFamily) (c.Pair d)) htrans (·.type) (fun h => h.1)
      (fun h => (same_orbit_iff e.cosetFamily _ _).mpr h) hex p hp
  have hif := hf.injective_of_diameter_lt_girth conn hdiam
    (fun v p hp => (show (4 : ℕ)<8 by decide).trans_le (hcG v p hp))
  have his := hg.injective_of_diameter_lt_girth conn hdiam
    (fun v p hp => (show (4 : ℕ)<8 by decide).trans_le (hdG v p hp))
  exact ⟨(MulEquiv.ofBijective (c.pairFst d) ⟨hif,hf.surjective⟩).symm.trans
    (MulEquiv.ofBijective (c.pairSnd d) ⟨his,hg.surjective⟩)⟩
end Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
