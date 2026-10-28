module
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.Pair
public import Theory.GroupAction.RankTwoCosetCover.SmallCover
public import Theory.GroupAction.DihedralPolygon
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.FiveGirth
public import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Exact marked equivalences from paired quadrangle completions

Two faithful completions with matching endpoint involutions are compared in
their actual paired completion. Girth eight and the common fourth-power
relation produce an embedded eight-cycle there; five-path transitivity makes
its diameter at most four. Both projections are then bijective coverings.
The resulting group equivalence retains the two endpoint maps pointwise.
No order bound on the paired completion is assumed.

This is the paired-cover argument of Aschbacher–Smith F.4.8–10,16–17,
printed pp.278–283. The proof follows the previously checked symplectic
marked comparison, with its geometric hypotheses exposed for the unitary
applications rather than importing a symplectic recognition theorem.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter5.UnitaryNativeLift.Paired
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
open SimpleGraph.PathTransitivePolygon.QuadrangleRecognition
universe u v w
variable {L D R : Type u} [Group L] [Group D] [Group R]
variable {α : RankTwoAmalgam L D R} {M : Type v} [Group M]
variable (c : RankTwoAmalgam.FaithfulCompletion α (G := M))

abbrev GirthEight : Prop :=
  ∀ v (p : (graph c.cosetFamily).Walk v v), p.IsCycle → 8 ≤ p.length

abbrev FiveTransitive : Prop :=
  ∀ v, RootPathTransitive (graph c.cosetFamily) M v 5

theorem connected : (graph c.cosetFamily).Connected :=
  Subgroup.CosetGeometry.RankTwo.connected c.cosetFamily c.generated

theorem graphAction : GraphAction (graph c.cosetFamily) M where
  map_adj g := (CosetGeometry.translationGraphIso c.cosetFamily g).toHom.map_adj

def bipartiteAction : GroupAction.DihedralPolygon.BipartiteAction M (graph c.cosetFamily) where
  color := (·.type)
  adjacent_color h := h.1
  smul_adj := (graphAction c).map_adj
  smul_color _ _ := rfl

theorem uniqueGeodesicsBelow_four (hg : GirthEight c) : (graph c.cosetFamily).UniqueGeodesicsBelow 4 := by
  intro x y p q hp hq hd
  by_contra hh
  obtain ⟨v,_,_,r,hr,hlen⟩ := (p.isPath_of_length_eq_dist hp).exists_isCycle_length_le_add_of_ne
    (q.isPath_of_length_eq_dist hq) hh
  have hb := hg v r hr
  omega

theorem exists_eight_cycle_of_involutions (hc : c.left.range ⊓ c.right.range = c.middle.range) (hg : GirthEight c) (s t : M)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : s^2=1) (ht2 : t^2=1) (hst : (s*t)^4=1) :
    ∃v,∃p : (graph c.cosetFamily).Walk v v,p.IsCycle ∧ p.length=8 := by
  have hsx : s • RankTwo.base c.cosetFamily false=RankTwo.base c.cosetFamily false := by
    change s∈RankTwo.stabilizer c.cosetFamily (RankTwo.base c.cosetFamily false)
    simpa only [RankTwo.stabilizer,RankTwo.base,stabilizer_base,RankTwoAmalgam.FaithfulCompletion.cosetFamily, Bool.cond_false] using hs
  have htl : t • RankTwo.base c.cosetFamily true=RankTwo.base c.cosetFamily true := by
    change t∈RankTwo.stabilizer c.cosetFamily (RankTwo.base c.cosetFamily true)
    simpa only [RankTwo.stabilizer,RankTwo.base,stabilizer_base,RankTwoAmalgam.FaithfulCompletion.cosetFamily, Bool.cond_true] using ht
  have hsl : s • RankTwo.base c.cosetFamily true≠RankTwo.base c.cosetFamily true := by
    intro hh
    have hh' : s∈c.right.range := by
      change s∈RankTwo.stabilizer c.cosetFamily (RankTwo.base c.cosetFamily true) at hh
      simpa only [RankTwo.stabilizer,RankTwo.base,stabilizer_base,RankTwoAmalgam.FaithfulCompletion.cosetFamily, Bool.cond_true] using hh
    exact hsout (hc ▸ show s∈c.left.range⊓c.right.range from ⟨hs,hh'⟩)
  have htx : t • RankTwo.base c.cosetFamily false≠RankTwo.base c.cosetFamily false := by
    intro hh
    have hh' : t∈c.left.range := by
      change t∈RankTwo.stabilizer c.cosetFamily (RankTwo.base c.cosetFamily false) at hh
      simpa only [RankTwo.stabilizer,RankTwo.base,stabilizer_base,RankTwoAmalgam.FaithfulCompletion.cosetFamily, Bool.cond_false] using hh
    exact htout (hc ▸ show t∈c.left.range⊓c.right.range from ⟨hh',ht⟩)
  let e : cycleGraph 8 ↪g (graph c.cosetFamily) := GroupAction.DihedralPolygon.edgeEmbedding (bipartiteAction c)
    (by decide : 1<4) (uniqueGeodesicsBelow_four c hg) (by decide : 0<4) le_rfl
    ⟨Bool.false_ne_true,incident_base c.cosetFamily false true⟩ hs2 ht2 hsx hsl htl htx
    (by rw [hst,one_smul]) (by rw [hst,one_smul])
  exact (cycleGraph_isContained_iff (by decide : 2<8)).mp ⟨e.toCopy⟩

theorem quadrangle_metric_of_involutions (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (hg : GirthEight c) (hfive : FiveTransitive c) (s t : M)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : s^2=1) (ht2 : t^2=1) (hst : (s*t)^4=1) :
    (∀v (p : (graph c.cosetFamily).Walk v v),p.IsCycle → 8≤p.length) ∧
    (∀v w,(graph c.cosetFamily).dist v w≤4) ∧
    (∃v,∃p : (graph c.cosetFamily).Walk v v,p.IsCycle ∧ p.length=8) := by
  have hex := exists_eight_cycle_of_involutions c hc hg s t hs ht hsout htout hs2 ht2 hst
  refine ⟨hg,diameter_bound_of_five_endpoint_bound (connected c) ?_,hex⟩
  intro v p hp
  exact five_endpoint_bound (graphAction c) hfive (·.type) (fun h => h.1)
    (fun h => (same_orbit_iff c.cosetFamily _ _).mpr h) hex p hp

theorem marked_pair_overlap {H : Type w} [Group H] (d : RankTwoAmalgam.FaithfulCompletion α (G := H))
    (hc : c.left.range ⊓ c.right.range = c.middle.range) :
    (c.pairCompletion d).left.range ⊓ (c.pairCompletion d).right.range =
      (c.pairCompletion d).middle.range := by
  let e := c.pairCompletion d
  apply le_antisymm _ (le_inf e.middle_le_left e.middle_le_right)
  rintro z ⟨⟨x,hx⟩,⟨y,hy⟩⟩
  have hxy : c.left x=c.right y := by
    have he := congrArg (c.pairFst d) (hx.trans hy.symm)
    simpa only [e,RankTwoAmalgam.FaithfulCompletion.pairFst_left,
      RankTwoAmalgam.FaithfulCompletion.pairFst_right] using he
  obtain ⟨b,hb⟩ := hc.le (show c.left x∈c.left.range⊓c.right.range from
    ⟨⟨x,rfl⟩,⟨y,hxy.symm⟩⟩)
  have hbx : α.left b=x :=
    c.left_injective hb
  exact ⟨b,by change e.left _=z; rw [hbx]; exact hx⟩

/-- Matching endpoint involutions with the quadrangle relation determine the actual
completion group; the whole overlap is retained in both projections. -/
theorem exists_marked_mulEquiv_of_matching_involutions {H : Type w} [Group H]
    (d : RankTwoAmalgam.FaithfulCompletion α (G := H))
    (hcO : c.left.range ⊓ c.right.range = c.middle.range)
    (hdO : d.left.range ⊓ d.right.range = d.middle.range)
    (hgc : GirthEight c) (hgd : GirthEight d)
    (hgp : GirthEight (c.pairCompletion d)) (htp : FiveTransitive (c.pairCompletion d))
    (s : L) (t : R)
    (hs : s^2=1) (ht : t^2=1)
    (hsout : c.left s∉c.middle.range) (htout : c.right t∉c.middle.range)
    (hc : (c.left s*c.right t)^4=1) (hd : (d.left s*d.right t)^4=1) :
    ∃ f : M ≃* H, (∀ x, f (c.left x) = d.left x) ∧
      (∀ x, f (c.right x) = d.right x) := by
  let e : RankTwoAmalgam.FaithfulCompletion α (G := c.Pair d) := c.pairCompletion d
  have hes : e.left s∉e.middle.range := by
    rintro ⟨b,hb⟩
    apply hsout
    refine ⟨b,?_⟩
    have hh := congrArg (c.pairFst d) hb
    simpa only [RankTwoAmalgam.FaithfulCompletion.middle, MonoidHom.comp_apply,
      e, RankTwoAmalgam.FaithfulCompletion.pairFst_left] using hh
  have het : e.right t∉e.middle.range := by
    rintro ⟨b,hb⟩
    apply htout
    refine ⟨b,?_⟩
    have hh := congrArg (c.pairFst d) hb
    simpa only [RankTwoAmalgam.FaithfulCompletion.middle, MonoidHom.comp_apply,
      e, RankTwoAmalgam.FaithfulCompletion.pairFst_left,
      RankTwoAmalgam.FaithfulCompletion.pairFst_right] using hh
  have he6 : (e.left s*e.right t)^4=1 := by
    apply Subtype.ext
    apply Prod.ext
    · have h : c.pairFst d ((e.left s*e.right t)^4)=c.pairFst d 1 := by
        simpa only [map_pow,map_mul,map_one,e,
          RankTwoAmalgam.FaithfulCompletion.pairFst_left,
          RankTwoAmalgam.FaithfulCompletion.pairFst_right] using hc
      exact h
    · have h : c.pairSnd d ((e.left s*e.right t)^4)=c.pairSnd d 1 := by
        simpa only [map_pow,map_mul,map_one,e,
          RankTwoAmalgam.FaithfulCompletion.pairSnd_left,
          RankTwoAmalgam.FaithfulCompletion.pairSnd_right] using hd
      exact h
  have heO := marked_pair_overlap c d hcO
  have hdiam := (quadrangle_metric_of_involutions e heO hgp htp (e.left s) (e.right t)
    ⟨s,rfl⟩ ⟨t,rfl⟩ hes het (by rw [←map_pow,hs,map_one])
      (by rw [←map_pow,ht,map_one]) he6).2.1
  have hf : CoverData e.cosetFamily c.cosetFamily (c.pairFst d) :=
    RankTwoAmalgam.FaithfulCompletion.coverData_of_hom _
      (by ext x; exact c.pairFst_left d x) (by ext x; exact c.pairFst_right d x) heO hcO
  have hg : CoverData e.cosetFamily d.cosetFamily (c.pairSnd d) :=
    RankTwoAmalgam.FaithfulCompletion.coverData_of_hom _
      (by ext x; exact c.pairSnd_left d x) (by ext x; exact c.pairSnd_right d x) heO hdO
  have hif := hf.injective_of_diameter_lt_girth (connected e) hdiam
    (fun v p hp => (show (4 : ℕ) < 8 by decide).trans_le (hgc v p hp))
  have his := hg.injective_of_diameter_lt_girth (connected e) hdiam
    (fun v p hp => (show (4 : ℕ) < 8 by decide).trans_le (hgd v p hp))
  let f := (MulEquiv.ofBijective (c.pairFst d) ⟨hif,hf.surjective⟩).symm.trans
    (MulEquiv.ofBijective (c.pairSnd d) ⟨his,hg.surjective⟩)
  refine ⟨f, ?_, ?_⟩
  · intro x
    change c.pairSnd d ((MulEquiv.ofBijective (c.pairFst d) ⟨hif,hf.surjective⟩).symm (c.left x)) = _
    rw [←c.pairFst_left d x]
    exact (congrArg (c.pairSnd d)
      ((MulEquiv.ofBijective (c.pairFst d) ⟨hif,hf.surjective⟩).symm_apply_apply _)).trans
        (c.pairSnd_left d x)
  · intro x
    change c.pairSnd d ((MulEquiv.ofBijective (c.pairFst d) ⟨hif,hf.surjective⟩).symm (c.right x)) = _
    rw [←c.pairFst_right d x]
    exact (congrArg (c.pairSnd d)
      ((MulEquiv.ofBijective (c.pairFst d) ⟨hif,hf.surjective⟩).symm_apply_apply _)).trans
        (c.pairSnd_right d x)


end CFSG.Quasithin.Chapter5.UnitaryNativeLift.Paired
