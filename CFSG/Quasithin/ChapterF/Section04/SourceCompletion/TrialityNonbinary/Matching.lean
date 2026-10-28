module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityNonbinary.Census
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.Pair
public import Theory.GroupAction.RankTwoCosetCover.SmallCover
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.HexagonRecognition
public import Theory.GroupAction.DihedralPolygon
public import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Comparing full triality completions with matching marked reflections

A common pair of endpoint involutions satisfying the hexagon relation gives a
twelve-cycle in the paired completion. Its seven-path transitivity forces
diameter six. The two covering projections are then injective by girth,
giving an actual group isomorphism. This argument does not infer that the
pair of arbitrary small completions is small: the matching relation is an
explicit hypothesis, still to be obtained from the order bound.

Source: Aschbacher–Smith F.3.6, F.4.10 and F.4.12–17, pp.272,279,282–283.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
variable {m : ℕ} {hm : 0 < m} (E : SourceExtension m hm) {M : Type*} [Group M] (c : Completion E M)

private def completion_bipartiteAction :
    GroupAction.DihedralPolygon.BipartiteAction M (graph c.cosetFamily) where
  color := (·.type)
  adjacent_color h := h.1
  smul_adj := (completion_graphAction E c).map_adj
  smul_color _ _ := rfl

theorem uniqueGeodesicsBelow_six (hc : c.left.range ⊓ c.right.range = c.middle.range) : (graph c.cosetFamily).UniqueGeodesicsBelow 6 := by
  intro x y p q hp hq hd
  by_contra hh
  obtain ⟨v,_,_,r,hr,hlen⟩ := (p.isPath_of_length_eq_dist hp).exists_isCycle_length_le_add_of_ne
    (q.isPath_of_length_eq_dist hq) hh
  have hb := completion_cycle_length_ge_twelve E c hc v r hr
  omega

theorem exists_twelve_cycle_of_involutions (hc : c.left.range ⊓ c.right.range = c.middle.range) (s t : M)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : s^2=1) (ht2 : t^2=1) (hst : (s*t)^6=1) :
    ∃v,∃p : (graph c.cosetFamily).Walk v v,p.IsCycle ∧ p.length=12 := by
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
  let e : cycleGraph 12 ↪g (graph c.cosetFamily) := GroupAction.DihedralPolygon.edgeEmbedding (completion_bipartiteAction E c)
    (by decide : 1<6) (uniqueGeodesicsBelow_six E c hc) (by decide : 0<6) le_rfl
    ⟨Bool.false_ne_true,incident_base c.cosetFamily false true⟩ hs2 ht2 hsx hsl htl htx
    (by rw [hst,one_smul]) (by rw [hst,one_smul])
  exact (cycleGraph_isContained_iff (by decide : 2<12)).mp ⟨e.toCopy⟩

theorem hexagon_metric_of_involutions (hc : c.left.range ⊓ c.right.range = c.middle.range) (s t : M)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : s^2=1) (ht2 : t^2=1) (hst : (s*t)^6=1) :
    (∀v (p : (graph c.cosetFamily).Walk v v),p.IsCycle → 12≤p.length) ∧
    (∀v w,(graph c.cosetFamily).dist v w≤6) ∧
    (∃v,∃p : (graph c.cosetFamily).Walk v v,p.IsCycle ∧ p.length=12) := by
  have hex := exists_twelve_cycle_of_involutions E c hc s t hs ht hsout htout hs2 ht2 hst
  refine ⟨completion_cycle_length_ge_twelve E c hc,HexagonRecognition.diameter_bound_of_seven_endpoint_bound (completion_connected E c) ?_,hex⟩
  intro v p hp
  exact HexagonRecognition.seven_endpoint_bound (completion_graphAction E c) (completion_seven_transitive E c hc) (·.type) (fun h => h.1)
    (fun h => (same_orbit_iff c.cosetFamily _ _).mpr h) hex p hp

private theorem pair_overlap {H : Type*} [Group H] (d : Completion E H)
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
  have hbx : E.amalgam.left b=x :=
    c.left_injective hb
  exact ⟨b,by change e.left _=z; rw [hbx]; exact hx⟩

/-- Matching endpoint involutions with the hexagon relation determine the actual
completion group; the whole overlap is retained in both projections. -/
theorem exists_mulEquiv_of_matching_involutions {H : Type*} [Group H]
    (d : Completion E H)
    (hcO : c.left.range ⊓ c.right.range = c.middle.range)
    (hdO : d.left.range ⊓ d.right.range = d.middle.range)
    (s : E.left) (t : E.right)
    (hs : s^2=1) (ht : t^2=1)
    (hsout : c.left s∉c.middle.range) (htout : c.right t∉c.middle.range)
    (hc : (c.left s*c.right t)^6=1) (hd : (d.left s*d.right t)^6=1) :
    ∃ f : M ≃* H, (∀ x, f (c.left x) = d.left x) ∧
      (∀ x, f (c.right x) = d.right x) := by
  let e : Completion E (c.Pair d) := c.pairCompletion d
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
  have he6 : (e.left s*e.right t)^6=1 := by
    apply Subtype.ext
    apply Prod.ext
    · have h : c.pairFst d ((e.left s*e.right t)^6)=c.pairFst d 1 := by
        simpa only [map_pow,map_mul,map_one,e,
          RankTwoAmalgam.FaithfulCompletion.pairFst_left,
          RankTwoAmalgam.FaithfulCompletion.pairFst_right] using hc
      exact h
    · have h : c.pairSnd d ((e.left s*e.right t)^6)=c.pairSnd d 1 := by
        simpa only [map_pow,map_mul,map_one,e,
          RankTwoAmalgam.FaithfulCompletion.pairSnd_left,
          RankTwoAmalgam.FaithfulCompletion.pairSnd_right] using hd
      exact h
  have heO := pair_overlap E c d hcO
  have hdiam := (hexagon_metric_of_involutions E e heO (e.left s) (e.right t)
    ⟨s,rfl⟩ ⟨t,rfl⟩ hes het (by rw [←map_pow,hs,map_one])
      (by rw [←map_pow,ht,map_one]) he6).2.1
  have hf : CoverData e.cosetFamily c.cosetFamily (c.pairFst d) :=
    RankTwoAmalgam.FaithfulCompletion.coverData_of_hom _
      (by ext x; exact c.pairFst_left d x) (by ext x; exact c.pairFst_right d x) heO hcO
  have hg : CoverData e.cosetFamily d.cosetFamily (c.pairSnd d) :=
    RankTwoAmalgam.FaithfulCompletion.coverData_of_hom _
      (by ext x; exact c.pairSnd_left d x) (by ext x; exact c.pairSnd_right d x) heO hdO
  have hif := hf.injective_of_diameter_lt_girth (completion_connected E e) hdiam
    (fun v p hp => (show (6 : ℕ) < 12 by decide).trans_le (completion_cycle_length_ge_twelve E c hcO v p hp))
  have his := hg.injective_of_diameter_lt_girth (completion_connected E e) hdiam
    (fun v p hp => (show (6 : ℕ) < 12 by decide).trans_le (completion_cycle_length_ge_twelve E d hdO v p hp))
  let ef := MulEquiv.ofBijective (c.pairFst d) ⟨hif,hf.surjective⟩
  let es := MulEquiv.ofBijective (c.pairSnd d) ⟨his,hg.surjective⟩
  refine ⟨ef.symm.trans es,?_,?_⟩
  · intro x
    change es (ef.symm (c.left x)) = d.left x
    have he : ef (e.left x) = c.left x := c.pairFst_left d x
    rw [←he,ef.symm_apply_apply]
    exact c.pairSnd_left d x
  · intro x
    change es (ef.symm (c.right x)) = d.right x
    have he : ef (e.right x) = c.right x := c.pairFst_right d x
    rw [←he,ef.symm_apply_apply]
    exact c.pairSnd_right d x


end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityNonbinary
