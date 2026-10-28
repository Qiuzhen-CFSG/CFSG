module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.SymplecticFour.FixedApartment
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.Pair
public import Theory.GroupAction.RankTwoCosetCover.SmallCover
public import Mathlib.Combinatorics.SimpleGraph.Circulant

/-!
# Recognition of nonbinary symplectic extension completions

The original full-extension order bound supplies the literal canonical Weyl
relation by the fixed-apartment theorem. The model and source completions
therefore have matching involutions satisfying (st)⁴ = 1. Their paired
completion has an actual eight-cycle, hence diameter four by five-path
transitivity. Both projections are injective because their targets have
girth eight. This identifies the groups through their genuine common cover.

For q > 2 this proves isomorphism with the originally marked extension, a
strengthening justified by the proved Cartan alignment. No such strengthening
for arbitrary generalized Lie extensions, as discussed in F.4.9, is assumed.
Transport gives a normal Sp₄ subgroup with trivial centralizer and literal
diagram-preserving extension action, and retains equality of full orders.
Ambient simplicity identifies that nontrivial normal subgroup with the whole
group without any additional native simplicity premise.

Source: Aschbacher–Smith F.4.8–10, F.4.13, F.4.16–17 and F.4.24,
printed pp.278–283,287–288 of `refs/quasithin.pdf`. This direct nonbinary
Cartan proof uses no Tits–Weiss or Fong–Seitz classification premise.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
open SimpleGraph.PathTransitivePolygon.QuadrangleRecognition
namespace CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
namespace Completion
variable {E : SourceExtension F} {M : Type*} [Group M] (c : Completion E M)
theorem uniqueGeodesicsBelow_four (hc : c.left.range ⊓ c.right.range = c.middle.range) : (graph c.cosetFamily).UniqueGeodesicsBelow 4 := by
  intro x y p q hp hq hd
  by_contra hh
  obtain ⟨v,_,_,r,hr,hlen⟩ := (p.isPath_of_length_eq_dist hp).exists_isCycle_length_le_add_of_ne
    (q.isPath_of_length_eq_dist hq) hh
  have hb := c.cycle_length_ge_eight hc v r hr
  omega

theorem exists_eight_cycle_of_involutions (hc : c.left.range ⊓ c.right.range = c.middle.range) (s t : M)
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
  let e : cycleGraph 8 ↪g (graph c.cosetFamily) := GroupAction.DihedralPolygon.edgeEmbedding c.bipartiteAction
    (by decide : 1<4) (c.uniqueGeodesicsBelow_four hc) (by decide : 0<4) le_rfl
    ⟨Bool.false_ne_true,incident_base c.cosetFamily false true⟩ hs2 ht2 hsx hsl htl htx
    (by rw [hst,one_smul]) (by rw [hst,one_smul])
  exact (cycleGraph_isContained_iff (by decide : 2<8)).mp ⟨e.toCopy⟩

theorem quadrangle_metric_of_involutions (hc : c.left.range ⊓ c.right.range = c.middle.range) (s t : M)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : s^2=1) (ht2 : t^2=1) (hst : (s*t)^4=1) :
    (∀v (p : (graph c.cosetFamily).Walk v v),p.IsCycle → 8≤p.length) ∧
    (∀v w,(graph c.cosetFamily).dist v w≤4) ∧
    (∃v,∃p : (graph c.cosetFamily).Walk v v,p.IsCycle ∧ p.length=8) := by
  have hex := c.exists_eight_cycle_of_involutions hc s t hs ht hsout htout hs2 ht2 hst
  refine ⟨c.cycle_length_ge_eight hc,diameter_bound_of_five_endpoint_bound c.connected ?_,hex⟩
  intro v p hp
  exact five_endpoint_bound c.graphAction (c.all_rootPathTransitive_five hc) (·.type) (fun h => h.1)
    (fun h => (same_orbit_iff c.cosetFamily _ _).mpr h) hex p hp

omit [Finite F] [CharP F 2] in
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

/-- Matching endpoint involutions with the quadrangle relation determine the actual
completion group; the whole overlap is retained in both projections. -/
theorem nonempty_mulEquiv_of_matching_involutions {H : Type*} [Group H]
    (d : Completion E H)
    (hcO : c.left.range ⊓ c.right.range = c.middle.range)
    (hdO : d.left.range ⊓ d.right.range = d.middle.range)
    (s : E.left) (t : E.right)
    (hs : s^2=1) (ht : t^2=1)
    (hsout : c.left s∉c.middle.range) (htout : c.right t∉c.middle.range)
    (hc : (c.left s*c.right t)^4=1) (hd : (d.left s*d.right t)^4=1) :
    Nonempty (M ≃* H) := by
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
  have heO := c.pair_overlap d hcO
  have hdiam := (e.quadrangle_metric_of_involutions heO (e.left s) (e.right t)
    ⟨s,rfl⟩ ⟨t,rfl⟩ hes het (by rw [←map_pow,hs,map_one])
      (by rw [←map_pow,ht,map_one]) he6).2.1
  have hf : CoverData e.cosetFamily c.cosetFamily (c.pairFst d) :=
    RankTwoAmalgam.FaithfulCompletion.coverData_of_hom _
      (by ext x; exact c.pairFst_left d x) (by ext x; exact c.pairFst_right d x) heO hcO
  have hg : CoverData e.cosetFamily d.cosetFamily (c.pairSnd d) :=
    RankTwoAmalgam.FaithfulCompletion.coverData_of_hom _
      (by ext x; exact c.pairSnd_left d x) (by ext x; exact c.pairSnd_right d x) heO hdO
  have hif := hf.injective_of_diameter_lt_girth e.connected hdiam
    (fun v p hp => (show (4 : ℕ) < 8 by decide).trans_le (c.cycle_length_ge_eight hcO v p hp))
  have his := hg.injective_of_diameter_lt_girth e.connected hdiam
    (fun v p hp => (show (4 : ℕ) < 8 by decide).trans_le (d.cycle_length_ge_eight hdO v p hp))
  exact ⟨(MulEquiv.ofBijective (c.pairFst d) ⟨hif,hf.surjective⟩).symm.trans
    (MulEquiv.ofBijective (c.pairSnd d) ⟨his,hg.surjective⟩)⟩

omit [Finite F] in
/-- The concrete inclusion completion satisfies the same literal Weyl relation. -/
theorem model_weylProduct_four : (weylProduct E.modelCompletion)^4=1 := by
  apply Subtype.ext
  change (MulAut.conj (WeylFrame.pointReflection (F := F)) *
    MulAut.conj WeylFrame.planeReflection)^4=1
  rw [←map_mul,←map_pow,WeylFrame.rotation_four,map_one]

/-- For q > 2 the marked full-extension completion is identified with the
original extension itself: the Cartan argument has aligned the actual Weyl
reflections. This strengthening is proved through their paired completion. -/
theorem nonempty_mulEquiv_of_card_le [Finite M] {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) : Nonempty (M ≃* E.carrier) := by
  apply c.nonempty_mulEquiv_of_matching_involutions E.modelCompletion ho E.model_overlap
    E.pointWeyl E.planeWeyl E.pointWeyl_sq E.planeWeyl_sq
  · rintro ⟨b,hb⟩
    have he := congrArg Subtype.val (c.left_injective hb)
    change b.val=MulAut.conj (WeylFrame.pointReflection (F := F)) at he
    have hm : MulAut.conj (WeylFrame.pointReflection (F := F)) ∈ E.middle ⊓ inner F :=
      ⟨he ▸ b.property,⟨_,rfl⟩⟩
    obtain ⟨g,hg,hg'⟩ := E.middle_inner.le hm
    exact WeylFrame.pointReflection_not_mem
      ((SourceExtension.inner_injective (F := F) hg') ▸ hg.2)
  · rintro ⟨b,hb⟩
    have he := congrArg Subtype.val (c.right_injective
      ((DFunLike.congr_fun c.compatible b).symm.trans hb))
    change b.val=MulAut.conj (WeylFrame.planeReflection (F := F)) at he
    have hm : MulAut.conj (WeylFrame.planeReflection (F := F)) ∈ E.middle ⊓ inner F :=
      ⟨he ▸ b.property,⟨_,rfl⟩⟩
    obtain ⟨g,hg,hg'⟩ := E.middle_inner.le hm
    exact WeylFrame.planeReflection_not_mem
      ((SourceExtension.inner_injective (F := F) hg') ▸ hg.1)
  · exact c.weylProduct_four_eq_one hF hn ho hcard
  · exact model_weylProduct_four

/-- F.4.8/F.4.17/F.4.24 in the nonbinary symplectic case, with the full
extension order and a faithful normal symplectic subgroup. -/
theorem recognized_normal_extension [Finite M] {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) :
    Nat.card M=Nat.card E.carrier ∧
    ∃ N : Subgroup M, ∃ hN : N.Normal, ∃ a : Sp F ≃* N,
      centralizer (N : Set M)=⊥ ∧
      (letI := hN; ∀g : M, DiagramAutomorphisms.PreservesDiagram
        (DiagramAutomorphisms.extensionAction N a g)) := by
  obtain ⟨e⟩ := c.nonempty_mulEquiv_of_card_le hF hn ho hcard
  let N := E.innerIn.map e.symm.toMonoidHom
  have hN : N.Normal := (E.innerIn_normal).map e.symm.toMonoidHom e.symm.surjective
  let := hN
  let a : Sp F ≃* N := E.innerEquiv.trans (e.symm.subgroupMap E.innerIn)
  have heval (x : Sp F) : e (a x).val=(E.innerEquiv x).val := e.apply_symm_apply _
  have hcentral : centralizer (N : Set M)=⊥ := by
    apply bot_unique
    intro x hx
    have hc : e x ∈ centralizer (E.innerIn : Set E.carrier) := by
      intro y hy
      have hm : e.symm y ∈ N := mem_map_of_mem _ hy
      have hh := congrArg e (hx (e.symm y) hm)
      simpa only [map_mul,e.apply_symm_apply] using hh
    have hx1 : e x=1 := mem_bot.mp (E.inner_centralizer.le hc)
    exact mem_bot.mpr (e.injective (hx1.trans (map_one e).symm))
  refine ⟨Nat.card_congr e.toEquiv,N,hN,a,hcentral,?_⟩
  intro g
  have ha : DiagramAutomorphisms.extensionAction N a g =
      DiagramAutomorphisms.extensionAction E.innerIn E.innerEquiv (e g) := by
    apply MulEquiv.ext
    intro y
    apply E.innerEquiv.injective
    apply Subtype.ext
    calc
      _ = e (a (DiagramAutomorphisms.extensionAction N a g y)).val := (heval _).symm
      _ = e (g*(a y).val*g⁻¹) := congrArg e (DiagramAutomorphisms.extensionAction_apply N a g y)
      _ = e g*(E.innerEquiv y).val*(e g)⁻¹ := by rw [map_mul,map_mul,map_inv,heval]
      _ = _ := (DiagramAutomorphisms.extensionAction_apply E.innerIn E.innerEquiv (e g) y).symm
  rw [ha]
  exact E.extensionAction_preservesDiagram (e g)

/-- In a simple ambient completion the recognized normal inner group is all
of it. No simplicity certificate for the native model is needed. -/
theorem nonempty_mulEquiv_native_of_simple [Finite M] [IsSimpleGroup M] {n : ℕ}
    (hF : Nat.card F=2^n) (hn : 1<n)
    (ho : c.left.range ⊓ c.right.range=c.middle.range)
    (hcard : Nat.card M≤Nat.card E.carrier) : Nonempty (M ≃* Sp F) := by
  obtain ⟨_,N,hN,a,_,_⟩ := c.recognized_normal_extension hF hn ho hcard
  have htop : N=⊤ := hN.eq_bot_or_eq_top.resolve_left (by
    intro hbot
    have ha : (a (WeylFrame.pointReflection (F := F))).val=1 :=
      mem_bot.mp (hbot ▸ (a WeylFrame.pointReflection).property)
    have ha' : a WeylFrame.pointReflection=1 := Subtype.ext ha
    have hs : WeylFrame.pointReflection (F := F)=1 := a.injective (ha'.trans (map_one a).symm)
    exact WeylFrame.pointReflection_not_mem (hs ▸ one_mem _))
  exact ⟨((a.trans (MulEquiv.subgroupCongr htop)).trans (Subgroup.topEquiv : (⊤ : Subgroup M) ≃* M)).symm⟩
end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.SymplecticFour
