module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalJointStabilizers
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicKernelTransport
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalJointImages

/-!
# Opposite Borel mover equality above distance six

The original paired selectors generate the whole intermediate stabilizer
with the two transported opposite movers and the endpoint seed. We retain
this property through the same reverse-path and joint-image construction;
no identification of a proper Thompson mover with a whole stabilizer is used.
The strengthened private selector chain reuses the earlier joint-image,
normalization and strict-slice lemmas.

Above distance six, the reverse joint image is two. Its common commutator
line is fixed by both opposite movers and by the endpoint seed, hence by
the entire intermediate stabilizer. The full critical-kernel normalizer is
its line centralizer. Consequently the kernel/seed join is invariant under
both generators of that stabilizer. Residual control puts it in the
Baumann slice, contradicting the strict forward bound. This excludes
distinct opposite movers on the last compatible shift.

Pulling back along all four actual transporters proves mover equality at
the first two edges of every original critical path above distance six.
The literal c.L,d.S application is in OriginalSylowExceptional. Both full
moving covers and their central attachments remain, and the cubic kernel
is still E with its odd quotient E/Q. The distance-six comparison,
terminal distance exclusions, whole CoreExhaustion, all five blockU clauses
and the exceptional original-source reconstruction remain required.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(c), (5.9)--(5.10), especially printed p.923;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags Theory.SpecificGroups.SymmetricSix
open Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem borel_paired_opposite_transports_base
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4) :
    ∃ g ∈ stabilizer Rg (alpha Rg), ∃ x ∈ stabilizer Rg (alpha Rg),
      let d := act Rg g (p.walk.getVert 1)
      Q Rg d ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
      Q Rg (act Rg x d) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
      edgeOffenderJoin (alpha Rg) d ⊔ edgeOffenderJoin (alpha Rg) (act Rg x d) =
        stabilizer Rg (alpha Rg) ∧
      x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
      ∀ J₀ : Subgroup (FreeAmalgam Rg), Q Rg (alpha Rg) ≤ J₀ →
        J₀ ≤ Q Rg (p.walk.getVert 1) → J₀.relIndex (Q Rg (p.walk.getVert 1)) = 2 →
        let J₁ := J₀.map (MulAut.conj g⁻¹).toMonoidHom
        (J₁ ⊔ J₁.map (MulAut.conj x⁻¹).toMonoidHom) ⊔ Z Rg z = stabilizer Rg (alpha Rg) := by
  obtain ⟨d,_,r,_,_,hpair,_,_,hgen₁,hgen₂,_,_,hnorm,_,_,g,hg,hgd,hopposite⟩ :=
    borel_small_critical_seed_selectors_with_opposite h e hz hk u hR p hp
  let x := (embedM Rg r)⁻¹
  have hx : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  refine ⟨g,hg,x,hx,?_⟩
  dsimp only
  rw [hgd]
  exact ⟨hgen₁,hgen₂,hpair,hnorm,hopposite⟩

include h e hz hk in
private theorem borel_paired_opposite_transports
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4) :
    ∃ g ∈ stabilizer Rg a, ∃ x ∈ stabilizer Rg a,
      let d := act Rg g (p.walk.getVert 1)
      Q Rg d ⊔ Z Rg z = stabilizer Rg a ∧
      Q Rg (act Rg x d) ⊔ Z Rg z = stabilizer Rg a ∧
      edgeOffenderJoin a d ⊔ edgeOffenderJoin a (act Rg x d) = stabilizer Rg a ∧
      x ∈ normalizer (edgeOffenderJoin a (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
      ∀ J₀ : Subgroup (FreeAmalgam Rg), Q Rg a ≤ J₀ →
        J₀ ≤ Q Rg (p.walk.getVert 1) → J₀.relIndex (Q Rg (p.walk.getVert 1)) = 2 →
        let J₁ := J₀.map (MulAut.conj g⁻¹).toMonoidHom
        (J₁ ⊔ J₁.map (MulAut.conj x⁻¹).toMonoidHom) ⊔ Z Rg z = stabilizer Rg a := by
  obtain ⟨k,hkvertex⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg k⁻¹ a = alpha Rg := by
    rw [hkvertex,act_mVertex,mul_inv_cancel]
    rfl
  have hpbase : (Q Rg (act Rg k⁻¹ z)).relIndex (Z Rg (act Rg k⁻¹ a)) < 4 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hp
  have hh := borel_paired_opposite_transports_base h e hz hk u hR
    (z := act Rg k⁻¹ z)
  rw [←hbase] at hh
  obtain ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm,hopposite⟩ := hh (p.act k⁻¹) hpbase
  let g' := k⁻¹*g*k
  let x' := k⁻¹*x*k
  have transform (v : Vertex Rg) (y : FreeAmalgam Rg) :
      act Rg (k⁻¹*y*k) v = act Rg k (act Rg y (act Rg k⁻¹ v)) := by
    simp only [act_mul]
  have cancel (v : Vertex Rg) : act Rg k (act Rg k⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hg' : g' ∈ stabilizer Rg a := by
    change act Rg g' a = a
    rw [transform,show act Rg g (act Rg k⁻¹ a) = act Rg k⁻¹ a from hg,cancel]
  have hx' : x' ∈ stabilizer Rg a := by
    change act Rg x' a = a
    rw [transform,show act Rg x (act Rg k⁻¹ a) = act Rg k⁻¹ a from hx,cancel]
  let d := act Rg g ((p.act k⁻¹).walk.getVert 1)
  have hd : act Rg k d = act Rg g' (p.walk.getVert 1) := by
    simp only [d,CriticalPath.act,actWalk_getVert,g',transform]
  have hdx : act Rg k (act Rg x d) = act Rg x' (act Rg g' (p.walk.getVert 1)) := by
    rw [←hd]
    simp only [x',←act_mul]
    congr 1
    group
  have hfirst : Adjacent Rg (act Rg k⁻¹ a) ((p.act k⁻¹).walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (p.act k⁻¹).walk.adj_getVert_succ (i := 0)
        ((p.act k⁻¹).length_eq_b ▸ sourceDistance_pos h)
  have had : Adjacent Rg (act Rg k⁻¹ a) d := by
    simpa only [show act Rg g (act Rg k⁻¹ a) = act Rg k⁻¹ a from hg] using
      (adjacent_act_iff Rg g _ _).mpr hfirst
  have hadx : Adjacent Rg (act Rg k⁻¹ a) (act Rg x d) := by
    simpa only [show act Rg x (act Rg k⁻¹ a) = act Rg k⁻¹ a from hx] using
      (adjacent_act_iff Rg x _ _).mpr had
  have hcol : color Rg (act Rg k⁻¹ a) = false := (p.act k⁻¹).start_color
  have mapJ (d₀ : Vertex Rg) (had₀ : Adjacent Rg (act Rg k⁻¹ a) d₀) :
      (edgeOffenderJoin (act Rg k⁻¹ a) d₀).map (MulAut.conj k⁻¹).toMonoidHom =
        edgeOffenderJoin a (act Rg k d₀) := by
    rw [←remaining_edge_join_act h e hz hk u (Or.inr hR) hcol had₀ k,cancel]
  have hm₁ := congrArg (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom) hgen₁
  have hm₂ := congrArg (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom) hgen₂
  have hmJ := congrArg (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom) hpair
  change (Q Rg d ⊔ Z Rg (act Rg k⁻¹ z)).map _ = _ at hm₁
  change (Q Rg (act Rg x d) ⊔ Z Rg (act Rg k⁻¹ z)).map _ = _ at hm₂
  change (edgeOffenderJoin (act Rg k⁻¹ a) d ⊔
    edgeOffenderJoin (act Rg k⁻¹ a) (act Rg x d)).map _ = _ at hmJ
  rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,cancel,cancel,hd] at hm₁
  rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,cancel,cancel,hdx] at hm₂
  rw [Subgroup.map_sup,mapJ d had,mapJ _ hadx,←stabilizer_act,cancel,hd,hdx] at hmJ
  have hmN := le_normalizer_map (MulAut.conj k⁻¹).toMonoidHom
    (mem_map_of_mem (MulAut.conj k⁻¹).toMonoidHom hnorm)
  rw [mapJ _ hfirst] at hmN
  have hvert : act Rg k ((p.act k⁻¹).walk.getVert 1) = p.walk.getVert 1 := by
    simp only [CriticalPath.act,actWalk_getVert,cancel]
  rw [hvert] at hmN
  refine ⟨g',hg',x',hx',hm₁,hm₂,hmJ,?_,?_⟩
  · simpa only [x',MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv] using hmN
  · intro J₀ hQJ hJR hi
    let Jb := J₀.map (MulAut.conj k).toMonoidHom
    have hQb : Q Rg (act Rg k⁻¹ a) ≤ Jb := by
      rw [Q_act,inv_inv]
      exact map_mono hQJ
    have hJb : Jb ≤ Q Rg ((p.act k⁻¹).walk.getVert 1) := by
      simp only [CriticalPath.act,actWalk_getVert,Q_act,inv_inv]
      exact map_mono hJR
    have hib : Jb.relIndex (Q Rg ((p.act k⁻¹).walk.getVert 1)) = 2 := by
      simp only [CriticalPath.act,actWalk_getVert,Q_act,inv_inv]
      exact (relIndex_map_map_of_injective (f := (MulAut.conj k).toMonoidHom)
        J₀ (Q Rg (p.walk.getVert 1)) (MulAut.conj k).injective).trans hi
    have hh := congrArg (Subgroup.map (MulAut.conj k⁻¹).toMonoidHom)
      (hopposite Jb hQb hJb hib)
    dsimp only at hh ⊢
    rw [Subgroup.map_sup,Subgroup.map_sup,←Z_act,cancel,←stabilizer_act,cancel] at hh
    have hgJ : (Jb.map (MulAut.conj g⁻¹).toMonoidHom).map
        (MulAut.conj k⁻¹).toMonoidHom = J₀.map (MulAut.conj g'⁻¹).toMonoidHom := by
      dsimp only [Jb]
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro v
      change k⁻¹*(g⁻¹*(k*v*k⁻¹)*g⁻¹⁻¹)*k⁻¹⁻¹ = g'⁻¹*v*g'⁻¹⁻¹
      dsimp only [g']
      group
    have hxJ (B : Subgroup (FreeAmalgam Rg)) :
        (B.map (MulAut.conj x⁻¹).toMonoidHom).map (MulAut.conj k⁻¹).toMonoidHom =
        (B.map (MulAut.conj k⁻¹).toMonoidHom).map (MulAut.conj x'⁻¹).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      apply MonoidHom.ext
      intro v
      change k⁻¹*(x⁻¹*v*x⁻¹⁻¹)*k⁻¹⁻¹ = x'⁻¹*(k⁻¹*v*k⁻¹⁻¹)*x'⁻¹⁻¹
      dsimp only [x']
      group
    rwa [hxJ,hgJ] at hh

include h e hz hk in
private theorem borel_nonsplit_paired_backward_opposite
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hn : X Rg a ≠ U Rg a ⊔
      (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) :
    ∃ g ∈ stabilizer Rg a, ∃ x ∈ stabilizer Rg a,
      let d := act Rg g (p.walk.getVert 1)
      let c := act Rg g (p.walk.getVert 2)
      let v := p.walk.getVert (p.walk.length-2)
      Q Rg d ⊔ Z Rg z = stabilizer Rg a ∧
      Q Rg (act Rg x d) ⊔ Z Rg z = stabilizer Rg a ∧
      edgeOffenderJoin a d ⊔ edgeOffenderJoin a (act Rg x d) = stabilizer Rg a ∧
      x ∈ normalizer (edgeOffenderJoin a (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
      (∀ J₀ : Subgroup (FreeAmalgam Rg), Q Rg a ≤ J₀ →
        J₀ ≤ Q Rg (p.walk.getVert 1) → J₀.relIndex (Q Rg (p.walk.getVert 1)) = 2 →
        let J₁ := J₀.map (MulAut.conj g⁻¹).toMonoidHom
        (J₁ ⊔ J₁.map (MulAut.conj x⁻¹).toMonoidHom) ⊔ Z Rg z = stabilizer Rg a) ∧
      X Rg z ≤ normalizer (((Z Rg c ⊓ Q Rg v) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      X Rg z ≤ normalizer (((Z Rg (act Rg x c) ⊓ Q Rg v) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      ⁅Z Rg c,Z Rg v⁆ ≠ ⊥ ∧ ⁅Z Rg (act Rg x c),Z Rg v⁆ ≠ ⊥ ∧
      ∃ (q₁ : CriticalPath Rg (sourceGeometry h) c v)
        (q₂ : CriticalPath Rg (sourceGeometry h) (act Rg x c) v),
        q₁.walk.getVert 1 = d ∧ q₂.walk.getVert 1 = act Rg x d ∧
        (∀ i ≤ p.walk.length-2, q₁.walk.getVert (i+2) = p.walk.getVert i) ∧
        (∀ i ≤ p.walk.length-2, q₂.walk.getVert (i+2) = p.walk.getVert i) := by
  obtain ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm,hopposite⟩ :=
    borel_paired_opposite_transports h e hz hk u hR p hp
  have hgen₂' : Q Rg (act Rg (g*x) (p.walk.getVert 1)) ⊔ Z Rg z = stabilizer Rg a := by
    simpa only [act_mul] using hgen₂
  obtain ⟨hN₁,hH₁,q₁,hq₁,ho₁⟩ :=
    borel_nonsplit_generating_shift h e hz hk hb u hR p hp hn g hg hgen₁
  have hh₂ := borel_nonsplit_generating_shift h e hz hk hb u hR p hp hn (g*x)
    ((stabilizer Rg a).mul_mem hg hx) hgen₂'
  obtain ⟨hN₂,hH₂,hex₂⟩ := hh₂
  rw [act_mul] at hex₂
  obtain ⟨q₂,hq₂,ho₂⟩ := hex₂
  simp only [act_mul] at hN₂ hH₂ hq₂
  exact ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm,hopposite,hN₁,hN₂,hH₁,hH₂,q₁,q₂,hq₁,hq₂,ho₁,ho₂⟩

include h e hz hk in
private theorem borel_three_shift_reverse_choices_opposite
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path)
    (hne : edgeOffenderJoin r.start t.edge ≠ edgeOffenderJoin t.start t.edge) :
    let v := r.path.walk.getVert (r.path.walk.length-2)
    ∃ g ∈ stabilizer Rg v, ∃ x ∈ stabilizer Rg v,
      let d := act Rg g (t.path.walk.getVert (t.path.walk.length-1))
      let c := act Rg g (t.path.walk.getVert (t.path.walk.length-2))
      Q Rg d ⊔ Z Rg t.start = stabilizer Rg v ∧
      Q Rg (act Rg x d) ⊔ Z Rg t.start = stabilizer Rg v ∧
      edgeOffenderJoin v d ⊔ edgeOffenderJoin v (act Rg x d) = stabilizer Rg v ∧
      x ∈ normalizer (edgeOffenderJoin v
        (t.path.walk.getVert (t.path.walk.length-1)) : Set (FreeAmalgam Rg)) ∧
      (∀ J₀ : Subgroup (FreeAmalgam Rg), Q Rg v ≤ J₀ →
        J₀ ≤ Q Rg (t.path.walk.getVert (t.path.walk.length-1)) → J₀.relIndex (Q Rg (t.path.walk.getVert (t.path.walk.length-1))) = 2 →
        let J₁ := J₀.map (MulAut.conj g⁻¹).toMonoidHom
        (J₁ ⊔ J₁.map (MulAut.conj x⁻¹).toMonoidHom) ⊔ Z Rg t.start = stabilizer Rg v) ∧
      X Rg t.start ≤ normalizer (((Z Rg c ⊓ Q Rg r.start) ⊔ Z Rg v :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      X Rg t.start ≤ normalizer (((Z Rg (act Rg x c) ⊓ Q Rg r.start) ⊔ Z Rg v :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      ⁅Z Rg c,Z Rg r.start⁆ ≠ ⊥ ∧ ⁅Z Rg (act Rg x c),Z Rg r.start⁆ ≠ ⊥ ∧
      ∃ (s₁ : CriticalPath Rg (sourceGeometry h) c r.start)
        (s₂ : CriticalPath Rg (sourceGeometry h) (act Rg x c) r.start),
        s₁.walk.getVert 1 = d ∧ s₂.walk.getVert 1 = act Rg x d ∧
        (∀ i ≤ t.path.walk.length-2,
          s₁.walk.getVert (i+2) = t.path.walk.getVert (t.path.walk.length-i)) ∧
        (∀ i ≤ t.path.walk.length-2,
          s₂.walk.getVert (i+2) = t.path.walk.getVert (t.path.walk.length-i)) := by
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let rev : CriticalPath Rg (sourceGeometry h) v t.start :=
    { start_color := t.path.end_color
      walk := t.path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,t.path.shortest,SimpleGraph.dist_comm]
      critical := reverse_pair h e t.path }
  have hcore := (borel_three_shift_endpoint_normalization h e hz hk hb u hR p q r t).2
  have hn₀ := borel_opposite_containing_core_nonsplit h e hz hk u hR
    r.path.start_color t.path.start_color t.adjacent_start t.adjacent_shift hne hcore
  have hn : X Rg v ≠ U Rg v ⊔
      (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg))) := by
    intro hs
    exact hn₀ (omega_generation_transport t.path.end_color r.path.start_color hs)
  have ht := two_borel_backward_shifts_small_moving h e hz hk hb q.path r t
  have hs : (Q Rg t.start).relIndex (Z Rg v) < 4 := by rw [ht.2.2.1]; decide
  have hv (i : ℕ) : rev.walk.getVert i = t.path.walk.getVert (t.path.walk.length-i) := by
    exact SimpleGraph.Walk.getVert_reverse _ _
  have hlen : rev.walk.length = t.path.walk.length := SimpleGraph.Walk.length_reverse _
  have htlen : t.path.walk.length = sourceDistance h := t.path.length_eq_b
  have hrlast : rev.walk.getVert (rev.walk.length-2) = r.start := by
    rw [hv,hlen,show t.path.walk.length-(t.path.walk.length-2)=2 by omega]
    simpa only [SimpleGraph.Walk.getVert_zero] using t.overlap 0 (by omega)
  obtain ⟨g,hg,x,hx,hg₁,hg₂,hpair,hnorm,hopposite,hN₁,hN₂,hH₁,hH₂,s₁,s₂,hs₁,hs₂,ho₁,ho₂⟩ :=
    borel_nonsplit_paired_backward_opposite h e hz hk hb u hR rev hs hn
  simp only [hrlast,hv] at hN₁ hN₂ hH₁ hH₂ hg₁ hg₂ hpair hnorm hopposite
  have hex : ∃ (s₁ : CriticalPath Rg (sourceGeometry h) (act Rg g (rev.walk.getVert 2))
      (rev.walk.getVert (rev.walk.length-2)))
      (s₂ : CriticalPath Rg (sourceGeometry h) (act Rg x (act Rg g (rev.walk.getVert 2)))
      (rev.walk.getVert (rev.walk.length-2))),
      s₁.walk.getVert 1 = act Rg g (rev.walk.getVert 1) ∧
      s₂.walk.getVert 1 = act Rg x (act Rg g (rev.walk.getVert 1)) ∧
      (∀ i ≤ t.path.walk.length-2,
        s₁.walk.getVert (i+2) = t.path.walk.getVert (t.path.walk.length-i)) ∧
      (∀ i ≤ t.path.walk.length-2,
        s₂.walk.getVert (i+2) = t.path.walk.getVert (t.path.walk.length-i)) := by
    exact ⟨s₁,s₂,hs₁,hs₂,fun i hi => (ho₁ i (hlen.symm ▸ hi)).trans (hv i),
      fun i hi => (ho₂ i (hlen.symm ▸ hi)).trans (hv i)⟩
  rw [hrlast,hv,hv] at hex
  exact ⟨g,hg,x,hx,hg₁,hg₂,hpair,hnorm,hopposite,hN₁,hN₂,hH₁,hH₂,hex⟩

include h e hz hk in
private theorem borel_four_shift_reverse_joint_image_opposite
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) (s : BorelBackwardShift (h := h) t.path)
    (hse : act Rg s.transporter (t.path.walk.getVert 1) = s.edge)
    (hne : edgeOffenderJoin t.start s.edge ≠ edgeOffenderJoin s.start s.edge) :
    let v := t.path.walk.getVert (t.path.walk.length-2)
    ∃ g ∈ stabilizer Rg v, ∃ x ∈ stabilizer Rg v,
      let d := act Rg g (s.path.walk.getVert (s.path.walk.length-1))
      let c := act Rg g (s.path.walk.getVert (s.path.walk.length-2))
      let A := Z Rg c ⊔ Z Rg (act Rg x c)
      Q Rg d ⊔ Z Rg s.start = stabilizer Rg v ∧
      Q Rg (act Rg x d) ⊔ Z Rg s.start = stabilizer Rg v ∧
      edgeOffenderJoin v d ⊔ edgeOffenderJoin v (act Rg x d) = stabilizer Rg v ∧
      x ∈ normalizer (edgeOffenderJoin v
        (s.path.walk.getVert (s.path.walk.length-1)) : Set (FreeAmalgam Rg)) ∧
      (∀ J₀ : Subgroup (FreeAmalgam Rg), Q Rg v ≤ J₀ →
        J₀ ≤ Q Rg (s.path.walk.getVert (s.path.walk.length-1)) → J₀.relIndex (Q Rg (s.path.walk.getVert (s.path.walk.length-1))) = 2 →
        let J₁ := J₀.map (MulAut.conj g⁻¹).toMonoidHom
        (J₁ ⊔ J₁.map (MulAut.conj x⁻¹).toMonoidHom) ⊔ Z Rg s.start = stabilizer Rg v) ∧
      X Rg s.start ≤ normalizer (((Z Rg c ⊓ Q Rg t.start) ⊔ Z Rg v :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      X Rg s.start ≤ normalizer (((Z Rg (act Rg x c) ⊓ Q Rg t.start) ⊔ Z Rg v :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      A ≤ Q Rg r.start ∧
      ((Q Rg t.start).relIndex A = 2 ∨ (Q Rg t.start).relIndex A = 4) ∧
      ((Q Rg t.start).relIndex A = 2 →
        ⁅Z Rg c,Z Rg t.start⁆ = ⁅Z Rg (act Rg x c),Z Rg t.start⁆ ∧
        Nat.card (⁅Z Rg c,Z Rg t.start⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
        Z Rg t.start ⊓ Q Rg c = Z Rg t.start ⊓ Q Rg (act Rg x c)) ∧
      ((Q Rg t.start).relIndex A = 4 →
        Q Rg t.start ⊔ A = Q Rg t.start ⊔ Q Rg r.start ∧
        ⁅Z Rg c,Z Rg t.start⁆ ⊔ ⁅Z Rg (act Rg x c),Z Rg t.start⁆ =
          ⁅Z Rg t.start,Q Rg r.start⁆) ∧
      ∃ (s₁ : CriticalPath Rg (sourceGeometry h) c t.start)
        (s₂ : CriticalPath Rg (sourceGeometry h) (act Rg x c) t.start),
        s₁.walk.getVert 1 = d ∧ s₂.walk.getVert 1 = act Rg x d ∧
        (∀ i ≤ s.path.walk.length-2,
          s₁.walk.getVert (i+2) = s.path.walk.getVert (s.path.walk.length-i)) ∧
        (∀ i ≤ s.path.walk.length-2,
          s₂.walk.getVert (i+2) = s.path.walk.getVert (s.path.walk.length-i)) := by
  obtain ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm,hopposite,hN₁,hN₂,_,_,s₁,s₂,hs₁,hs₂,ho₁,ho₂⟩ :=
    borel_three_shift_reverse_choices_opposite h e hz hk hb u hR q.path r t s hne
  let c := act Rg g (s.path.walk.getVert (s.path.walk.length-2))
  let A := Z Rg c ⊔ Z Rg (act Rg x c)
  have htlen : t.path.walk.length = sourceDistance h := t.path.length_eq_b
  have hslen : s.path.walk.length = sourceDistance h := s.path.length_eq_b
  have ht2 : t.path.walk.getVert 2 = r.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using t.overlap 0 (Nat.zero_le _)
  have hs4 : s.path.walk.getVert 4 = r.start := by
    simpa only [show 2+2=4 from rfl,ht2] using s.overlap 2 (by omega)
  have seed_core {y : Vertex Rg} (w : CriticalPath Rg (sourceGeometry h) y t.start)
      (ho : ∀ i ≤ s.path.walk.length-2,
        w.walk.getVert (i+2) = s.path.walk.getVert (s.path.walk.length-i)) :
      Z Rg y ≤ Q Rg r.start := by
    have hwlen : w.walk.length = sourceDistance h := w.length_eq_b
    have hv : w.walk.getVert (w.walk.length-2) = r.start := by
      have hh := ho (s.path.walk.length-4) (by omega)
      rw [show s.path.walk.length-4+2=w.walk.length-2 by omega,
        show s.path.walk.length-(s.path.walk.length-4)=4 by omega,hs4] at hh
      exact hh
    apply Z_le_Q_of_dist_lt Rg y ((sourceGeometry h).exists_critical y w.start_color)
    have hd : (cosetGraph Rg).dist y r.start = w.walk.length-2 :=
      (congrArg (fun z => (cosetGraph Rg).dist y z) hv).symm.trans
        (w.dist_start (by omega : w.walk.length-2 ≤ w.walk.length))
    rw [hd,(sourceGeometry h).distance_constant _ w.start_color]
    change w.walk.length-2 < sourceDistance h
    omega
  have hAC : A ≤ Q Rg r.start := sup_le (seed_core s₁ ho₁) (seed_core s₂ ho₂)
  have hsr : act Rg s.transporter r.start = s.start := by simpa only [ht2] using s.start_eq
  have hst : act Rg s.transporter t.edge = s.edge := by simpa only [t.first] using hse
  have hjt := remaining_edge_join_act h e hz hk u (Or.inr hR)
    t.path.start_color t.adjacent_shift s.transporter
  have hjr := remaining_edge_join_act h e hz hk u (Or.inr hR)
    r.path.start_color t.adjacent_start s.transporter
  rw [show act Rg s.transporter t.start = t.start from s.transporter_mem,hst] at hjt
  rw [hsr,hst] at hjr
  have hne' : edgeOffenderJoin t.start t.edge ≠ edgeOffenderJoin r.start t.edge := by
    intro he
    exact hne (hjt.trans ((congrArg (Subgroup.map (MulAut.conj s.transporter⁻¹).toMonoidHom) he).trans hjr.symm))
  have hcores := borel_four_shift_mutual_cores h e hz hk hb u hR p q r t s hse
  have him := borel_mutual_core_joint_image h e hz hk u hR t.path.start_color r.path.start_color
    t.adjacent_shift t.adjacent_start hne' hcores.1 hcores.2 A hAC
  have hi : (Q Rg t.start).relIndex A = 2 ∨ (Q Rg t.start).relIndex A = 4 := by
    have hbound := Nat.le_of_dvd (by decide : 0 < 4) him.1
    have hn : (Q Rg t.start).relIndex A ≠ 1 :=
      fun he => s₁.critical.2 (le_sup_left.trans (relIndex_eq_one.mp he))
    have hd := him.1
    interval_cases he : (Q Rg t.start).relIndex A <;> norm_num at hd <;> omega
  refine ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm,hopposite,hN₁,hN₂,hAC,hi,
    fun he => borel_joint_image_two_equal_lines h e hz hk s₁ s₂ he,?_,
    s₁,s₂,hs₁,hs₂,ho₁,ho₂⟩
  intro he
  have hh := him.2 he
  have hcomm := borel_core_joint_commutator h e hz hk u hR t.path.start_color t.adjacent_shift
    (Q Rg r.start) (Z Rg c) (Z Rg (act Rg x c)) hcores.1
    (seed_core s₁ ho₁) (seed_core s₂ ho₂)
  refine ⟨hh.1,?_⟩
  rw [commutator_comm (Z Rg c),commutator_comm (Z Rg (act Rg x c)),←hcomm]
  exact hh.2

include h e hz hk in
private theorem borel_four_shift_reverse_joint_image_two_gt_six_opposite
    (hb : 6 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) (s : BorelBackwardShift (h := h) t.path)
    (hse : act Rg s.transporter (t.path.walk.getVert 1) = s.edge)
    (hne : edgeOffenderJoin t.start s.edge ≠ edgeOffenderJoin s.start s.edge) :
    let v := t.path.walk.getVert (t.path.walk.length-2)
    ∃ g ∈ stabilizer Rg v, ∃ x ∈ stabilizer Rg v,
      let d := act Rg g (s.path.walk.getVert (s.path.walk.length-1))
      let c := act Rg g (s.path.walk.getVert (s.path.walk.length-2))
      let A := Z Rg c ⊔ Z Rg (act Rg x c)
      Q Rg d ⊔ Z Rg s.start = stabilizer Rg v ∧
      Q Rg (act Rg x d) ⊔ Z Rg s.start = stabilizer Rg v ∧
      edgeOffenderJoin v d ⊔ edgeOffenderJoin v (act Rg x d) = stabilizer Rg v ∧
      x ∈ normalizer (edgeOffenderJoin v
        (s.path.walk.getVert (s.path.walk.length-1)) : Set (FreeAmalgam Rg)) ∧
      (∀ J₀ : Subgroup (FreeAmalgam Rg), Q Rg v ≤ J₀ →
        J₀ ≤ Q Rg (s.path.walk.getVert (s.path.walk.length-1)) → J₀.relIndex (Q Rg (s.path.walk.getVert (s.path.walk.length-1))) = 2 →
        let J₁ := J₀.map (MulAut.conj g⁻¹).toMonoidHom
        (J₁ ⊔ J₁.map (MulAut.conj x⁻¹).toMonoidHom) ⊔ Z Rg s.start = stabilizer Rg v) ∧
      X Rg s.start ≤ normalizer (((Z Rg c ⊓ Q Rg t.start) ⊔ Z Rg v :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      X Rg s.start ≤ normalizer (((Z Rg (act Rg x c) ⊓ Q Rg t.start) ⊔ Z Rg v :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) ∧
      A ≤ Q Rg r.start ∧
      (Q Rg t.start).relIndex A = 2 ∧
      ⁅Z Rg c,Z Rg t.start⁆ = ⁅Z Rg (act Rg x c),Z Rg t.start⁆ ∧
      Nat.card (⁅Z Rg c,Z Rg t.start⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      Z Rg t.start ⊓ Q Rg c = Z Rg t.start ⊓ Q Rg (act Rg x c) ∧
      ∃ (s₁ : CriticalPath Rg (sourceGeometry h) c t.start)
        (s₂ : CriticalPath Rg (sourceGeometry h) (act Rg x c) t.start),
        s₁.walk.getVert 1 = d ∧ s₂.walk.getVert 1 = act Rg x d ∧
        (∀ i ≤ s.path.walk.length-2,
          s₁.walk.getVert (i+2) = s.path.walk.getVert (s.path.walk.length-i)) ∧
        (∀ i ≤ s.path.walk.length-2,
          s₂.walk.getVert (i+2) = s.path.walk.getVert (s.path.walk.length-i)) := by
  obtain ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm,hopposite,hN₁,hN₂,hAC,hi,htwo,hfour,
    s₁,s₂,hs₁,hs₂,ho₁,ho₂⟩ :=
    borel_four_shift_reverse_joint_image_opposite h e hz hk (by omega) u hR p q r t s hse hne
  have hsmall : (Q Rg t.start).relIndex
      (Z Rg (act Rg g (s.path.walk.getVert (s.path.walk.length-2))) ⊔
        Z Rg (act Rg x (act Rg g (s.path.walk.getVert (s.path.walk.length-2))))) = 2 := by
    rcases hi with hi | hi
    · exact hi
    · exact (borel_four_shift_reverse_core_span_false_gt_six h e hz hk hb u hR p q r t s
        s₁ s₂ ho₁ ho₂ (hfour hi).2).elim
  have hlines := htwo hsmall
  exact ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm,hopposite,hN₁,hN₂,hAC,hsmall,
    hlines.1,hlines.2.1,hlines.2.2,s₁,s₂,hs₁,hs₂,ho₁,ho₂⟩

include h e hz hk in
/-- A full critical line at a strict neighboring slice cannot be fixed by the
whole intermediate stabilizer when the endpoint normalizes its kernel join. -/
theorem borel_strict_neighbor_line_not_central
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c d w z : Vertex Rg} (ha : color Rg a = false)
    (p : CriticalPath Rg (sourceGeometry h) c w)
    (hp : (Q Rg w).relIndex (Z Rg c) < 4)
    (had : Adjacent Rg a d) (hcd : Adjacent Rg c d)
    (hgen : Q Rg d ⊔ Z Rg z = stabilizer Rg a)
    (hstrict : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c))
    (hn : Z Rg z ≤ normalizer (((Z Rg c ⊓ Q Rg w) ⊔ Z Rg a :
      Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))) :
    ¬ ⁅Z Rg c,Z Rg w⁆ ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
  intro hcentral
  let K := Z Rg c ⊓ Q Rg w
  let N := K ⊔ Z Rg a
  have hb2 := distance_gt_two h e hz hk
  have hd : color Rg d = true := by
    have hh := adjacent_color_ne Rg had
    rw [ha] at hh
    cases he : color Rg d <;> simp_all
  have hcv := terminal_neighbor_seed_radius had hcd
  have hNV : N ≤ V Rg a := sup_le (inf_le_left.trans hcv) (Z_le_VBall Rg a 2)
  have hZaT : Z Rg a ≤ Q Rg d :=
    (((sourceGeometry h).omega_bound a ha (by
      rw [(sourceGeometry h).distance_constant a ha]; exact sourceDistance_pos h)).trans
      (omegaCenter_le _)).trans (Q_le_adjacent_h Rg hd had)
  have hTNc : Q Rg d ≤ normalizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    (show Q Rg d ≤ stabilizer Rg c from
      fun _ hx => hx.2 _ (adjacent_symm Rg hcd)).trans (Z_normalized Rg c)
  let := finite_Z Rg c
  let := finite_Z Rg a
  have hnot : ¬ K ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
    intro hKB
    have hki : K.relIndex (Z Rg c) = 2 := by
      rw [show K = Z Rg c ⊓ Q Rg w from rfl,inf_relIndex_left]
      exact (small_critical_indices h e hz hk p hp).1
    have hi := relIndex_le_of_le_left hKB
      (index_ne_zero_of_finite : K.relIndex (Z Rg c) ≠ 0)
    have hj := relIndex_le_of_le_right (H := B Rg a ((sourceGeometry h).Z_normal _))
      (DistanceEight.U_le_Z Rg c) index_ne_zero_of_finite
    rw [hki] at hi
    exact (Nat.not_le_of_gt hstrict) (hj.trans hi)
  have hsmall : (Z Rg a).relIndex N ∣ 8 := by
    have hbig : (Z Rg a).relIndex (Z Rg c ⊔ Z Rg a) ∣ 8 := by
      rw [relIndex_sup_of_normalizes (Z Rg c) (Z Rg a) (hZaT.trans hTNc)]
      have hh := relIndex_dvd_of_le_left (Z Rg c) (adjacent_Z_le Rg ha had)
      rw [borel_full_seed_edge_index h e hz hk u hR p.start_color hcd] at hh
      exact hh
    have hm := relIndex_mul_relIndex (Z Rg a) N (Z Rg c ⊔ Z Rg a)
      le_sup_right (sup_le_sup_right inf_le_left _)
    exact (Dvd.intro _ hm).trans hbig
  have hTGc : Q Rg d ≤ stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hcd)
  have hTGa : Q Rg d ≤ stabilizer Rg a := fun _ hx => hx.2 _ (adjacent_symm Rg had)
  have hTK : Q Rg d ≤ normalizer (K : Set (FreeAmalgam Rg)) := by
    have hh := le_inf hTGc (hTGa.trans (le_centralizer_iff.mp hcentral))
    rw [←small_critical_kernel_normalizer_eq_line_centralizer h e hz hk p hp] at hh
    exact hh.trans inf_le_right
  have hGN : stabilizer Rg a ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le ((le_inf hTK (hTGa.trans (Z_normalized Rg a))).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)) hn
  exact hnot (le_sup_left.trans (terminal_residual_small_radius_le_slice h e hz hk ha N
    hNV ((Ltilde_le_stabilizer a).trans hGN) hsmall))

include h e hz hk in
/-- Above distance six, the last compatible Borel shift has equal opposite
proper Thompson movers. The full-stabilizer centrality argument uses both
selected opposite movers with their original transporters. -/
theorem borel_four_shift_mover_eq_gt_six
    (hb : 6 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) (s : BorelBackwardShift (h := h) t.path)
    (hse : act Rg s.transporter (t.path.walk.getVert 1) = s.edge) :
    edgeOffenderJoin t.start s.edge = edgeOffenderJoin s.start s.edge := by
  by_contra hne
  obtain ⟨g,hg,x,hx,hgen₁,hgen₂,hpair,hnorm,hopposite,hN₁,hN₂,hAC,hi,hline,hcard,hkernel,
    s₁,s₂,hs₁,hs₂,ho₁,ho₂⟩ :=
    borel_four_shift_reverse_joint_image_two_gt_six_opposite h e hz hk hb u hR p q r t s hse hne
  let v := t.path.walk.getVert (t.path.walk.length-2)
  let c₀ := s.path.walk.getVert (s.path.walk.length-2)
  let d₀ := s.path.walk.getVert (s.path.walk.length-1)
  let c := act Rg g c₀
  let d := act Rg g d₀
  let H := ⁅Z Rg c,Z Rg t.start⁆
  have hb4 : 4 < sourceDistance h := by omega
  have hb2 : 2 < sourceDistance h := by omega
  have hl : s.path.walk.length = sourceDistance h := s.path.length_eq_b
  have hsl : s₁.walk.length = sourceDistance h := s₁.length_eq_b
  have hc₀ : color Rg c₀ = false := by
    simpa only [action_preserves_color] using s₁.start_color
  have hc₀d₀ : Adjacent Rg c₀ d₀ := by
    have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-2) (by omega)
    rw [show s.path.walk.length-2+1=s.path.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hcd : Adjacent Rg c d := (adjacent_act_iff Rg g _ _).mpr hc₀d₀
  have hw2 : s₁.walk.getVert 2 = v := by
    simpa only [Nat.zero_add,Nat.sub_zero,SimpleGraph.Walk.getVert_length] using
      ho₁ 0 (Nat.zero_le _)
  have had : Adjacent Rg v d := by
    have hh := adjacent_symm Rg
      ((cosetGraph_adj Rg _ _).mp (s₁.walk.adj_getVert_succ (i := 1) (by omega)))
    simpa only [hs₁,hw2] using hh
  have small₁ : (Q Rg t.start).relIndex (Z Rg c) < 4 := by
    have hh := relIndex_le_of_le_right (H := Q Rg t.start)
      (show Z Rg c ≤ Z Rg c ⊔ Z Rg (act Rg x c) from le_sup_left)
      (by rw [hi]; decide)
    rw [hi] at hh
    omega
  have small₂ : (Q Rg t.start).relIndex (Z Rg (act Rg x c)) < 4 := by
    have hh := relIndex_le_of_le_right (H := Q Rg t.start)
      (show Z Rg (act Rg x c) ≤ Z Rg c ⊔ Z Rg (act Rg x c) from le_sup_right)
      (by rw [hi]; decide)
    rw [hi] at hh
    omega
  let rev : CriticalPath Rg (sourceGeometry h) v s.start :=
    { start_color := s.path.end_color
      walk := s.path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,s.path.shortest,SimpleGraph.dist_comm]
      critical := reverse_pair h e s.path }
  have hB : (B Rg v ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg v ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb2 v rev.start_color ((stabilizer Rg v).inv_mem hg))
  have hstrict : 2 < (B Rg v ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) := by
    rw [show c = act Rg g c₀ from rfl,U_act,←hB,
      relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    simpa only [rev,SimpleGraph.Walk.getVert_reverse] using
      borel_forward_slice_strict_at h e hz hk hb4 u hR rev
  have hZX : Z Rg s.start ≤ X Rg s.start :=
    (sourceGeometry h).omega_bound s.start s.path.start_color (by
      rw [(sourceGeometry h).distance_constant _ s.path.start_color]
      exact sourceDistance_pos h)
  have hcore₁ := (borel_normalized_neighbor_kernel_core h e hz hk u hR rev.start_color
    s₁ small₁ hs₁ had hcd hgen₁ hstrict (hZX.trans hN₁)).1
  have hJg := remaining_edge_join_act h e hz hk u (Or.inr hR) hc₀ hc₀d₀ g
  have hJx := remaining_edge_join_act h e hz hk u (Or.inr hR) s₁.start_color hcd x
  have hQv : (Q Rg v).map (MulAut.conj g⁻¹).toMonoidHom = Q Rg v := by
    rw [←Q_act,show act Rg g v = v from hg]
  have hcore₀ : Q Rg v ≤ edgeOffenderJoin c₀ d₀ := by
    rw [hJg,←hQv] at hcore₁
    exact (map_le_map_iff_of_injective (MulAut.conj _).injective).mp hcore₁
  obtain ⟨J₀,_,hJ₀,_,hJT,hJi,_⟩ := borel_edge_maximal_offenders h e hz hk u hR hc₀ hc₀d₀
  have hgen := hopposite (edgeOffenderJoin c₀ d₀) hcore₀ (by rwa [hJ₀]) (by rwa [hJ₀])
  dsimp only at hgen
  rw [←hJg,←hJx] at hgen
  have hJ₁ := (borel_small_mover_normalizes_critical_kernel h e hz hk u hR s₁ small₁).1
  have hJ₂ := (borel_small_mover_normalizes_critical_kernel h e hz hk u hR s₂ small₂).1
  rw [hs₁] at hJ₁
  rw [hs₂,←hline] at hJ₂
  have hHt : H ≤ Z Rg t.start := by
    dsimp only [H]
    rw [commutator_comm]
    exact critical_seed_commutator_le h (CriticalPath.ofPair s₁.end_color (reverse_pair h e s₁))
  have hts : (cosetGraph Rg).dist t.start s.start = 2 := by
    have hs2 : s.path.walk.getVert 2 = t.start := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using s.overlap 0 (Nat.zero_le _)
    rw [SimpleGraph.dist_comm]
    exact (congrArg (fun y => (cosetGraph Rg).dist s.start y) hs2).symm.trans
      (s.path.dist_start (by omega : 2 ≤ s.path.walk.length))
  have htsQ : Z Rg t.start ≤ Q Rg s.start := by
    apply Z_le_Q_of_dist_lt Rg t.start ((sourceGeometry h).exists_critical _ t.path.start_color)
    rw [hts,(sourceGeometry h).distance_constant _ t.path.start_color]
    exact hb2
  have hHs : H ≤ centralizer (Z Rg s.start : Set (FreeAmalgam Rg)) :=
    (hHt.trans htsQ).trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg s.start s.path.start_color)))
  have hcentral : H ≤ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact sup_le (sup_le hJ₁ hJ₂) (le_centralizer_iff.mp hHs)
  exact borel_strict_neighbor_line_not_central h e hz hk u hR rev.start_color s₁ small₁
    had hcd hgen₁ hstrict (hZX.trans hN₁) hcentral
include h e hz hk in
/-- Pull equality of opposite movers through the literal backward-shift
transporter to the first two vertices of the original critical path. -/
theorem borel_shift_mover_eq_pullback
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (q : BorelBackwardShift (h := h) p)
    (hqe : act Rg q.transporter (p.walk.getVert 1) = q.edge)
    (heq : edgeOffenderJoin a q.edge = edgeOffenderJoin q.start q.edge) :
    edgeOffenderJoin a (p.walk.getVert 1) =
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have ha1 : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have h21 : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) := by
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hcol : color Rg (p.walk.getVert 2) = false := by
    have hh := q.path.start_color
    rw [←q.start_eq,action_preserves_color] at hh
    exact hh
  have hm₁ := remaining_edge_join_act h e hz hk u (Or.inr hR) p.start_color ha1 q.transporter
  have hm₂ := remaining_edge_join_act h e hz hk u (Or.inr hR) hcol h21 q.transporter
  rw [show act Rg q.transporter a = a from q.transporter_mem,hqe] at hm₁
  rw [q.start_eq,hqe] at hm₂
  exact (map_injective (MulAut.conj q.transporter⁻¹).injective)
    (hm₁.symm.trans (heq.trans hm₂))

include h e hz hk in
/-- The opposite proper Borel movers agree along the first two edges of
every original critical path of distance greater than six. The four shifts
needed for the terminal argument are constructed and discharged here. -/
theorem borel_critical_mover_eq_gt_six
    (hb : 6 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    edgeOffenderJoin a (p.walk.getVert 1) =
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) := by
  have hb4 : 4 < sourceDistance h := by omega
  obtain ⟨q,hqe⟩ := borel_backwardShift h e hz hk hb4 u hR p
  obtain ⟨r,hre⟩ := borel_backwardShift h e hz hk hb4 u hR q.path
  obtain ⟨t,hte⟩ := borel_backwardShift h e hz hk hb4 u hR r.path
  obtain ⟨s,hse⟩ := borel_backwardShift h e hz hk hb4 u hR t.path
  have hs := borel_four_shift_mover_eq_gt_six h e hz hk hb u hR p q r t s hse
  have ht := borel_shift_mover_eq_pullback h e hz hk u hR t.path s hse hs
  have ht2 : t.path.walk.getVert 2 = r.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using t.overlap 0 (Nat.zero_le _)
  rw [t.first,ht2] at ht
  have hr := borel_shift_mover_eq_pullback h e hz hk u hR r.path t hte ht.symm
  have hr2 : r.path.walk.getVert 2 = q.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using r.overlap 0 (Nat.zero_le _)
  rw [r.first,hr2] at hr
  have hq := borel_shift_mover_eq_pullback h e hz hk u hR q.path r hre hr.symm
  have hq2 : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  rw [q.first,hq2] at hq
  exact borel_shift_mover_eq_pullback h e hz hk u hR p q hqe hq.symm

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
