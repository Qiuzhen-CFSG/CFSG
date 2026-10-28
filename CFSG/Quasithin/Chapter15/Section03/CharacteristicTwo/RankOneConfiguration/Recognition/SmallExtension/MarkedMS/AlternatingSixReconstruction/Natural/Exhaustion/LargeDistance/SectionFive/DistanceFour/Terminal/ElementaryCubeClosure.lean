module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ElementaryCentralForward

/-!
# Unconditional cube distance-four exclusion

The strict midpoint slice first excludes the small opposite branch. A paired
backward path is then transported to the forward midpoint; the two edge-seed
intersections give a central triple for the second strict neighbor. Reversing
that path invokes the central-forward-triple contradiction. The initial cube
selection therefore rules out replacement distance four whenever the radical
image is the three-disjoint-transposition image of `A6`.

Source: Meierfrankenfeld--Stellmacher (1993), (5.12)(1),(3), pp.924--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation BinaryPermutation
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
private theorem cube_strict_neighbor_backward_base
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ b, Adjacent d.radical b t ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical b) ∧
        Q d.radical (p.walk.getVert 1) ⊔ Q d.radical t = stabilizer d.radical (alpha d.radical) ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) b (p.walk.getVert 2),
          q.walk.getVert 2 = alpha d.radical := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨t,hat,g,hg,hgt,hct,hi,x,hx,hanchor,hxAnchor,hpair,hx3,q,hq,_,hgen,halt⟩ :=
    ElementarySmallCompatible.cube_compatible_strict_backward_pair_knownSimple
      (e := e) (hz := hz) (hn := hn) hb u him p hdelta hstrict
  rcases halt with ⟨v,hvt,hover⟩ | ⟨v,hvt,hover⟩
  · refine ⟨t,hat,act d.radical g delta,hct,hi,hanchor,?_⟩
    have hh : ∃ w : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical g delta) (p.walk.getVert (p.walk.length-2)),
        w.walk.getVert 2 = alpha d.radical := by
      refine ⟨v,?_⟩
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
    rw [show p.walk.length - 2 = 2 by omega] at hh
    exact hh
  · have hxG : x ∈ stabilizer d.radical (alpha d.radical) := Ltilde_le_stabilizer _ hx
    have hfix : act d.radical x⁻¹ (alpha d.radical) = alpha d.radical := inv_mem hxG
    have hlen : q.walk.length = 4 := q.length_eq_b.trans hb
    have hcancel (v : Vertex d.radical) : act d.radical x⁻¹ (act d.radical x v) = v := by
      rw [←act_mul,mul_inv_cancel,act_one]
    refine ⟨act d.radical x⁻¹ t,?_,act d.radical x⁻¹ (act d.radical g delta),?_,?_,?_,?_⟩
    · simpa only [hfix] using (adjacent_act_iff d.radical x⁻¹ _ _).mpr hat
    · exact (adjacent_act_iff d.radical x⁻¹ _ _).mpr hct
    · have hB : (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).map
          (MulAut.conj x).toMonoidHom = B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _) :=
        mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
          hb2 (alpha d.radical) rfl hxG)
      rw [U_act,inv_inv,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x).injective]
      exact hi
    · have hQfirst : (Q d.radical (p.walk.getVert 1)).map (MulAut.conj x).toMonoidHom =
          Q d.radical (p.walk.getVert 1) := mem_normalizer_iff_map_conj_eq.mp hxAnchor
      have hGa : (stabilizer d.radical (alpha d.radical)).map (MulAut.conj x).toMonoidHom =
          stabilizer d.radical (alpha d.radical) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical (alpha d.radical)).le_normalizer hxG)
      have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hanchor
      simpa only [Subgroup.map_sup,hQfirst,hGa,Q_act,inv_inv] using hh
    · have hlen' : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
      have hend : act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2)) =
          p.walk.getVert (p.walk.length-2) := by
        rw [hlen',hq,←act_mul,mul_inv_cancel,act_one]
      have hex : ∃ w : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical x⁻¹ (act d.radical g delta))
          (act d.radical x⁻¹ (q.walk.getVert (q.walk.length-2))),
          w.walk.getVert 2 = alpha d.radical := by
        refine ⟨v.act x⁻¹,?_⟩
        have hh := hover 0 (by omega)
        simpa only [CriticalPath.act,actWalk_getVert,Nat.zero_add,
          SimpleGraph.Walk.getVert_zero,hfix] using congrArg (act d.radical x⁻¹) hh
      rw [hend,show p.walk.length - 2 = 2 by omega] at hex
      simpa only [hcancel] using hex

include e hz hn in
private theorem cube_strict_neighbor_backward_at
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {a z delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical a t ∧
      ∃ b, Adjacent d.radical b t ∧
        2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical b) ∧
        Q d.radical (p.walk.getVert 1) ⊔ Q d.radical t = stabilizer d.radical a ∧
        ∃ q : CriticalPath d.radical (replacementGeometry h d) b (p.walk.getVert 2),
          q.walk.getVert 2 = a := by
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨j,hja⟩ : ∃ j : FreeAmalgam d.radical, act d.radical j a = alpha d.radical := by
    obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical p.start_color
    refine ⟨j⁻¹,?_⟩
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base := cube_strict_neighbor_backward_base (e := e) (hz := hz) (hn := hn)
    hb u him (z := act d.radical j z) (delta := act d.radical j delta)
  rw [←hja] at base
  have hi : 2 < (B d.radical (act d.radical j a)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (act d.radical j delta)) := by
    rw [Escape.PairingControl.FirstPairing.B_act hb2 j a p.start_color,U_act,
      relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hstrict
  obtain ⟨t,hat,b,hbt,hbstrict,hgen,q,hq2⟩ := base (p.act j)
    (by simpa only [CriticalPath.act,actWalk_getVert] using
      (adjacent_act_iff d.radical j _ _).mpr hdelta) hi
  have hcancel (v : Vertex d.radical) : act d.radical j⁻¹ (act d.radical j v) = v := by
    rw [←act_mul,mul_inv_cancel,act_one]
  refine ⟨act d.radical j⁻¹ t,?_,act d.radical j⁻¹ b,?_,?_,?_,?_⟩
  · simpa only [hcancel] using (adjacent_act_iff d.radical j⁻¹ _ _).mpr hat
  · exact (adjacent_act_iff d.radical j⁻¹ _ _).mpr hbt
  · have hh : 2 < (B d.radical (act d.radical j⁻¹ (act d.radical j a))
        ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical (act d.radical j⁻¹ b)) := by
      rw [Escape.PairingControl.FirstPairing.B_act hb2 j⁻¹ (act d.radical j a)
        (by rw [action_preserves_color,p.start_color]),U_act,
        relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
      exact hbstrict
    simpa only [hcancel] using hh
  · have hh := congrArg (Subgroup.map (MulAut.conj (j⁻¹)⁻¹).toMonoidHom) hgen
    simpa only [Subgroup.map_sup,←Q_act,←stabilizer_act,CriticalPath.act,actWalk_getVert,hcancel] using hh
  · have hh : ∃ w : CriticalPath d.radical (replacementGeometry h d)
        (act d.radical j⁻¹ b) (act d.radical j⁻¹ ((p.act j).walk.getVert 2)),
        w.walk.getVert 2 = a := by
      refine ⟨q.act j⁻¹,?_⟩
      simpa only [CriticalPath.act,actWalk_getVert,hcancel] using congrArg (act d.radical j⁻¹) hq2
    rw [CriticalPath.act,actWalk_getVert] at hh
    rw [hcancel] at hh
    exact hh

include e hz hn in
/-- A strict forward slice in the full cube image is impossible at distance four. -/
theorem cube_strict_forward_false_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hstrict : 2 < (B d.radical a ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) : False := by
  have hb2 : 2 < replacementDistance h d := by omega
  let s := fullSymmetricAction_knownSimple h e hz hn d hb2
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let v := p.walk.getVert 2
  have hv : color d.radical v = false := (p.vertex_color (by omega)).mpr (by decide)
  have hnext : 2 < (B d.radical v ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical z) := by
    by_contra! hsmall
    exact cube_strict_small_opposite_false_knownSimple hb u him p hstrict hsmall
  obtain ⟨q,hq,hxN,htriple⟩ := cube_strict_backward_triple_at_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u him p hstrict
  obtain ⟨q₀,hq₀2,hq₀3⟩ : ∃ q₀ : CriticalPath d.radical (replacementGeometry h d) q.start v,
      q₀.walk.getVert 2 = a ∧ q₀.walk.getVert 3 = p.walk.getVert 1 := by
    have hh : ∃ q₀ : CriticalPath d.radical (replacementGeometry h d)
        q.start (p.walk.getVert (p.walk.length-2)),
        q₀.walk.getVert 2 = a ∧ q₀.walk.getVert 3 = p.walk.getVert 1 := by
      refine ⟨q.path,?_,?_⟩
      · simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (by omega)
      · exact q.overlap 1 (by omega)
    rw [show p.walk.length - 2 = 2 by omega] at hh
    exact hh
  let r : CriticalPath d.radical (replacementGeometry h d) v q.start := {
    start_color := q₀.end_color
    walk := q₀.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,q₀.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc q₀ }
  have hql : q₀.walk.length = 4 := q₀.length_eq_b.trans hb
  have hr1 : r.walk.getVert 1 = p.walk.getVert 1 := by
    change q₀.walk.reverse.getVert 1 = _
    rw [SimpleGraph.Walk.getVert_reverse,hql]
    exact hq₀3
  have hr2 : r.walk.getVert 2 = a := by
    change q₀.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,hql]
    exact hq₀2
  have hve : Adjacent d.radical v (p.walk.getVert 1) := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hvf : Adjacent d.radical v (p.walk.getVert 3) :=
    (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzf : Adjacent d.radical z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  obtain ⟨l,hlv,hlf⟩ := stabilizer_transitive_neighbors d.radical v hvf hve
  have hdelta : Adjacent d.radical (act d.radical l z) (r.walk.getVert 1) := by
    rw [hr1,←hlf]
    exact (adjacent_act_iff d.radical l _ _).mpr hzf
  have hdeltaStrict : 2 < (B d.radical v ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (act d.radical l z)) := by
    have hB := Escape.PairingControl.FirstPairing.B_act (geometry := replacementGeometry h d) hb2 l v hv
    rw [show act d.radical l v = v from hlv] at hB
    rw [hB,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hnext
  obtain ⟨t,hvt,b,hbt,hbstrict,hgen,w,hw2⟩ :=
    cube_strict_neighbor_backward_at hb u him r hdelta hdeltaStrict
  have hae : Adjacent d.radical a (p.walk.getVert 1) := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hAc := cube_strict_seed_intersection_eq_edge s hb2 u hfull p.start_color hae hve hstrict
  have hBc := cube_strict_seed_intersection_eq_edge s hb2 u hfull hv hvt hbt hbstrict
  have hedgeCent {t₀ : Vertex d.radical} (hc₀ : Adjacent d.radical v t₀) :
      Z d.radical t₀ ≤ centralizer (Q d.radical t₀ : Set (FreeAmalgam d.radical)) := by
    have ht₀ : color d.radical t₀ = true := by
      have hh := adjacent_color_ne d.radical hc₀
      rw [hv] at hh
      exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
    intro x hx
    rw [Z,if_neg (by simp [ht₀])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hcentral : Z d.radical a ⊓ Z d.radical v ⊓ Z d.radical b ≤
      centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    rw [←hgen,hr1]
    exact sup_le
      (le_centralizer_iff.mp (inf_le_left.trans (hAc.le.trans (hedgeCent hve))))
      (le_centralizer_iff.mp ((le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
        (hBc.le.trans (hedgeCent hvt))))
  obtain ⟨w₀,hw₀2⟩ : ∃ w₀ : CriticalPath d.radical (replacementGeometry h d) b a,
      w₀.walk.getVert 2 = v := by
    have hh : ∃ w₀ : CriticalPath d.radical (replacementGeometry h d) b (r.walk.getVert 2),
        w₀.walk.getVert 2 = v := ⟨w,hw2⟩
    rwa [hr2] at hh
  let wr : CriticalPath d.radical (replacementGeometry h d) a b := {
    start_color := w₀.end_color
    walk := w₀.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,w₀.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse_pair s hc w₀ }
  have hwrl : w₀.walk.length = 4 := w₀.length_eq_b.trans hb
  have hwr2 : wr.walk.getVert 2 = v := by
    change w₀.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,hwrl]
    exact hw₀2
  exact cube_strict_forward_triple_false_knownSimple hb u him wr
    (by simpa only [hwr2] using hstrict) (by simpa only [hwr2] using hcentral)

include e hz hn in
/-- The full cube radical image cannot have replacement distance four. -/
theorem cube_distance_four_false_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom) : False := by
  obtain ⟨z,p,_,hi⟩ := DistanceFour.cube_initial_selection_knownSimple
    (e := e) (hz := hz) (hn := hn) hb u him
  exact cube_strict_forward_false_knownSimple hb u him p hi

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
