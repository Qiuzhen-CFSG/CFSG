module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneCentralForward
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneDerivedCore

/-!
# Distance four is impossible for the original small-image cubic plane branch

A strict forward slice first forces the opposite slice to be strict.
The original paired backward selector retains a generating first-edge pair;
transporting it to the forward midpoint constructs a second strict neighbor.
The two strict edge-seed intersections make their triple central there.
Reversing that same critical path invokes the central-forward contradiction.
Finally the already proved existence of a strict forward slice discharges the
last selected-path premise. The radical is the literal nonsylow plane edge,
and neither full moving cover nor the odd cubic covering kernel is discarded.

Source: MS93 (5.12), printed pp.924--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
private theorem plane_strict_neighbor_backward_base
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hdelta : Adjacent Rg delta (p.walk.getVert 1))
    (hstrict : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg delta)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      ∃ b, Adjacent Rg b t ∧
        2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg b) ∧
        Q Rg (p.walk.getVert 1) ⊔ Q Rg t = stabilizer Rg (alpha Rg) ∧
        ∃ q : CriticalPath Rg (sourceGeometry h) b (p.walk.getVert 2),
          q.walk.getVert 2 = alpha Rg ∧ q.walk.getVert 3 = p.walk.getVert 1 := by
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨t,hat,rr,hrr,q,hq,_,hgen,hpair,hnorm,hinside,g,hg,hgt,hi,halt⟩ :=
    plane_small_critical_backward_shift h e hz hk u hR p (hsmall _ _ p) hdelta hstrict
  let x := (embedM Rg rr)⁻¹
  have hxG : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨rr⁻¹,by rw [map_inv]⟩
  have hct : Adjacent Rg (act Rg g delta) t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hdelta
  have hav : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 0) (by omega))
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hat] at hgen
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR rfl hav] at hnorm hinside
  have hxAnchor : x ∈ normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg)) := hnorm
  have hanchor : Q Rg (p.walk.getVert 1) ⊔ Q Rg t = stabilizer Rg (alpha Rg) := by
    apply le_antisymm
    · exact sup_le (fun _ hx => hx.2 _ (adjacent_symm Rg hav))
        (fun _ hx => hx.2 _ (adjacent_symm Rg hat))
    · rw [←hgen]
      exact sup_le (sup_le le_sup_right ((le_sup_left.trans hinside).trans le_sup_left))
        ((le_sup_right.trans hinside).trans le_sup_left)
  rcases halt with ⟨v,hvt,hover⟩ | ⟨v,hvt,hover⟩
  · refine ⟨t,hat,act Rg g delta,hct,hi,hanchor,?_⟩
    have hh : ∃ w : CriticalPath Rg (sourceGeometry h)
        (act Rg g delta) (p.walk.getVert (p.walk.length-2)),
        w.walk.getVert 2 = alpha Rg ∧ w.walk.getVert 3 = p.walk.getVert 1 := by
      refine ⟨v,?_,hover 1 (by omega)⟩
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
    rw [show p.walk.length - 2 = 2 by omega] at hh
    exact hh
  · have hfix : act Rg x⁻¹ (alpha Rg) = alpha Rg := inv_mem hxG
    have hlen : q.walk.length = 4 := q.length_eq_b.trans hb
    have hcancel (v : Vertex Rg) : act Rg x⁻¹ (act Rg x v) = v := by
      rw [←act_mul,mul_inv_cancel,act_one]
    refine ⟨act Rg x⁻¹ t,?_,act Rg x⁻¹ (act Rg g delta),?_,?_,?_,?_⟩
    · simpa only [hfix] using (adjacent_act_iff Rg x⁻¹ _ _).mpr hat
    · exact (adjacent_act_iff Rg x⁻¹ _ _).mpr hct
    · have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
          (MulAut.conj x).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
        mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
          hb2 (alpha Rg) rfl hxG)
      rw [U_act,inv_inv,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x).injective]
      exact hi
    · have hQfirst : (Q Rg (p.walk.getVert 1)).map (MulAut.conj x).toMonoidHom =
          Q Rg (p.walk.getVert 1) := mem_normalizer_iff_map_conj_eq.mp hxAnchor
      have hGa : (stabilizer Rg (alpha Rg)).map (MulAut.conj x).toMonoidHom =
          stabilizer Rg (alpha Rg) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer Rg (alpha Rg)).le_normalizer hxG)
      have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hanchor
      simpa only [Subgroup.map_sup,hQfirst,hGa,Q_act,inv_inv] using hh
    · have hlen' : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
      have hend : act Rg x⁻¹ (q.walk.getVert (q.walk.length-2)) =
          p.walk.getVert (p.walk.length-2) := by
        rw [hlen',hq,←act_mul,mul_inv_cancel,act_one]
      have hex : ∃ w : CriticalPath Rg (sourceGeometry h)
          (act Rg x⁻¹ (act Rg g delta))
          (act Rg x⁻¹ (q.walk.getVert (q.walk.length-2))),
          w.walk.getVert 2 = alpha Rg ∧ w.walk.getVert 3 = p.walk.getVert 1 := by
        refine ⟨v.act x⁻¹,?_,?_⟩
        · have hh := hover 0 (by omega)
          simpa only [CriticalPath.act,actWalk_getVert,Nat.zero_add,
            SimpleGraph.Walk.getVert_zero,hfix] using congrArg (act Rg x⁻¹) hh
        · simp only [CriticalPath.act,actWalk_getVert,hover 1 (by omega),hq]
          exact hcancel _
      rw [hend,show p.walk.length - 2 = 2 by omega] at hex
      simpa only [hcancel] using hex

include h e hz hk in
private theorem plane_strict_neighbor_backward_at
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hdelta : Adjacent Rg delta (p.walk.getVert 1))
    (hstrict : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg delta)) :
    ∃ t, Adjacent Rg a t ∧
      ∃ b, Adjacent Rg b t ∧
        2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg b) ∧
        Q Rg (p.walk.getVert 1) ⊔ Q Rg t = stabilizer Rg a ∧
        ∃ q : CriticalPath Rg (sourceGeometry h) b (p.walk.getVert 2),
          q.walk.getVert 2 = a ∧ q.walk.getVert 3 = p.walk.getVert 1 := by
  have hb2 : 2 < sourceDistance h := by omega
  obtain ⟨j,hja⟩ : ∃ j : FreeAmalgam Rg, act Rg j a = alpha Rg := by
    obtain ⟨j,hj⟩ := exists_mVertex_of_color Rg p.start_color
    refine ⟨j⁻¹,?_⟩
    rw [hj,act_mVertex,mul_inv_cancel]
    rfl
  have base := plane_strict_neighbor_backward_base h e hz hk hb u hR hsmall (z := act Rg j z) (delta := act Rg j delta)
  rw [←hja] at base
  have hi : 2 < (B Rg (act Rg j a)
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg j delta)) := by
    rw [Escape.PairingControl.FirstPairing.B_act hb2 j a p.start_color,U_act,
      relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hstrict
  obtain ⟨t,hat,b,hbt,hbstrict,hgen,q,hq2,hq3⟩ := base (p.act j)
    (by simpa only [CriticalPath.act,actWalk_getVert] using
      (adjacent_act_iff Rg j _ _).mpr hdelta) hi
  have hcancel (v : Vertex Rg) : act Rg j⁻¹ (act Rg j v) = v := by
    rw [←act_mul,mul_inv_cancel,act_one]
  refine ⟨act Rg j⁻¹ t,?_,act Rg j⁻¹ b,?_,?_,?_,?_⟩
  · simpa only [hcancel] using (adjacent_act_iff Rg j⁻¹ _ _).mpr hat
  · exact (adjacent_act_iff Rg j⁻¹ _ _).mpr hbt
  · have hh : 2 < (B Rg (act Rg j⁻¹ (act Rg j a))
        ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg j⁻¹ b)) := by
      rw [Escape.PairingControl.FirstPairing.B_act hb2 j⁻¹ (act Rg j a)
        (by rw [action_preserves_color,p.start_color]),U_act,
        relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
      exact hbstrict
    simpa only [hcancel] using hh
  · have hh := congrArg (Subgroup.map (MulAut.conj (j⁻¹)⁻¹).toMonoidHom) hgen
    simpa only [Subgroup.map_sup,←Q_act,←stabilizer_act,CriticalPath.act,actWalk_getVert,hcancel] using hh
  · have hh : ∃ w : CriticalPath Rg (sourceGeometry h)
        (act Rg j⁻¹ b) (act Rg j⁻¹ ((p.act j).walk.getVert 2)),
        w.walk.getVert 2 = a ∧ w.walk.getVert 3 = p.walk.getVert 1 := by
      refine ⟨q.act j⁻¹,?_,?_⟩
      · simpa only [CriticalPath.act,actWalk_getVert,hcancel] using congrArg (act Rg j⁻¹) hq2
      · simpa only [CriticalPath.act,actWalk_getVert,hcancel] using congrArg (act Rg j⁻¹) hq3
    rw [CriticalPath.act,actWalk_getVert] at hh
    rw [hcancel] at hh
    exact hh


include h e hz hk in
/-- Strict forward slices are impossible in the original small-image plane branch. -/
theorem plane_strict_forward_false
    (hb : sourceDistance h = 4) (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hstrict : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) : False := by
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let v := p.walk.getVert 2
  have hv : color Rg v = false := (p.vertex_color (by omega)).mpr (by decide)
  have hnext : 2 < (B Rg v ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg z) := by
    by_contra! hop
    exact plane_strict_forward_small_opposite_false h e hz hk u hR hb hsmall p hstrict hop
  have hdelta : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨s,has,d,hds,hdstrict,hfirst,q₀,hq₀2,hq₀3⟩ :=
    plane_strict_neighbor_backward_at h e hz hk hb u hR hsmall p hdelta hstrict
  let r : CriticalPath Rg (sourceGeometry h) v d := {
    start_color := q₀.end_color
    walk := q₀.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,q₀.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      _ q₀.start_color (by
        rw [(sourceGeometry h).distance_constant _ q₀.start_color]
        exact sourceDistance_pos h) _ q₀.end_color q₀.critical }
  have hql : q₀.walk.length = 4 := q₀.length_eq_b.trans hb
  have hr1 : r.walk.getVert 1 = p.walk.getVert 1 := by
    change q₀.walk.reverse.getVert 1 = _
    rw [SimpleGraph.Walk.getVert_reverse,hql]
    exact hq₀3
  have hr2 : r.walk.getVert 2 = a := by
    change q₀.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,hql]
    exact hq₀2
  have hve : Adjacent Rg v (p.walk.getVert 1) := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hvf : Adjacent Rg v (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzf : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := p.walk.adj_getVert_succ (i := 3) (by omega)
    rw [show 3+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  obtain ⟨l,hlv,hlf⟩ := stabilizer_transitive_neighbors Rg v hvf hve
  have hdelta : Adjacent Rg (act Rg l z) (r.walk.getVert 1) := by
    rw [hr1,←hlf]
    exact (adjacent_act_iff Rg l _ _).mpr hzf
  have hdeltaStrict : 2 < (B Rg v ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg l z)) := by
    have hB := Escape.PairingControl.FirstPairing.B_act (geometry := sourceGeometry h) hb2 l v hv
    rw [show act Rg l v = v from hlv] at hB
    rw [hB,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hnext
  obtain ⟨t,hvt,b,hbt,hbstrict,hgen,w,hw2,_⟩ :=
    plane_strict_neighbor_backward_at h e hz hk hb u hR hsmall r hdelta hdeltaStrict
  have hae : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hAc : Z Rg a ⊓ Z Rg v = Z Rg (p.walk.getVert 1) := by
    rw [inf_comm]
    exact (plane_strict_slice_eq_edge h e hz hk u hR p.start_color hv hae hve hstrict).2.1
  have hBc : Z Rg v ⊓ Z Rg b = Z Rg t := by
    rw [inf_comm]
    have hbcol := (w.start_color)
    exact (plane_strict_slice_eq_edge h e hz hk u hR hv hbcol hvt hbt hbstrict).2.1
  have hedgeCent {t₀ : Vertex Rg} (hc₀ : Adjacent Rg v t₀) :
      Z Rg t₀ ≤ centralizer (Q Rg t₀ : Set (FreeAmalgam Rg)) := by
    have ht₀ : color Rg t₀ = true := by
      have hh := adjacent_color_ne Rg hc₀
      rw [hv] at hh
      exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
    intro x hx
    rw [Z,if_neg (by simp [ht₀])] at hx
    exact (mem_omegaCenter_iff.mp hx).2.2
  have hcentral : Z Rg a ⊓ Z Rg v ⊓ Z Rg b ≤
      centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mpr
    rw [←hgen,hr1]
    exact sup_le
      (le_centralizer_iff.mp (inf_le_left.trans (hAc.le.trans (hedgeCent hve))))
      (le_centralizer_iff.mp ((le_inf (inf_le_left.trans inf_le_right) inf_le_right).trans
        (hBc.le.trans (hedgeCent hvt))))
  obtain ⟨w₀,hw₀2⟩ : ∃ w₀ : CriticalPath Rg (sourceGeometry h) b a,
      w₀.walk.getVert 2 = v := by
    have hh : ∃ w₀ : CriticalPath Rg (sourceGeometry h) b (r.walk.getVert 2),
        w₀.walk.getVert 2 = v := ⟨w,hw2⟩
    rwa [hr2] at hh
  let wr : CriticalPath Rg (sourceGeometry h) a b := {
    start_color := w₀.end_color
    walk := w₀.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,w₀.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      _ w₀.start_color (by
        rw [(sourceGeometry h).distance_constant _ w₀.start_color]
        exact sourceDistance_pos h) _ w₀.end_color w₀.critical }
  have hwrl : w₀.walk.length = 4 := w₀.length_eq_b.trans hb
  have hwr2 : wr.walk.getVert 2 = v := by
    change w₀.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,hwrl]
    exact hw₀2
  exact plane_strict_forward_central_triple_false h e hz hk u hR hb hsmall wr
    (by simpa only [hwr2] using hstrict) (by simpa only [hwr2] using hcentral)


include h e hz hk in
/-- The original cubic plane image cannot have distance four with uniformly
small critical seed images. -/
theorem plane_four_uniformly_small_false
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4) : False := by
  obtain ⟨z,p,hs⟩ := plane_exists_strict_forward_slice h e hz hk u hR hb4
  exact plane_strict_forward_false h e hz hk hb4 u hR hsmall p hs

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
