module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicRadicalImage

/-!
# Generating shifts at distance four in the original cubic graph

A small predecessor Baumann slice identifies the full reverse critical
kernel. If an eligible backward seed on a generating edge stayed in the
predecessor core, the residual-shift theorem would produce a large critical
image. Its reciprocal slice is at the original starting vertex, where the
backward failure calculation gives index two. The strict large-image slice
bound contradicts that index. Thus the eligible seed escapes, including at
distance four, without requiring the strict bound from (5.9).

In the full point-core branch this constructs a generating backward step
with the same local conjugator and every overlap vertex. A large predecessor
slice instead gives a strict forward slice on an extended reverse path;
the existing small- and large-image constructions apply there. Consequently
the original base vertex always has a generating backward configuration.
Point-core containment is equality and forces distance four. The two seeds
in the new critical pair then lie in the same selected span, proving that
span is nonabelian.

The whole-core and literal C.1.32 applications retain the original cubic
projection, its odd kernel, both moving covers of orders 16 and 32, and the
plane and Sylow radical-image alternatives. The remaining distance-four
commutator exclusions, those other radical images, natural exhaustion and
both final reconstruction outcomes are still required.

Source: Meierfrankenfeld--Stellmacher (1993), (5.7)--(5.8), printed
pp.919--920, and the initial shifted configuration of (5.12), pp.924--925;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk

include h in
private theorem small_predecessor_transporter
    {c t v : Vertex Rg} (hcol : color Rg c = false)
    (hct : Adjacent Rg c t) (hcv : Adjacent Rg c v) :
    ∃ k ∈ Ltilde Rg c, act Rg k t = v := by
  have hgen : Ltilde Rg c ⊔ Q Rg t = stabilizer Rg c := by
    apply CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
    · rw [h.relative_residual]
      exact (codisjoint_subgroupOf_sup L R).eq_top
    · exact hcol
    · exact hct
  have hn : Q Rg t ≤ normalizer (Ltilde Rg c : Set (FreeAmalgam Rg)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hxc : x⁻¹ ∈ stabilizer Rg c :=
      (stabilizer Rg c).inv_mem (hx.2 _ (adjacent_symm Rg hct))
    have hh := Ltilde_act Rg x⁻¹ c
    rw [inv_inv,show act Rg x⁻¹ c = c from hxc] at hh
    exact hh.symm
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors Rg c hct hcv
  have hprod : g ∈ (Q Rg t : Set (FreeAmalgam Rg)) *
      (Ltilde Rg c : Set (FreeAmalgam Rg)) := by
    rw [←coe_mul_of_left_le_normalizer_right _ _ hn,
      sup_comm (Q Rg t) (Ltilde Rg c),hgen]
    exact hg
  obtain ⟨q,hq,k,hkm,rfl⟩ := hprod
  refine ⟨k,hkm,?_⟩
  have hqt : act Rg q t = t := hq.1
  simpa only [act_mul,hqt] using hgt

include h e hz hk in
/-- A small predecessor slice forces every eligible backward seed on a
generating edge to escape the predecessor core. The residual-shifted path
would otherwise have a large critical image and a small reciprocal slice.
This argument includes distance four and both central covers. -/
theorem eligible_backward_escape_of_small_predecessor
    (hb : 2 < sourceDistance h) (u : S)
    (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hindex : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg a') ≤ 2)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg))
    (hel : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    ¬ Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  have hs := critical_predecessor_small_slice h e hz hk hb p hindex
  have hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [hs.2.2]
    decide
  have hslice : U Rg a' ⊓ Q Rg (alpha Rg) ≤
      B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _) :=
    (inf_le_inf_right _ (DistanceEight.U_le_Z Rg a')).trans
      (hs.1 ▸ inf_le_right)
  have hline := small_eligible_backward_failure_line h e hz hk hb u hR
    p hsmall hat hct hgen hel hbad
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hct' : Adjacent Rg (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj Rg _ _).mp hh
  have hcv : Adjacent Rg (p.walk.getVert (p.walk.length-2))
      (p.walk.getVert (p.walk.length-3)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-3) (by omega)
    rw [show p.walk.length-3+1=p.walk.length-2 by omega] at hh
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
  obtain ⟨k,hkm,hkt⟩ := small_predecessor_transporter (h := h) hcol hct' hcv
  obtain ⟨q,hlarge,_,hover,_⟩ := eligible_backward_residual_critical_path
    h e hz hk hb u hR p hsmall hat hct hgen hel hbad hslice k hkm hkt
  have hstrict := (large_critical_slices_gt_two h e hz hk hb q hlarge).2
  have hq2 : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
      hover 0 (Nat.zero_le _)
  rw [hq2,hline.2.1] at hstrict
  omega


include h e hz hk in
/-- A small predecessor slice supplies a generating backward step, including
at distance four. The local conjugator moves the original first edge and
second vertex together, and the new walk retains the entire overlap. -/
theorem full_point_backward_step_of_small_predecessor
    (u : S) (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hindex : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg a') ≤ 2) :
    ∃ c t x, x ∈ stabilizer Rg (alpha Rg) ∧
      act Rg x (p.walk.getVert 2) = c ∧
      Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hb := distance_gt_two h e hz hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hs := critical_predecessor_small_slice h e hz hk hb p hindex
  have hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [hs.2.2]
    decide
  obtain ⟨t,hat,hgen⟩ := small_image_full_point_generating_neighbor h e hz hk u hfull p hsmall
  have ha1 : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors Rg (alpha Rg) ha1 hat
  let c := act Rg x (p.walk.getVert 2)
  have hct : Adjacent Rg c t := by
    rw [←hxt]
    apply (adjacent_act_iff Rg x _ _).mpr
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hcol : color Rg c = false := by
    rw [action_preserves_color]
    exact (p.vertex_color (by omega)).mpr (by decide)
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hx))
  have hel : ¬ U Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    intro hn
    apply full_point_critical_forward_eligible h e hz hk hb u hfull p
    change U Rg (act Rg x (p.walk.getVert 2)) ≤ _ at hn
    rw [U_act,←hB] at hn
    exact (map_le_map_iff_of_injective (MulAut.conj x⁻¹).injective).mp hn
  have hescape := eligible_backward_escape_of_small_predecessor h e hz hk hb u hfull.le
    p hindex hat hct hgen hel
  let w : (cosetGraph Rg).Walk c (alpha Rg) :=
    .cons ((cosetGraph_adj Rg _ _).mpr hct)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
  have hw : w.length = 2 := rfl
  let q := p.prepend_two (Nat.le_of_lt hb) hcol w hw hescape
  have hqt : q.walk.getVert 1 = t := by
    simp only [q,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  exact ⟨c,t,x,hx,rfl,hat,hct,hgen,q,hqt,
    fun i hi => p.prepend_two_overlap _ _ _ _ _ hi⟩

include h e hz hk in
/-- The small-predecessor backward step at every original component vertex.
The same conjugator transports the generating edge and every walk vertex. -/
theorem full_point_backward_step_of_small_predecessor_at
    (u : S) (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (hindex : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg a') ≤ 2) :
    ∃ c t x, x ∈ stabilizer Rg a ∧
      act Rg x (p.walk.getVert 2) = c ∧
      Adjacent Rg a t ∧ Adjacent Rg c t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg a ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hb := distance_gt_two h e hz hk
  have hcol : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  have hidx : (B Rg ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg g⁻¹ a')) ≤ 2 := by
    simp only [CriticalPath.act,actWalk_length,actWalk_getVert]
    rw [Escape.PairingControl.FirstPairing.B_act hb g⁻¹ _ hcol,U_act,
      relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]
    exact hindex
  have base := full_point_backward_step_of_small_predecessor h e hz hk u hfull
    (a' := act Rg g⁻¹ a')
  rw [←hbase] at base
  obtain ⟨c,t,x,hx,hxc,hat,hct,hgen,q,hq1,hover⟩ := base (p.act g⁻¹) hidx
  change act Rg x ((actWalk Rg g⁻¹ p.walk).getVert 2) = c at hxc
  rw [actWalk_getVert] at hxc
  let y := g⁻¹*x*g
  have hy (v : Vertex Rg) :
      act Rg y v = act Rg g (act Rg x (act Rg g⁻¹ v)) := by
    simp only [y,act_mul]
  have hcancel (v : Vertex Rg) : act Rg g (act Rg g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hqc : ∃ r : CriticalPath Rg (sourceGeometry h)
      (act Rg g c)
      (act Rg g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2))),
      r.walk.getVert 1 = act Rg g t ∧
      ∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i := by
    refine ⟨q.act g,?_,?_⟩
    · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act Rg g) hq1
    · intro i hi
      have he := congrArg (act Rg g) (hover i (by
        simpa only [CriticalPath.act,actWalk_length] using hi))
      simpa only [CriticalPath.act,actWalk_getVert,hcancel] using he
  have hend : act Rg g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2)) =
      p.walk.getVert (p.walk.length-2) := by
    change act Rg g ((actWalk Rg g⁻¹ p.walk).getVert
      ((actWalk Rg g⁻¹ p.walk).length-2)) = _
    rw [actWalk_length,actWalk_getVert,hcancel]
  rw [hend] at hqc
  obtain ⟨r,hr1,hrover⟩ := hqc
  refine ⟨act Rg g c,act Rg g t,y,?_,?_,?_,?_,?_,r,hr1,hrover⟩
  · change act Rg y a = a
    rw [hy,show act Rg x (act Rg g⁻¹ a) = act Rg g⁻¹ a from hx,hcancel]
  · rw [hy,hxc]
  · simpa only [hcancel] using (adjacent_act_iff Rg g _ _).mpr hat
  · exact (adjacent_act_iff Rg g _ _).mpr hct
  · have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hcancel,hcancel] at he
    exact he


include h e hz hk in
/-- A strict forward slice gives a generating backward step for either
critical-image size. No lower bound of five on the distance is needed. -/
theorem full_point_backward_step_of_strict_forward
    (u : S) (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hindex : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) :
    ∃ c t x, x ∈ stabilizer Rg (alpha Rg) ∧
      act Rg x (p.walk.getVert 2) = c ∧
      Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hb := distance_gt_two h e hz hk
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hdelta : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hstep : ∃ t, Adjacent Rg (alpha Rg) t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
      ∃ x ∈ stabilizer Rg (alpha Rg),
        act Rg x (p.walk.getVert 1) = t ∧
        ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg x (p.walk.getVert 2))
          (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
            (U Rg (act Rg x (p.walk.getVert 2))) := by
    by_cases hs : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4
    · exact small_full_point_backward_shift h e hz hk u hfull p hs hdelta hindex
    · exact large_full_point_backward_shift_of_two_lt_slice h e hz hk hb u hfull p
        (by omega) hdelta hindex
  obtain ⟨t,hat,hgen,x,hx,hxt,q,hq,hover,_⟩ := hstep
  refine ⟨_,t,x,hx,rfl,hat,?_,hgen,q,hq,hover⟩
  rw [←hxt]
  exact (adjacent_act_iff Rg x _ _).mpr hdelta

include h e hz hk in
/-- The full point-core branch always has an actual generating backward
configuration at the original base vertex, including at distance four.
A small predecessor slice uses the residual-shift contradiction. A large
one becomes a strict forward slice on the extended reverse path. -/
theorem full_point_exists_generating_backward_step
    (u : S) (hfull : (Rg).map π = pointCore.map (MulAut.conj u).toMonoidHom) :
    ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
      ∃ c t x, x ∈ stabilizer Rg (alpha Rg) ∧
        act Rg x (p.walk.getVert 2) = c ∧
        Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
        Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
        ∃ q : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
          q.walk.getVert 1 = t ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hb := distance_gt_two h e hz hk
  obtain ⟨a',⟨p⟩⟩ := CriticalPath.exists_from (R := Rg)
    (geometry := sourceGeometry h) (a := alpha Rg) rfl
  by_cases hi : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg a') ≤ 2
  · exact ⟨a',p,full_point_backward_step_of_small_predecessor h e hz hk u hfull p hi⟩
  let pr : CriticalPath Rg (sourceGeometry h) a' (alpha Rg) :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        (alpha Rg) rfl (sourceDistance_pos h) a' p.end_color p.critical⟩
  have hpr : pr.walk.getVert 2 = p.walk.getVert (p.walk.length-2) := by
    change p.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse]
  obtain ⟨d,q,_,hq2⟩ := full_point_critical_reverse_prefix h e hz hk hb u hfull pr
  have hforward : 2 < (B Rg (pr.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (q.walk.getVert 2)) := by
    rw [hq2,hpr]
    omega
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg q.start_color
  have hbase : act Rg g⁻¹ (pr.walk.getVert 2) = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hq0 : ∃ q0 : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ (pr.walk.getVert 2)) (act Rg g⁻¹ d),
      2 < (B Rg (act Rg g⁻¹ (pr.walk.getVert 2)) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (q0.walk.getVert 2)) := by
    refine ⟨q.act g⁻¹,?_⟩
    simp only [CriticalPath.act,actWalk_getVert]
    rw [Escape.PairingControl.FirstPairing.B_act hb g⁻¹ _ q.start_color,U_act,
      relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]
    exact hforward
  rw [hbase] at hq0
  obtain ⟨q0,hidx⟩ := hq0
  exact ⟨_,q0,full_point_backward_step_of_strict_forward h e hz hk u hfull q0 hidx⟩


include h e hz hk in
/-- Point-core containment supplies a nonabelian selected span at distance
four, together with its actual generating backward path. The nonabelianness
comes from two seeds related by the retained local conjugator. -/
theorem point_image_nonabelian_generating_configuration
    (u : S) (hR : (Rg).map π ≤ pointCore.map (MulAut.conj u).toMonoidHom) :
    sourceDistance h = 4 ∧
      ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
        ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
          localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ ∧
        ∃ c t x, x ∈ stabilizer Rg (alpha Rg) ∧
          act Rg x (p.walk.getVert 2) = c ∧
          Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
          Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
            q.walk.getVert 1 = t ∧
            ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hb := point_image_distance_eq_four h e hz hk u hR
  obtain ⟨a',p,c,t,x,hx,hxc,hat,hct,hgen,q,hq1,hover⟩ :=
    full_point_exists_generating_backward_step h e hz hk u
      (full_point_image_of_contained h e hz hk u hR)
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
  have hZP : Z Rg (p.walk.getVert 2) ≤ P := Z_le_localZSpan Rg _ _
  have hZc : Z Rg c ≤ P := by
    rw [←hxc,Z_act]
    have hn : P.map (MulAut.conj x⁻¹).toMonoidHom = P :=
      mem_normalizer_iff_map_conj_eq.mp
        (localZSpan_normalized Rg _ _ ((stabilizer Rg (alpha Rg)).inv_mem hx))
    exact (map_mono hZP).trans_eq hn
  have hZend : Z Rg (p.walk.getVert (p.walk.length-2)) ≤ P := by
    simpa only [hl,Nat.reduceSub] using hZP
  have hnon : ⁅P,P⁆ ≠ ⊥ := by
    intro hn
    apply critical_commutator_not_central h e hz hk q
    exact (commutator_mono hZc hZend).trans (hn ▸ bot_le)
  exact ⟨hb,a',p,hnon,c,t,x,hx,hxc,hat,hct,hgen,q,hq1,hover⟩


omit hk in
include h e hz in
/-- Whole-core application: the original point-core branch now supplies
the nonabelian selected span and a generating backward configuration at
distance four. Plane and Sylow radical images remain separate branches. -/
theorem coreExhaustion_or_cubic_nonabelian_generating_configuration :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
            ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
              localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ ∧
            ∃ c t x, x ∈ stabilizer Rg (alpha Rg) ∧
              act Rg x (p.walk.getVert 2) = c ∧
              Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
              Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
              ∃ q : CriticalPath Rg (sourceGeometry h) c
                  (p.walk.getVert (p.walk.length-2)),
                q.walk.getVert 1 = t ∧
                ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom := by
  rcases coreExhaustion_or_cubic_radical_cases h e hz with
    hx | ⟨hk,hs,hb,hcovers,u,hpoint | hplane | hsylow⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl ?_⟩
    exact ⟨hpoint.2,point_image_nonabelian_generating_configuration h e hz hk u hpoint.2.le⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inl hplane)⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr (Or.inr hsylow)⟩

omit hk in
include h e hz in
/-- Literal C.1.32 consumer of the constructed distance-four configuration,
retaining the original cubic projection and both full moving covers. -/
theorem rankTwo_or_cubic_nonabelian_generating_configuration :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        ((Rg).map (CubicAction.projection h e hz hk) =
            pointCore.map (MulAut.conj u).toMonoidHom ∧
          sourceDistance h = 4 ∧
          ∃ a', ∃ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a',
            ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
              localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ ∧
            ∃ c t x, x ∈ stabilizer Rg (alpha Rg) ∧
              act Rg x (p.walk.getVert 2) = c ∧
              Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
              Q Rg t ⊔ Z Rg a' = stabilizer Rg (alpha Rg) ∧
              ∃ q : CriticalPath Rg (sourceGeometry h) c
                  (p.walk.getVert (p.walk.length-2)),
                q.walk.getVert 1 = t ∧
                ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∨
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom :=
  (coreExhaustion_or_cubic_nonabelian_generating_configuration h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

