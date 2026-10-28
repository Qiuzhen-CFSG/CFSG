module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePairedKernelSlice
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePairedKernelSlice

/-!
# Small reciprocal slices for the original generating plane paths

Suppose the midpoint edge cores of a critical four-edge path generate its
stabilizer and the backward Baumann slice is strict. The opposite slice has
index at most two. To prove this, a strict opposite slice would give two
backward critical paths with a common midpoint and large joint endpoint
image. Select another generating edge at their starting vertex. The plane
large-subactor theorem makes this edge and the two endpoint seeds generate.
The raw comparisons now concern the same full kernel, rather than two
different kernels. They place this index-at-most-two kernel in the Baumann
subgroup, contradicting the transported strict slice.

The original backward selector supplies the midpoint generation and the
strict backward slice, so its opposite slice is now unconditionally small
under the retained distance-four and small-critical-image assumptions. The
paired-kernel alternative from the preceding reduction is discharged.
The full seed, both moving covers and the cubic projection with kernel E
are retained. The small-slice terminal argument, remaining plane/Borel
branches and both whole-core exhaustions still belong to the reconstruction.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.6)(a), (5.12)(1),(3), printed pp.917--918,924--927;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
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
private theorem paired_common_midpoint_small_slice
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z z' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (p' : CriticalPath Rg (sourceGeometry h) a z')
    (hfirst : p'.walk.getVert 1 = p.walk.getVert 1)
    (hcenter : p'.walk.getVert 2 = p.walk.getVert 2)
    (hmid : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hmid' : Q Rg (p'.walk.getVert 1) ⊔ Q Rg (p'.walk.getVert 3) =
      stabilizer Rg (p'.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a))
    (hlarge : 2 < (Q Rg a).relIndex (Z Rg z ⊔ Z Rg z')) :
    (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) ≤ 2 := by
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hav : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcv : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨s,has,x,hx,hgen,hpair,hnorm,hinside⟩ :=
    normalized_plane_selectors_at h e hz hk u hR p (hsmall _ _ p)
  have hpairFirst : Q Rg s ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a := by
    apply le_antisymm
    · exact sup_le (fun _ hv => hv.2 _ (adjacent_symm Rg has))
        (fun _ hv => hv.2 _ (adjacent_symm Rg hav))
    · rw [←hgen]
      exact sup_le (sup_le le_sup_left ((le_sup_left.trans hinside).trans le_sup_right))
        ((le_sup_right.trans hinside).trans le_sup_right)
  have endpoint_le {w : Vertex Rg}
      (r : CriticalPath Rg (sourceGeometry h) a w)
      (hrt : r.walk.getVert 1 = p.walk.getVert 1) : Z Rg w ≤ Q Rg (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt Rg w ((sourceGeometry h).exists_critical w r.end_color)
    rw [←hrt,SimpleGraph.dist_comm,r.dist_end,
      (sourceGeometry h).distance_constant w r.end_color]
    have hh : r.walk.length = sourceDistance h := r.length_eq_b
    change r.walk.length-1 < sourceDistance h
    omega
  have hgenPair : (Q Rg s ⊔ Z Rg z) ⊔ Z Rg z' = stabilizer Rg a := by
    rw [sup_assoc]
    exact plane_edge_pair_large_subactor_generates h e hz hk u hR p.start_color has hav
      hpairFirst _ (sup_le (endpoint_le p rfl) (endpoint_le p' hfirst)) hlarge
  obtain ⟨g,hg,hgs⟩ := stabilizer_transitive_neighbors Rg a hav has
  let d := act Rg g (p.walk.getVert 2)
  have hds : Adjacent Rg d s := by
    rw [←hgs]
    exact (adjacent_act_iff Rg g _ _).mpr hcv
  have hcommon := plane_raw_paired_kernel_le_slice h e hz hk u hR hb4 hsmall p p' has hds
    hgenPair hpairFirst (by rwa [hfirst]) g hg rfl g hg (by rw [hcenter])
    hmid hmid' (by exact hback) (by rwa [hcenter])
  have hKB : Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
    simpa only [hcenter,inf_idem] using hcommon.2.1
  have hindex := (raw_preceding_kernel_normalized h e hz hk u hR hb4 hsmall p has hds).2
  let := finite_Z Rg d
  let : Finite (U Rg d) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg d)) (inclusion_injective _)
  have hsmallD : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ≤ 2 := by
    have hi := relIndex_le_of_le_left hKB
      (index_ne_zero_of_finite (H := (Z Rg d ⊓ Q Rg (p.walk.getVert 2)).subgroupOf (Z Rg d)))
    rw [inf_relIndex_left] at hi
    exact ((relIndex_le_of_le_right (DistanceEight.U_le_Z Rg d) index_ne_zero_of_finite).trans hi).trans hindex
  have hBmap : (B Rg a ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg a ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb a p.start_color
      ((stabilizer Rg a).inv_mem hg))
  change (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
    (U Rg (act Rg g (p.walk.getVert 2))) ≤ 2 at hsmallD
  rwa [U_act,←hBmap,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hsmallD

include h e hz hk in
/-- A strict backward slice on a generating midpoint path forces its
literal opposite slice to have index at most two. -/
theorem plane_generating_midpoint_reciprocal_slice
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hmid : Q Rg (p.walk.getVert 1) ⊔ Q Rg (p.walk.getVert 3) =
      stabilizer Rg (p.walk.getVert 2))
    (hback : 2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a)) :
    (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) ≤ 2 := by
  by_contra hn
  have hforward := Nat.lt_of_not_ge hn
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb4
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hav : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcv : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨s,has,x,hx,hgen,hpair,hnorm,hinside⟩ :=
    normalized_plane_selectors_at h e hz hk u hR p (hsmall _ _ p)
  have hfirst : Q Rg s ⊔ Q Rg (p.walk.getVert 1) = stabilizer Rg a := by
    apply le_antisymm
    · exact sup_le (fun _ hv => hv.2 _ (adjacent_symm Rg has))
        (fun _ hv => hv.2 _ (adjacent_symm Rg hav))
    · rw [←hgen]
      exact sup_le (sup_le le_sup_left ((le_sup_left.trans hinside).trans le_sup_right))
        ((le_sup_right.trans hinside).trans le_sup_right)
  have hxa : act Rg x a = a := hx
  have hpx : ∃ p' : CriticalPath Rg (sourceGeometry h) (act Rg x a) (act Rg x z),
      ∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i) :=
    ⟨p.act x,fun _ => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hxa] at hpx
  obtain ⟨p',hverts⟩ := hpx
  have hmid' : Q Rg (p'.walk.getVert 1) ⊔ Q Rg (p'.walk.getVert 3) =
      stabilizer Rg (p'.walk.getVert 2) := by
    rw [hverts 1,hverts 3,hverts 2,Q_act,Q_act,stabilizer_act,←Subgroup.map_sup,hmid]
  have hU : U Rg a = (U Rg a).map (MulAut.conj x⁻¹).toMonoidHom := by
    rw [←U_act,hxa]
  have hback' : 2 < (B Rg (p'.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a) := by
    rw [hverts 2,Escape.PairingControl.FirstPairing.B_act hb x _ hc,hU,
      relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hback
  have hQfirst : Q Rg (p'.walk.getVert 1) = Q Rg (p.walk.getVert 1) := by
    rw [hverts 1,Q_act]
    exact mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg))).inv_mem hnorm)
  obtain ⟨g,hg,hgs⟩ := stabilizer_transitive_neighbors Rg a hav has
  let d := act Rg g (p.walk.getVert 2)
  have hds : Adjacent Rg d s := by
    rw [←hgs]
    exact (adjacent_act_iff Rg g _ _).mpr hcv
  have hg' : x⁻¹*g ∈ stabilizer Rg a :=
    (stabilizer Rg a).mul_mem ((stabilizer Rg a).inv_mem hx) hg
  have hgd' : act Rg (x⁻¹*g) (p'.walk.getVert 2) = d := by
    rw [hverts 2,←act_mul,mul_inv_cancel_left]
  have hBmap : (B Rg a ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg a ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized hb a p.start_color
      ((stabilizer Rg a).inv_mem hg))
  have hstrict : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) := by
    change 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg g (p.walk.getVert 2)))
    rw [U_act,←hBmap,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hforward
  have hcommon := plane_raw_paired_kernel_le_slice h e hz hk u hR hb4 hsmall p p' has hds
    hgen hfirst (by rwa [hQfirst]) g hg rfl (x⁻¹*g) hg' hgd' hmid hmid' hback hback'
  obtain ⟨q,q',hq1,hq1',hqv,hqv',hI,hjoin,hne⟩ :=
    raw_paired_paths_of_strict_slice h e hz hk u hR hb4 hsmall p p' has hds hcommon.2.1 hstrict
  have hqa : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hqv 0 (by omega)
  have hqa' : q'.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hqv' 0 (by omega)
  have hqmid : Q Rg (q.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 3) =
      stabilizer Rg (q.walk.getVert 2) := by
    rw [hq1,hqa,hqv 1 (by omega)]
    exact hfirst
  have hqmid' : Q Rg (q'.walk.getVert 1) ⊔ Q Rg (q'.walk.getVert 3) =
      stabilizer Rg (q'.walk.getVert 2) := by
    rw [hq1',hqa',hqv' 1 (by omega),hQfirst]
    exact hfirst
  have hh := paired_common_midpoint_small_slice h e hz hk u hR hb4 hsmall q q'
    (hq1'.trans hq1.symm) (hqa'.trans hqa.symm) hqmid hqmid' (by rwa [hqa])
    (small_critical_distinct_kernels_joint_image h e hz hk q q' (hsmall _ _ q) (hsmall _ _ q') hne)
  rw [hqa] at hh
  have hUmap : (U Rg a).map (MulAut.conj g⁻¹).toMonoidHom = U Rg a := by
    rw [←U_act,show act Rg g a = a from hg]
  have hstrictD : 2 < (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg a) := by
    change 2 < (B Rg (act Rg g (p.walk.getVert 2)) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a)
    rw [Escape.PairingControl.FirstPairing.B_act hb g _ hc,←hUmap,
      relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hback
  exact (Nat.not_lt_of_ge hh) hstrictD

include h e hz hk in
/-- The original backward selector has a small opposite slice. The
simultaneous paired-kernel alternative has been excluded on the same graph. -/
theorem plane_selected_backward_small_slice
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2))) :
    ∃ d c, ∃ q : CriticalPath Rg (sourceGeometry h) d c,
      q.walk.getVert 2 = alpha Rg ∧
      Q Rg (q.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 3) = stabilizer Rg (alpha Rg) ∧
      2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
      (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) ≤ 2 := by
  obtain ⟨d,c,q,hqa,hmid,hback,_⟩ :=
    plane_selected_backward_kernel_reduction h e hz hk u hR hb4 hsmall p hs
  refine ⟨d,c,q,hqa,hmid,hback,?_⟩
  have hh := plane_generating_midpoint_reciprocal_slice h e hz hk u hR hb4 hsmall q
    (by rwa [hqa]) (by rwa [hqa])
  rwa [hqa] at hh

omit hk in
include h e hz in
/-- Whole-core application with the actual small opposite slice, both moving
covers and the original plane/Borel alternatives. -/
theorem coreExhaustion_or_cubic_backward_small_slice :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) →
          ∃ d c, ∃ q : CriticalPath Rg (sourceGeometry h) d c,
            q.walk.getVert 2 = alpha Rg ∧
            Q Rg (q.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 3) = stabilizer Rg (alpha Rg) ∧
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
            (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) ≤ 2)) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall _ p hstrict =>
        plane_selected_backward_small_slice h e hz hk u hplane hb4 hsmall p hstrict⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the small backward opposite slice. -/
theorem rankTwo_or_cubic_backward_small_slice :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 →
          (∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
            (Q Rg z).relIndex (Z Rg a) < 4) →
          ∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) →
          ∃ d c, ∃ q : CriticalPath Rg (sourceGeometry h) d c,
            q.walk.getVert 2 = alpha Rg ∧
            Q Rg (q.walk.getVert 1) ⊔ Q Rg (q.walk.getVert 3) = stabilizer Rg (alpha Rg) ∧
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
            (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg (alpha Rg)) ≤ 2)) :=
  (coreExhaustion_or_cubic_backward_small_slice h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
