module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneShiftedConfiguration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardRigidity
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPredecessorSlice

/-!
# Exact strict slices in the original cubic plane graph

The full seed Z_d fixed by an incident plane edge Q_t is precisely its
omega-center Z_t. The known full-seed fixed index is four; the central edge
attachment gives the same index in U_d. Since Z_t lies in the Baumann slice
B_a at every other component vertex incident with t, a strict slice has
index exactly four, and Z_d intersect B_a = Z_d intersect Z_a = Z_t.
This argument needs neither distance four nor small critical images, and
also applies in the centrally generated full-omega case.

For two small backward critical paths d--c and d--c' sharing t and a,
paired generation identifies their common full kernel with Z_t. The two
reverse predecessor bounds place Z_d intersect B_a in that common kernel.
Thus this configuration has the same exact slice even without assuming
strictness. Applying this to the original normalized selector retains the
component switch, both distinct midpoints, both backward paths and both
generation identities, and identifies their literal seed intersection.

The whole-core and C.1.32 consumers retain the Borel and centrally generated
omega alternatives, the distance-four and small-image premises, the original
projection with kernel E, and both full moving covers. The required index-two
end-slice bounds still require exclusion of the strict index-four case;
normality of the common kernel alone does not supply those bounds. The
larger-distance exclusions and both final core exhaustions remain open.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.6)--(5.8) and the paired comparison in (5.12)(3), printed
pp.917--920,926--927; Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk


include h e hz hk in
/-- The full seed fixed by its incident plane edge is exactly the edge
omega-center, with index four in both the full and moving seeds. -/
theorem plane_edge_full_seed_fixer
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {d t : Vertex Rg} (hd : color Rg d = false) (hdt : Adjacent Rg d t) :
    Z Rg d ⊓ centralizer (Q Rg t : Set (FreeAmalgam Rg)) = Z Rg t ∧
      (Z Rg t).relIndex (Z Rg d) = 4 ∧ (Z Rg t).relIndex (U Rg d) = 4 := by
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hdt
    rw [hd] at hh
    cases he : color Rg t <;> simp_all
  have hZQ : Z Rg d ≤ Q Rg d := by
    apply Z_le_Q_of_dist_lt Rg d ((sourceGeometry h).exists_critical d hd)
    rw [SimpleGraph.dist_self,(sourceGeometry h).distance_constant _ hd]
    exact sourceDistance_pos h
  have hZX := (sourceGeometry h).omega_bound d hd (by
    rw [(sourceGeometry h).distance_constant _ hd]
    exact sourceDistance_pos h)
  have hfixed : Z Rg d ⊓ centralizer (Q Rg t : Set (FreeAmalgam Rg)) = Z Rg t := by
    apply le_antisymm
    · intro v hv
      rw [Z,if_neg (by simp [ht])]
      exact mem_omegaCenter_iff.mpr
        ⟨(hZQ.trans (Q_le_adjacent_h Rg ht hdt)) hv.1,
          (mem_omegaCenter_iff.mp (hZX hv.1)).2.1,hv.2⟩
    · refine le_inf (adjacent_Z_le Rg hd hdt) ?_
      intro v hv
      rw [Z,if_neg (by simp [ht])] at hv
      exact (mem_omegaCenter_iff.mp hv).2.2
  have hfull : (Z Rg t).relIndex (Z Rg d) = 4 := by
    rw [←hfixed,inf_relIndex_left]
    have hi := remaining_edge_full_seed_fixed_index h e hz hk u (Or.inl hR) hd hdt
    rwa [plane_edgeOffenderJoin_eq h e hz hk u hR hd hdt] at hi
  have hseed : Z Rg d = U Rg d ⊔ Z Rg t := vertex_seed_eq_moving_sup_edge h e hz hd hdt
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) d hd
  have hindexU : (Z Rg t).relIndex (Z Rg d) = (Z Rg t).relIndex (U Rg d) := by
    rw [hseed,sup_comm (U Rg d)]
    have hn : U Rg d ≤ normalizer (Z Rg t : Set (FreeAmalgam Rg)) :=
      (((DistanceEight.U_le_Z Rg d).trans (le_centralizer (Z Rg d))).trans
        (centralizer_le (adjacent_Z_le Rg hd hdt))).trans (Subgroup.centralizer_le_normalizer _)
    exact relIndex_sup_of_normalized _ _ hn
  exact ⟨hfixed,hfull,hindexU ▸ hfull⟩

private theorem eq_four_of_dvd_four {n : ℕ} (hn : n ∣ 4) (hlo : 2 < n) : n = 4 := by
  have hhi := Nat.le_of_dvd (by decide : 0 < 4) hn
  have hc : n = 3 ∨ n = 4 := by omega
  rcases hc with rfl | hc
  · norm_num at hn
  · exact hc

include h e hz hk in
/-- Every strict plane slice is exactly the shared edge omega-center.
This holds independently of the critical distance being four, of small
critical images, and of the full-omega central-generation alternative. -/
theorem plane_strict_slice_eq_edge
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a d t : Vertex Rg} (ha : color Rg a = false) (hd : color Rg d = false)
    (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t)
    (hs : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d)) :
    Z Rg d ⊓ B Rg a ((sourceGeometry h).Z_normal _) = Z Rg t ∧
      Z Rg d ⊓ Z Rg a = Z Rg t ∧
      (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (Z Rg d) = 4 ∧
      (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) = 4 := by
  have hb := distance_gt_two h e hz hk
  obtain ⟨_,hfull,hmove⟩ := plane_edge_full_seed_fixer h e hz hk u hR hd hdt
  have hZtB : Z Rg t ≤ B Rg a ((sourceGeometry h).Z_normal _) :=
    (adjacent_Z_le Rg ha hat).trans (Escape.EdgeTransfer.Z_le_B hb a ha)
  let := finite_Z Rg d
  let : Finite (U Rg d) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg d)) (inclusion_injective _)
  have hdvd : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∣ 4 := by
    rw [←hmove]
    exact relIndex_dvd_of_le_left _ hZtB
  have hU := eq_four_of_dvd_four hdvd hs
  have hZ : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (Z Rg d) = 4 := by
    apply Nat.le_antisymm
    · exact (relIndex_le_of_le_left hZtB index_ne_zero_of_finite).trans_eq hfull
    · rw [←hU]
      exact relIndex_le_of_le_right (DistanceEight.U_le_Z Rg d) index_ne_zero_of_finite
  have hslice : Z Rg d ⊓ B Rg a ((sourceGeometry h).Z_normal _) = Z Rg t := by
    have htK : Z Rg t ≤ Z Rg d ⊓ B Rg a ((sourceGeometry h).Z_normal _) :=
      le_inf (adjacent_Z_le Rg hd hdt) hZtB
    have hi := relIndex_mul_relIndex (Z Rg t)
      (Z Rg d ⊓ B Rg a ((sourceGeometry h).Z_normal _)) (Z Rg d) htK inf_le_left
    rw [inf_relIndex_left,hZ,hfull] at hi
    exact le_antisymm (relIndex_eq_one.mp (by omega)) htK
  refine ⟨hslice,?_,hZ,hU⟩
  exact le_antisymm
    ((inf_le_inf_left _ (Escape.EdgeTransfer.Z_le_B hb a ha)).trans_eq hslice)
    (le_inf (adjacent_Z_le Rg hd hdt) (adjacent_Z_le Rg ha hat))

include h e hz hk in
/-- A paired backward configuration identifies its full Baumann slice with
the common full critical kernel and the actual shared edge omega-center. -/
theorem plane_paired_backward_slice
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {a c c' d t s : Vertex Rg}
    (q : CriticalPath Rg (sourceGeometry h) d c)
    (q' : CriticalPath Rg (sourceGeometry h) d c')
    (hqa : q.walk.getVert 2 = a) (hqa' : q'.walk.getVert 2 = a)
    (hqt : q.walk.getVert 1 = t) (hqt' : q'.walk.getVert 1 = t)
    (hq : (Q Rg c).relIndex (Z Rg d) < 4)
    (hq' : (Q Rg c').relIndex (Z Rg d) < 4)
    (hds : Adjacent Rg d s)
    (hgen : Q Rg s ⊔ (Z Rg c ⊔ Z Rg c') = stabilizer Rg d) :
    (Z Rg d ⊓ Q Rg c) ⊓ (Z Rg d ⊓ Q Rg c') = Z Rg t ∧
      Z Rg d ⊓ B Rg a ((sourceGeometry h).Z_normal _) = Z Rg t ∧
      (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (Z Rg d) = 4 ∧
      (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) = 4 := by
  have hb := distance_gt_two h e hz hk
  have hl : q.walk.length = 4 := q.length_eq_b.trans hb4
  have ha : color Rg a = false := by
    rw [←hqa]
    exact (q.vertex_color (by omega)).mpr (by decide)
  have hdt : Adjacent Rg d t := by
    rw [←hqt]
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      q.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent Rg a t := by
    rw [←hqa,←hqt]
    exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (q.walk.adj_getVert_succ (i := 1) (by omega)))
  have endpoint {w : Vertex Rg} (r : CriticalPath Rg (sourceGeometry h) d w)
      (hr : r.walk.getVert 1 = t) : Z Rg w ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg w ((sourceGeometry h).exists_critical w r.end_color)
    rw [←hr,SimpleGraph.dist_comm,r.dist_end,
      (sourceGeometry h).distance_constant w r.end_color]
    have hrl : r.walk.length = sourceDistance h := r.length_eq_b
    have hbpos := sourceDistance_pos h
    change r.walk.length-1 < sourceDistance h
    omega
  have hinside : Z Rg c ⊔ Z Rg c' ≤ edgeOffenderJoin d t := by
    rw [plane_edgeOffenderJoin_eq h e hz hk u hR q.start_color hdt]
    exact sup_le (endpoint q hqt) (endpoint q' hqt')
  have hgen' : (edgeOffenderJoin d s ⊔ Z Rg c) ⊔ Z Rg c' = stabilizer Rg d := by
    rw [plane_edgeOffenderJoin_eq h e hz hk u hR q.start_color hds,sup_assoc]
    exact hgen
  obtain ⟨_,_,hfix,hindex⟩ := remaining_paired_small_kernel_comparison h e hz hk u
    (Or.inl hR) q q' hq hq' hds hdt hgen' hinside
  rw [plane_edgeOffenderJoin_eq h e hz hk u hR q.start_color hdt] at hfix
  obtain ⟨hfixed,_,hmoveEdge⟩ := plane_edge_full_seed_fixer h e hz hk u hR q.start_color hdt
  rw [hfixed] at hfix
  have slice_le {w : Vertex Rg} (r : CriticalPath Rg (sourceGeometry h) d w)
      (hra : r.walk.getVert 2 = a) :
      Z Rg d ⊓ B Rg a ((sourceGeometry h).Z_normal _) ≤ Q Rg w := by
    let rr : CriticalPath Rg (sourceGeometry h) w d :=
      ⟨r.end_color,r.walk.reverse,
        by rw [SimpleGraph.Walk.length_reverse,r.shortest,SimpleGraph.dist_comm],reverse_pair h e r⟩
    have hrl : r.walk.length = 4 := r.length_eq_b.trans hb4
    have hmid : rr.walk.getVert (rr.walk.length-2) = a := by
      change r.walk.reverse.getVert (r.walk.reverse.length-2) = a
      rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,hrl]
      exact hra
    simpa only [hmid] using critical_predecessor_slice_le_start_core h hb rr
  have hslice : Z Rg d ⊓ B Rg a ((sourceGeometry h).Z_normal _) = Z Rg t := by
    apply le_antisymm
    · rw [←hfix]
      exact le_inf (le_inf inf_le_left (slice_le q hqa))
        (le_inf inf_le_left (slice_le q' hqa'))
    · exact le_inf (adjacent_Z_le Rg q.start_color hdt)
        ((adjacent_Z_le Rg ha hat).trans (Escape.EdgeTransfer.Z_le_B hb a ha))
  have hfull : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (Z Rg d) = 4 := by
    rw [←inf_relIndex_left,hslice,←hfix]
    exact hindex
  have hZU : (Z Rg d ⊓ B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) =
      (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) := by
    have hh := relIndex_inf_mul_relIndex (B Rg a ((sourceGeometry h).Z_normal _))
      (Z Rg d) (U Rg d)
    rw [relIndex_eq_one.mpr (DistanceEight.U_le_Z Rg d),
      inf_of_le_right (DistanceEight.U_le_Z Rg d),mul_one] at hh
    simpa only [inf_comm (Z Rg d)] using hh.symm
  rw [hslice] at hZU
  exact ⟨hfix,hslice,hfull,by rw [←hZU,hmoveEdge]⟩

include h e hz hk in
/-- The original selector supplies an exact full-seed and moving slice of
index four, with its common kernel equal to the literal edge omega-center,
unless full omega is centrally generated. The switch and both paths are kept. -/
theorem plane_small_critical_shifted_slice
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    (hsmall : ∀ a z (_p : CriticalPath Rg (sourceGeometry h) a z),
      (Q Rg z).relIndex (Z Rg a) < 4)
    {z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hd : Adjacent Rg delta (p.walk.getVert 1))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta)) :
    (∀ v : Vertex Rg, color Rg v = false →
      (X Rg v = U Rg v ⊔
        (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
      X Rg v = Z Rg v) ∨
    (∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        2 < (Q Rg (alpha Rg)).relIndex (Z Rg z ⊔ Z Rg (act Rg x z)) ∧
        x ∈ normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ Q Rg (p.walk.getVert 1) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let d := act Rg g delta
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
          ∃ q' : CriticalPath Rg (sourceGeometry h) d (p'.walk.getVert 2),
            q.walk.getVert 1 = t ∧ q'.walk.getVert 1 = t ∧
            (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            (∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i) ∧
            Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≠ Z Rg d ⊓ Q Rg (p'.walk.getVert 2) ∧
            ((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊓
              (Z Rg d ⊓ Q Rg (p'.walk.getVert 2))).relIndex (Z Rg d) = 4 ∧
            2 < (Q Rg d).relIndex (Z Rg (p.walk.getVert 2) ⊔ Z Rg (p'.walk.getVert 2)) ∧
            (Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊓
              (Z Rg d ⊓ Q Rg (p'.walk.getVert 2)) = Z Rg t ∧
            Z Rg d ⊓ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) = Z Rg t ∧
            Z Rg d ⊓ Z Rg (alpha Rg) = Z Rg t ∧
            (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (Z Rg d) = 4 ∧
            (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) = 4 ∧
            ∃ s, Adjacent Rg d s ∧ Q Rg s ⊔ Q Rg t = stabilizer Rg d ∧
              Q Rg s ⊔ (Z Rg (p.walk.getVert 2) ⊔ Z Rg (p'.walk.getVert 2)) = stabilizer Rg d) := by
  rcases plane_small_critical_shifted_configuration h e hz hk u hR hb4 hsmall p hd hs
    with hc | ⟨t,hat,r,hr,p',hverts,hgen,hpair,hlarge,hnorm,hinside,g,hg,hgt,
      hstrict,q,q',hqt,hqt',hqv,hqv',hne,hindex,hlarge',s,hds,hpair',hgen'⟩
  · exact Or.inl hc
  right
  have hqa : q.walk.getVert 2 = alpha Rg := by simpa using hqv 0 (by omega)
  have hqa' : q'.walk.getVert 2 = alpha Rg := by simpa using hqv' 0 (by omega)
  obtain ⟨hcommon,hslice,hfull,hmove⟩ := plane_paired_backward_slice h e hz hk u hR hb4
    q q' hqa hqa' hqt hqt' (hsmall _ _ q) (hsmall _ _ q') hds hgen'
  have hdt : Adjacent Rg (act Rg g delta) t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hd
  have hseed := (plane_strict_slice_eq_edge h e hz hk u hR rfl q.start_color hat hdt hstrict).2.1
  exact ⟨t,hat,r,hr,p',hverts,hgen,hpair,hlarge,hnorm,hinside,g,hg,hgt,hstrict,
    q,q',hqt,hqt',hqv,hqv',hne,hindex,hlarge',hcommon,hslice,hseed,hfull,hmove,s,hds,hpair',hgen'⟩

omit hk in
include h e hz in
/-- Whole-core application identifying the paired backward slices and their
shared edge omega-center from the retained small-image premise and a strict slice. -/
theorem coreExhaustion_or_cubic_plane_shifted_slice :
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
          ∀ z delta (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
            Adjacent Rg delta (p.walk.getVert 1) →
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta) →
    (∀ v : Vertex Rg, color Rg v = false →
      (X Rg v = U Rg v ⊔
        (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
      X Rg v = Z Rg v) ∨
    (∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        2 < (Q Rg (alpha Rg)).relIndex (Z Rg z ⊔ Z Rg (act Rg x z)) ∧
        x ∈ normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ Q Rg (p.walk.getVert 1) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let d := act Rg g delta
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
          ∃ q' : CriticalPath Rg (sourceGeometry h) d (p'.walk.getVert 2),
            q.walk.getVert 1 = t ∧ q'.walk.getVert 1 = t ∧
            (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            (∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i) ∧
            Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≠ Z Rg d ⊓ Q Rg (p'.walk.getVert 2) ∧
            ((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊓
              (Z Rg d ⊓ Q Rg (p'.walk.getVert 2))).relIndex (Z Rg d) = 4 ∧
            2 < (Q Rg d).relIndex (Z Rg (p.walk.getVert 2) ⊔ Z Rg (p'.walk.getVert 2)) ∧
            (Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊓
              (Z Rg d ⊓ Q Rg (p'.walk.getVert 2)) = Z Rg t ∧
            Z Rg d ⊓ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) = Z Rg t ∧
            Z Rg d ⊓ Z Rg (alpha Rg) = Z Rg t ∧
            (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (Z Rg d) = 4 ∧
            (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) = 4 ∧
            ∃ s, Adjacent Rg d s ∧ Q Rg s ⊔ Q Rg t = stabilizer Rg d ∧
              Q Rg s ⊔ (Z Rg (p.walk.getVert 2) ⊔ Z Rg (p'.walk.getVert 2)) = stabilizer Rg d))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 hsmall _ _ p hd hstrict =>
        plane_small_critical_shifted_slice h e hz hk u hplane hb4 hsmall p hd hstrict⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application, preserving the original projection and both
full covers. The small-image and central-omega branches remain explicit. -/
theorem rankTwo_or_cubic_plane_shifted_slice :
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
          ∀ z delta (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
            Adjacent Rg delta (p.walk.getVert 1) →
            2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta) →
    (∀ v : Vertex Rg, color Rg v = false →
      (X Rg v = U Rg v ⊔
        (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) ∧
      X Rg v = Z Rg v) ∨
    (∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      ∃ p' : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, p'.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Q Rg (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        2 < (Q Rg (alpha Rg)).relIndex (Z Rg z ⊔ Z Rg (act Rg x z)) ∧
        x ∈ normalizer (Q Rg (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ Q Rg (p.walk.getVert 1) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let d := act Rg g delta
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
          ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
          ∃ q' : CriticalPath Rg (sourceGeometry h) d (p'.walk.getVert 2),
            q.walk.getVert 1 = t ∧ q'.walk.getVert 1 = t ∧
            (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
            (∀ i ≤ 2, q'.walk.getVert (i+2) = p'.walk.getVert i) ∧
            Z Rg d ⊓ Q Rg (p.walk.getVert 2) ≠ Z Rg d ⊓ Q Rg (p'.walk.getVert 2) ∧
            ((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊓
              (Z Rg d ⊓ Q Rg (p'.walk.getVert 2))).relIndex (Z Rg d) = 4 ∧
            2 < (Q Rg d).relIndex (Z Rg (p.walk.getVert 2) ⊔ Z Rg (p'.walk.getVert 2)) ∧
            (Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊓
              (Z Rg d ⊓ Q Rg (p'.walk.getVert 2)) = Z Rg t ∧
            Z Rg d ⊓ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) = Z Rg t ∧
            Z Rg d ⊓ Z Rg (alpha Rg) = Z Rg t ∧
            (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (Z Rg d) = 4 ∧
            (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) = 4 ∧
            ∃ s, Adjacent Rg d s ∧ Q Rg s ⊔ Q Rg t = stabilizer Rg d ∧
              Q Rg s ⊔ (Z Rg (p.walk.getVert 2) ⊔ Z Rg (p'.walk.getVert 2)) = stabilizer Rg d))) :=
  (coreExhaustion_or_cubic_plane_shifted_slice h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
