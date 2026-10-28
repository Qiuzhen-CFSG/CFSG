module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourLargeCores
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourSmallExclusion
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicKernelTransport
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardRigidity

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourAdjustedSeed
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourSmallExclusion

/-!
# Residual fixedness in the large original Borel selection

For distinct incident movers containing both neighboring cores, their
intersection has index four over either core. A large critical endpoint
image fills this intersection. The whole neighboring-seed/core movement
therefore equals the critical commutator, with both full covers retained.

In the actual adjusted backward selection, the critical commutator is fixed
by the generating endpoint actor. For distinct movers its first-edge
invariance now extends to the whole midpoint stabilizer. Its order divides
eight, so the A6 residual fixes it; normal generation gives the same movement
for the entire selected span. For equal movers, quadraticity fixes the
critical commutator under the common mover, and generation fixes it under
the whole midpoint stabilizer directly. Thus both cases give residual
fixedness of the actual backward critical commutator.

The core containment required in the opposite direction is transported from
the forward large path using the same residual representative. The adjusted
actor, both full central attachments, strict slice and literal cubic kernel
are retained in the selection. OriginalSylowExceptional applies this to the
original c.L,d.S graph. Whole-radius/core fixedness in the remaining case and
the selected-span terminal contradiction are still required for exhaustion.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(c) and (5.12)(2), printed pp.916,925--926;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.GroupTheory Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
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
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
/-- Distinct mutually core-containing movers make the large critical image
fill their intersection, so the whole midpoint movement is the critical one. -/
theorem borel_four_large_distinct_movement_eq
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c w : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) c w)
    (hp : 4 ≤ (Q Rg w).relIndex (Z Rg c))
    (hcore : Q Rg c ≤ edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1))
    (hne : edgeOffenderJoin c (p.walk.getVert 1) ≠
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1)) :
    ⁅Z Rg c,Q Rg (p.walk.getVert 2)⁆ = ⁅Z Rg c,Z Rg w⁆ := by
  let a := p.walk.getVert 2
  let t := p.walk.getVert 1
  let J := edgeOffenderJoin c t ⊓ edgeOffenderJoin a t
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have ha : color Rg a = false := (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent Rg c t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent Rg a t := adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
    (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨Jc,_,hcJ,hQc,hcT,_⟩ := borel_edge_maximal_offenders h e hz hk u hR p.start_color hct
  obtain ⟨Ja,_,haJ,hQa,haT,_⟩ := borel_edge_maximal_offenders h e hz hk u hR ha hat
  have hQaJ : Q Rg a ≤ J := le_inf
    (borel_four_large_midpoint_core_le_mover h e hz hk u hR p hp) (hQa.trans haJ.symm.le)
  have hQcJ : Q Rg c ≤ J := le_inf (hQc.trans hcJ.symm.le) hcore
  have hZwQa : Z Rg w ≤ Q Rg a := by
    apply Z_le_Q_of_dist_lt Rg w ((sourceGeometry h).exists_critical w p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,hl,(sourceGeometry h).distance_constant _ p.end_color]
    exact distance_gt_two h e hz hk
  have hZwJ := hZwQa.trans hQaJ
  have hJG : J ≤ stabilizer Rg c :=
    (inf_le_left.trans (hcJ.le.trans hcT)).trans
      (show Q Rg t ≤ stabilizer Rg c from fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  let := finite_stabilizer Rg c
  let : Finite J := Finite.of_injective (inclusion hJG) (inclusion_injective _)
  let K := Q Rg c ⊔ Z Rg w
  have hKJ : K ≤ J := sup_le hQcJ hZwJ
  have hi : (Q Rg c).relIndex J = 4 :=
    borel_opposite_containing_core_index h e hz hk u hR p.start_color ha hct hat hne hcore
  have hr : 4 ≤ (Q Rg c).relIndex (Z Rg w) :=
    reverse_critical_image_four_le h e hz hk (sourceDistance_pos h) p hp
  have hupper := relIndex_le_of_le_right hKJ
    (show (Q Rg c).relIndex J ≠ 0 from by rw [hi]; decide)
  have hlower := relIndex_le_of_le_right (show Z Rg w ≤ K from le_sup_right)
    (show (Q Rg c).relIndex K ≠ 0 from by
      let : Finite K := Finite.of_injective (inclusion hKJ) (inclusion_injective _)
      exact index_ne_zero_of_finite)
  have hki : (Q Rg c).relIndex K = 4 := by omega
  have hmul := relIndex_mul_relIndex (Q Rg c) K J le_sup_left hKJ
  rw [hki,hi] at hmul
  have hK : K = J := le_antisymm hKJ (relIndex_eq_one.mp (by omega))
  have hcentral : Q Rg c ≤ centralizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg c p.start_color))
  have hZwG : Z Rg w ≤ stabilizer Rg c :=
    (hZwQa.trans hQaJ).trans hJG
  have hcomm : ⁅Z Rg c,Z Rg w⁆ = ⁅Z Rg c,J⁆ :=
    commutator_eq_of_centralizing_sup hK hcentral (hZwG.trans (Z_normalized Rg c))
  exact le_antisymm ((commutator_mono le_rfl hQaJ).trans_eq hcomm.symm)
    (commutator_mono le_rfl hZwQa)

include h e hz hk in
/-- Both mover comparisons fix the critical commutator under the actual
midpoint residual. In the distinct case the entire selected span has this
same movement, and that movement is invariant under the full stabilizer. -/
theorem borel_four_large_selected_fixed
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c w : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) c w)
    (hp : 4 ≤ (Q Rg w).relIndex (Z Rg c))
    (hcore : Q Rg c ≤ edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1))
    (A : Subgroup (FreeAmalgam Rg))
    (hgen : edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) ⊔ A =
      stabilizer Rg (p.walk.getVert 2))
    (hfix : ⁅Z Rg c,Z Rg w⁆ ≤ centralizer (A : Set (FreeAmalgam Rg))) :
    ⁅Z Rg c,Z Rg w⁆ ≤ fixedCore Rg (p.walk.getVert 2) ∧
      (edgeOffenderJoin c (p.walk.getVert 1) ≠
        edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) →
        ⁅localZSpan Rg c (p.walk.getVert 2),Q Rg (p.walk.getVert 2)⁆ =
          ⁅Z Rg c,Z Rg w⁆ ∧
        stabilizer Rg (p.walk.getVert 2) ≤ normalizer
          ((⁅Z Rg c,Z Rg w⁆ : Subgroup (FreeAmalgam Rg)) : Set _)) := by
  let a := p.walk.getVert 2
  let t := p.walk.getVert 1
  let D := ⁅Z Rg c,Z Rg w⁆
  let H := ⁅Z Rg c,Q Rg a⁆
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have ha : color Rg a = false := (p.vertex_color (by omega)).mpr (by decide)
  have hct : Adjacent Rg c t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hat : Adjacent Rg a t := adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
    (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hmove := borel_four_large_midpoint_movement h e hz hk u hR p hp
  have hHQ : H ≤ Q Rg a := hmove.2.1.trans (omegaCenter_le _)
  have hDQ : D ≤ Q Rg a := hmove.2.2.2.2.trans hHQ
  obtain ⟨Ja,_,haJ,_,haT,_⟩ := borel_edge_maximal_offenders h e hz hk u hR ha hat
  have hTG : Q Rg t ≤ stabilizer Rg a := fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  have hgenT : Q Rg t ⊔ A = stabilizer Rg a := by
    apply le_antisymm (sup_le hTG (le_sup_right.trans hgen.le))
    rw [←hgen]
    exact sup_le_sup (haJ.le.trans haT) le_rfl
  have distinct (hne : edgeOffenderJoin c t ≠ edgeOffenderJoin a t) :
      H = D ∧ stabilizer Rg a ≤ normalizer (D : Set (FreeAmalgam Rg)) := by
    have he : H = D := borel_four_large_distinct_movement_eq h e hz hk u hR p hp hcore hne
    refine ⟨he,?_⟩
    rw [←hgenT]
    exact sup_le (he ▸ hmove.2.2.2.1)
      ((le_centralizer_iff.mp hfix).trans (Subgroup.centralizer_le_normalizer _))
  have hDF : D ≤ fixedCore Rg a := by
    by_cases he : edgeOffenderJoin c t = edgeOffenderJoin a t
    · obtain ⟨Jc,_,hcJ,_,hcT,_,_,_,hquad⟩ :=
        borel_edge_maximal_offenders h e hz hk u hR p.start_color hct
      have hZwQa : Z Rg w ≤ Q Rg a := by
        apply Z_le_Q_of_dist_lt Rg w ((sourceGeometry h).exists_critical w p.end_color)
        rw [SimpleGraph.dist_comm,p.dist_end,hl,(sourceGeometry h).distance_constant _ p.end_color]
        exact distance_gt_two h e hz hk
      have hZwJ : Z Rg w ≤ Jc := hZwQa.trans
        ((borel_four_large_midpoint_core_le_mover h e hz hk u hR p hp).trans hcJ.le)
      have hDJ : D ≤ centralizer (Jc : Set (FreeAmalgam Rg)) := by
        apply commutator_eq_bot_iff_le_centralizer.mp
        apply le_bot_iff.mp
        change ⁅⁅Z Rg c,Z Rg w⁆,Jc⁆ ≤ ⊥
        rw [critical_whole_commutator_eq_moving h e hz p (distance_gt_two h e hz hk)]
        exact (commutator_mono
          (commutator_mono le_rfl ((DistanceEight.U_le_Z Rg w).trans hZwJ)) le_rfl).trans_eq hquad
      have hDC : D ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
        apply le_centralizer_iff.mp
        rw [←hgen]
        exact sup_le (le_centralizer_iff.mp (hDJ.trans (centralizer_le (he ▸ hcJ.le))))
          (le_centralizer_iff.mp hfix)
      exact le_inf hDQ (hDC.trans (centralizer_le (Ltilde_le_stabilizer a)))
    · obtain ⟨he,hDN⟩ := distinct he
      exact small_invariant_core_le_fixed h e hz hk ha D hDQ hDN (he ▸ hmove.2.2.1)
  refine ⟨hDF,?_⟩
  intro hne
  obtain ⟨he,hDN⟩ := distinct hne
  refine ⟨le_antisymm ?_ (he.symm.le.trans (commutator_mono (Z_le_localZSpan Rg c a) le_rfl)),hDN⟩
  have hcG : Z Rg c ≤ stabilizer Rg a :=
    ((terminal_neighbor_seed_radius hat hct).trans
      ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) a ha)).trans (fun _ hx => hx.1)
  rw [localZSpan_eq_conjugates]
  apply commutator_iSup_le_of_relative_normal (stabilizer Rg a) (Q Rg a) D _ hDN
  · intro g
    exact (map_mono hcG).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      ((stabilizer Rg a).le_normalizer ((stabilizer Rg a).inv_mem g.property)))
  · intro g
    have hm := congrArg (fun K : Subgroup (FreeAmalgam Rg) =>
      K.map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom) he
    dsimp only [H] at hm
    have hQm : (Q Rg a).map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom = Q Rg a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg a ((stabilizer Rg a).inv_mem g.property))
    have hDm : D.map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom = D :=
      mem_normalizer_iff_map_conj_eq.mp (hDN ((stabilizer Rg a).inv_mem g.property))
    rw [map_commutator,hQm,hDm] at hm
    exact hm.le

include h e hz hk in
/-- The actual adjusted forward/backward selection has residual-fixed critical
movement. Both covers, the entire central attachment, the transporter and
all the original normalization and strict-slice data are retained. -/
theorem borel_four_large_backward_fixed
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    ∃ A : Subgroup (FreeAmalgam Rg), A ≤ Z Rg z ∧ Z Rg (p.walk.getVert 3) ≤ A ∧
      A.relIndex (Z Rg z) ≤ 2 ∧
      ⁅Z Rg (alpha Rg),A⁆ = ⁅Z Rg (alpha Rg),Z Rg z⁆ ∧
      ∃ d t, ∃ x ∈ Ltilde Rg (alpha Rg),
        act Rg x (p.walk.getVert 2) = d ∧ act Rg x (p.walk.getVert 1) = t ∧
        Adjacent Rg (alpha Rg) t ∧ Adjacent Rg d t ∧
        edgeOffenderJoin (alpha Rg) t ⊔ A = stabilizer Rg (alpha Rg) ∧
        (Z Rg (p.walk.getVert 1) ⊓ centralizer
          (edgeOffenderJoin (alpha Rg) t : Set (FreeAmalgam Rg)) ≤
          centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) ∧
        Q Rg t ⊔ A = stabilizer Rg (alpha Rg) ∧
        Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
        ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
          q.walk.getVert 1 = t ∧
          (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
          ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),A⁆ ≤ Z Rg (alpha Rg) ∧
          A ≤ normalizer
            (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg (alpha Rg) :
              Subgroup (FreeAmalgam Rg)) : Set _) ∧
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
          4 ≤ (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) ∧
          Q Rg d ≤ edgeOffenderJoin (alpha Rg) t ∧
          ⁅Z Rg d,Z Rg (p.walk.getVert 2)⁆ ≤ fixedCore Rg (alpha Rg) ∧
          (edgeOffenderJoin d t ≠ edgeOffenderJoin (alpha Rg) t →
            ⁅localZSpan Rg d (alpha Rg),Q Rg (alpha Rg)⁆ =
              ⁅Z Rg d,Z Rg (p.walk.getVert 2)⁆ ∧
            stabilizer Rg (alpha Rg) ≤ normalizer
              ((⁅Z Rg d,Z Rg (p.walk.getVert 2)⁆ : Subgroup (FreeAmalgam Rg)) : Set _)) := by
  obtain ⟨A,hAZ,hattach,hi,hcomm,d,t,x,hx,hxd,hxt,hat,hdt,hJgen,hfix,hgen,hgenZ,
    q,hqt,hover,hbound,hnorm,hstrict,hlarge⟩ :=
    borel_four_large_backward_large h e hz hk u hR p hp
  have hqa : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by decide)
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hab : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcore := borel_four_large_midpoint_core_le_mover h e hz hk u hR p hp
  have hcore' := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hcore
  rw [←Q_act,←remaining_edge_join_act h e hz hk u (Or.inr hR) rfl hab x,
    hxd,hxt,show act Rg x (alpha Rg) = alpha Rg from Ltilde_le_stabilizer _ hx] at hcore'
  have hf := borel_four_large_selected_fixed h e hz hk u hR q hlarge
    (by rwa [hqa,hqt]) A (by rwa [hqa,hqt])
    ((four_midpoint_line_centralizes_endpoint h e hz hk u hR q p rfl).trans (centralizer_le hAZ))
  rw [hqa,hqt] at hf
  exact ⟨A,hAZ,hattach,hi,hcomm,d,t,x,hx,hxd,hxt,hat,hdt,hJgen,hfix,hgen,hgenZ,
    q,hqt,hover,hbound,hnorm,hstrict,hlarge,hcore',hf⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
