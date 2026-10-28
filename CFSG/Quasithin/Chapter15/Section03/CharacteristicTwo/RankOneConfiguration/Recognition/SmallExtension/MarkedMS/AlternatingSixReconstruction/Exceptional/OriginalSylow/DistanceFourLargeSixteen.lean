module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.ResidualSelectors
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneFourSpans
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourEqual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward

/-!
# Large critical images on the full order-sixteen cover

For a large critical image, the original order-sixteen moving cover controls
the whole restricted radius. The full endpoint seed is the join of that
cover with the last edge seed. The predecessor core centralizes the latter,
so the same control holds for the full seed, including its central attachment.

Consequently every neighboring restricted kernel is normalized by the
endpoint seed. At distance four the existing large-image construction supplies
a generating edge and a backward critical path. Replacing its transporter
by its residual representative preserves both vertices of the incident star.
The new normalization holds on these actual choices, without an assumed
compatible forward path, a mover comparison, or a backward image bound.

These statements concern the original cubic graph, with kernel E and odd
E/Q. The order-sixteen hypothesis concerns its full moving cover, not a
replacement graph. The order-thirty-two branch, full-omega comparison, initial
small-image compatibility and the terminal contradiction remain open.
OriginalSylowExceptional applies the results to the literal c.L,d.S source.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), (5.2)(iii), (5.8) and the normalization step in (5.12),
printed pp.866--867,914--915,919--920,924--925;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
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
/-- On the order-sixteen moving cover, a large critical image controls the
whole endpoint seed on the restricted radius. The last edge seed is
centralized by the whole predecessor core, so its full attachment is retained. -/
theorem large_sixteen_restricted_seed_control
    (hnat : Nat.card (initialMoved L R) = 16)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : 4 ≤ (Q Rg z).relIndex (Z Rg a)) :
    ⁅V Rg a ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),Z Rg z⁆ ≤ Z Rg a := by
  let Y := V Rg a ⊓ Q Rg (p.walk.getVert (p.walk.length-2))
  let t := p.walk.getVert (p.walk.length-1)
  have hb := distance_gt_two h e hz hk
  have ht := terminal_last_edge_inputs h p hb
  have htcol : color Rg t = true := by
    have hh := adjacent_color_ne Rg ht.1
    rw [p.end_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hedge : Z Rg t ≤ centralizer (Y : Set (FreeAmalgam Rg)) :=
    (terminal_edge_seed_central htcol).trans
      (centralizer_le (inf_le_right.trans ht.2.1))
  have hgen := vertex_seed_eq_moving_sup_edge h e hz p.end_color ht.1
  have hZG : Z Rg z ≤ stabilizer Rg a :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      p.critical
  have hUZ : U Rg z ≤ Z Rg z := DistanceEight.U_le_Z Rg z
  have htZ : Z Rg t ≤ Z Rg z := hgen ▸ le_sup_right
  rw [commutator_comm,hgen]
  exact commutator_sup_le_of_relative_normal (stabilizer Rg a)
    (U Rg z) (Z Rg t) Y (Z Rg a) (Z_normalized Rg a)
    (hUZ.trans hZG) (htZ.trans hZG)
    (by rw [commutator_comm]; exact
      critical_radius_moving_commutator_le_Z_of_natural h e hz hk hnat hb p hp)
    ((commutator_eq_bot_iff_le_centralizer.mpr hedge).le.trans bot_le)

include h e hz hk in
/-- Every restricted neighboring kernel is normalized by the whole endpoint
seed in the large-image order-sixteen case. No compatible forward path,
mover comparison, or backward critical-image bound is assumed. -/
theorem large_sixteen_neighbor_kernel_normalized
    (hnat : Nat.card (initialMoved L R) = 16)
    {a z d t : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : 4 ≤ (Q Rg z).relIndex (Z Rg a))
    (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t) :
    ⁅Z Rg d ⊓ Q Rg (p.walk.getVert (p.walk.length-2)),Z Rg z⁆ ≤ Z Rg a ∧
      Z Rg z ≤ normalizer
        (((Z Rg d ⊓ Q Rg (p.walk.getVert (p.walk.length-2))) ⊔ Z Rg a :
          Subgroup (FreeAmalgam Rg)) : Set _) := by
  have hdV := terminal_neighbor_seed_radius hat hdt
  have hm := (commutator_mono (inf_le_inf_right _ hdV) le_rfl).trans
    (large_sixteen_restricted_seed_control h e hz hk hnat p hp)
  exact ⟨hm,normalize_join_of_commutator _ _ _
    (le_normalizer_iff_commutator_le_left.mpr (critical_seed_commutator_le h p)) hm⟩

include h e hz hk in
/-- At the original base vertex, the large-image branch constructs a
generating backward critical path and its actual residual transporter.
For the order-sixteen cover, its full restricted kernel is normalized by
the endpoint seed. The selected span and both strict indices are retained. -/
theorem borel_four_large_sixteen_backward_selection
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (hnat : Nat.card (initialMoved L R) = 16)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    ∃ d t, ∃ x ∈ Ltilde Rg (alpha Rg),
      act Rg x (p.walk.getVert 2) = d ∧ act Rg x (p.walk.getVert 1) = t ∧
      Adjacent Rg (alpha Rg) t ∧ Adjacent Rg d t ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        ⁅Z Rg d ⊓ Q Rg (p.walk.getVert 2),Z Rg z⁆ ≤ Z Rg (alpha Rg) ∧
        (Z Rg z ≤ normalizer
          (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg (alpha Rg) :
            Subgroup (FreeAmalgam Rg)) : Set _)) ∧
        ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
          localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ ∧
        2 < (Q Rg (p.walk.getVert 2)).relIndex
          (localZSpan Rg (p.walk.getVert 2) (alpha Rg)) ∧
        2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (p.walk.getVert 2)) := by
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨hnon,hindex,hslice,t,hat,hgen,g,hg,hgt,q,hqt,_,hover,_⟩ :=
    large_remaining_four_span_configuration h e hz hk hb u (Or.inr hR) p hp
  have hab : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcb : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨x,hx,_,_,_,hxt,hxv⟩ := residual_star_transporter h rfl hab g hg
  have hxd : act Rg x (p.walk.getVert 2) = act Rg g (p.walk.getVert 2) := hxv _ hcb
  have hdt : Adjacent Rg (act Rg g (p.walk.getVert 2)) t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hcb
  have hnorm := large_sixteen_neighbor_kernel_normalized h e hz hk hnat p hp hat hdt
  simp only [hl,Nat.reduceSub] at hnorm
  exact ⟨_,t,x,hx,hxd,hxt.trans hgt,hat,hdt,hgen,q,hqt,hover,
    hnorm.1,hnorm.2,hnon,hindex,hslice⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

