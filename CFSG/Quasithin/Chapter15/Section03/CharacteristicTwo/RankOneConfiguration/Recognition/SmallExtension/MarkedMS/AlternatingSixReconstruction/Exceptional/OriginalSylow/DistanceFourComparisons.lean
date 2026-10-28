module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourSlices
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward

/-!
# Strict kernel comparisons at original Borel distance four

Let a small critical pair c--w run through a neighbor d of a, and suppose
its full kernel joined to Z_a is normalized by an actor A generating G_a
with Q_d. A strict Baumann slice excludes residual normalization of that
join: its index over Z_a divides eight, so residual control would put the
whole kernel in the slice and bound its seed index by two. Consequently
Q_a lies in the opposite proper Thompson mover. The critical commutator
lies in X_a but cannot be central in the whole G_a.

For a large forward image, apply this comparison to the actual adjusted
seed and backward selector. A small backward image forces the two movers
to be distinct and excludes central generation of omega at every component
vertex. The actor still contains the full last-edge attachment and preserves
the entire critical commutator; normalization by the full endpoint seed
is not assumed on the order-thirty-two cover.

If no large critical image occurs, the initial compatible strict slice and
two normalized backward selections construct the strict small-kernel
configuration with all transporters and generation premises discharged.
This gives the actual midpoint-core and noncentral-line comparisons in
both image branches. The remaining MS93 (5.12)(2)--(3) exclusion of these
configurations, CoreExhaustion and whole-block reconstruction are still
required. Both full covers and the cubic kernel E with odd E/Q are retained.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(c), (5.12)(2)--(3), printed pp.915--917,925--927;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open CFSG.Quasithin.ChapterB.Offenders.Six
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
include h e hz hk in
/-- A strict small critical kernel excludes residual generation by its
normalizing actor and opposite mover. Its critical line is in midpoint omega
and is not fixed by the whole midpoint stabilizer. -/
theorem borel_strict_small_kernel_actor_obstruction
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c d w : Vertex Rg} (ha : color Rg a = false)
    (p : CriticalPath Rg (sourceGeometry h) c w)
    (hp : (Q Rg w).relIndex (Z Rg c) < 4)
    (hfirst : p.walk.getVert 1 = d)
    (had : Adjacent Rg a d) (hcd : Adjacent Rg c d)
    (A : Subgroup (FreeAmalgam Rg))
    (hgen : Q Rg d ⊔ A = stabilizer Rg a)
    (hstrict : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c))
    (hn : A ≤ normalizer (((Z Rg c ⊓ Q Rg w) ⊔ Z Rg a :
      Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))) :
    (¬ Ltilde Rg a ≤ edgeOffenderJoin c d ⊔ A) ∧
      Q Rg a ≤ edgeOffenderJoin c d ∧ ⁅Z Rg c,Z Rg w⁆ ≤ X Rg a ∧
      ¬ ⁅Z Rg c,Z Rg w⁆ ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
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
  have hJdata := borel_small_mover_normalizes_critical_kernel h e hz hk u hR p hp
  rw [hfirst] at hJdata
  obtain ⟨J,_,hJ,_,hJT,_⟩ := borel_edge_maximal_offenders h e hz hk u hR p.start_color hcd
  have hJN : edgeOffenderJoin c d ≤ normalizer (N : Set (FreeAmalgam Rg)) :=
    (le_inf hJdata.2 (((hJ.le.trans hJT).trans
      (show Q Rg d ≤ stabilizer Rg a from
        fun _ hx => hx.2 _ (adjacent_symm Rg had))).trans (Z_normalized Rg a))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hnotL : ¬ Ltilde Rg a ≤ edgeOffenderJoin c d ⊔ A := by
    intro hL
    exact hnot (le_sup_left.trans (terminal_residual_small_radius_le_slice h e hz hk ha N
      hNV (hL.trans (sup_le hJN hn)) hsmall))
  have hQa : Q Rg a ≤ edgeOffenderJoin c d := by
    by_contra hbad
    have hL := (borel_opposite_generation_of_core_not_le h e hz hk u hR ha p.start_color
      had hcd A hgen hbad).2
    exact hnotL hL
  have hHQ : ⁅Z Rg c,Z Rg w⁆ ≤ Q Rg a :=
    ((critical_seed_commutator_le h p).trans hcv).trans ((sourceGeometry h).V_le_Q hb2 a ha)
  have hHC : ⁅Z Rg c,Z Rg w⁆ ≤ centralizer (Q Rg a : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (hQa.trans hJdata.1)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c p.start_color
  refine ⟨hnotL,hQa,?_,?_⟩
  · intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hHQ hx,
      elemPow_eq_one_of_isElementaryAbelian x ((critical_seed_commutator_le h p) hx),hHC hx⟩
  · intro hcentral
    have hTGc : Q Rg d ≤ stabilizer Rg c :=
      fun _ hx => hx.2 _ (adjacent_symm Rg hcd)
    have hTGa : Q Rg d ≤ stabilizer Rg a :=
      fun _ hx => hx.2 _ (adjacent_symm Rg had)
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
/-- The actual large-image adjusted selector retains the strict slice.
A small backward image excludes equal movers and central generation of
omega, while preserving the full attachment and critical commutator. -/
theorem borel_four_large_backward_comparison
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
          ((Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4 →
            (¬ Ltilde Rg (alpha Rg) ≤ edgeOffenderJoin d t ⊔ A) ∧
            edgeOffenderJoin (alpha Rg) t ≠ edgeOffenderJoin d t ∧
            Q Rg (alpha Rg) ≤ edgeOffenderJoin d t ∧
            ⁅Z Rg d,Z Rg (p.walk.getVert 2)⁆ ≤ X Rg (alpha Rg) ∧
            (¬ ⁅Z Rg d,Z Rg (p.walk.getVert 2)⁆ ≤
              centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))) ∧
            ∀ v : Vertex Rg, color Rg v = false →
              X Rg v ≠ U Rg v ⊔
                (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg)))) := by
  obtain ⟨A,hAZ,hattach,hi,hcomm,d,t,x,hx,hxd,hxt,hat,hdt,hJgen,hfix,hgen,hgenZ,
    q,hqt,hover,hbound,hnorm⟩ :=
    borel_four_large_adjusted_backward_selection h e hz hk u hR p hp
  have hstrict := large_remaining_four_forward_slice_strict_at h e hz hk
    (borel_distance_eq_four h e hz hk u hR) u (Or.inr hR) p hp
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (geometry := sourceGeometry h)
        (distance_gt_two h e hz hk) (alpha Rg) rfl
        ((stabilizer Rg (alpha Rg)).inv_mem (Ltilde_le_stabilizer _ hx)))
  have hid : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) := by
    rw [←hxd,U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hstrict
  refine ⟨A,hAZ,hattach,hi,hcomm,d,t,x,hx,hxd,hxt,hat,hdt,hJgen,hfix,hgen,hgenZ,
    q,hqt,hover,hbound,hnorm,hid,?_⟩
  intro hq
  have hc := borel_strict_small_kernel_actor_obstruction h e hz hk u hR rfl q hq hqt
    hat hdt A hgen hid hnorm
  have hne : edgeOffenderJoin (alpha Rg) t ≠ edgeOffenderJoin d t := by
    intro he
    apply hc.1
    rw [←he,hJgen]
    exact Ltilde_le_stabilizer _
  refine ⟨hc.1,hne,hc.2.1,hc.2.2.1,hc.2.2.2,?_⟩
  intro v hv hs
  exact borel_opposite_containing_core_nonsplit h e hz hk u hR rfl q.start_color
    hat hdt hne hc.2.1 (omega_generation_transport hv rfl hs)

include h e hz hk in
/-- If a large image does not occur, the initial strict slice and two
normalized selections give a small critical line in the midpoint omega
subgroup which is not central in its whole stabilizer. All actors and
transporters belong to the original graph. -/
theorem borel_four_terminal_core_comparison
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    (∃ a z : Vertex Rg, ∃ _p : CriticalPath Rg (sourceGeometry h) a z,
      4 ≤ (Q Rg z).relIndex (Z Rg a)) ∨
    ∃ a z y d t : Vertex Rg,
      ∃ p : CriticalPath Rg (sourceGeometry h) d z,
      ∃ r : CriticalPath Rg (sourceGeometry h) a y,
        p.walk.getVert 1 = t ∧ p.walk.getVert 2 = a ∧
        p.walk.getVert 3 = r.walk.getVert 1 ∧ r.walk.getVert 2 = z ∧
        (Q Rg z).relIndex (Z Rg d) = 2 ∧
        (Q Rg y).relIndex (Z Rg a) = 2 ∧
        Adjacent Rg a t ∧ Adjacent Rg d t ∧
        2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg d) ∧
        ∃ x ∈ Ltilde Rg a, act Rg x z = d ∧
          act Rg x (r.walk.getVert 1) = t ∧
          Q Rg t ⊔ Z Rg y = stabilizer Rg a ∧
          (Z Rg (r.walk.getVert 1) ⊓ centralizer
            (edgeOffenderJoin a t : Set (FreeAmalgam Rg)) ≤
            centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) ∧
          (X Rg y ≤ normalizer (((Z Rg d ⊓ Q Rg z) ⊔ Z Rg a :
            Subgroup (FreeAmalgam Rg)) : Set _)) ∧
          (¬ Ltilde Rg a ≤ edgeOffenderJoin d t ⊔ Z Rg y) ∧
          Q Rg a ≤ edgeOffenderJoin d t ∧
          ⁅Z Rg d,Z Rg z⁆ ≤ X Rg a ∧
          ¬ ⁅Z Rg d,Z Rg z⁆ ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
  by_cases hlarge : ∃ a z : Vertex Rg, ∃ _p : CriticalPath Rg (sourceGeometry h) a z,
      4 ≤ (Q Rg z).relIndex (Z Rg a)
  · exact Or.inl hlarge
  have small {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
      (Q Rg z).relIndex (Z Rg a) < 4 := by
    by_contra! hh
    exact hlarge ⟨a,z,p,hh⟩
  have hb := borel_distance_eq_four h e hz hk u hR
  have hb2 := distance_gt_two h e hz hk
  obtain ⟨a,z,y,p,r,hrz,hgen,hfixed,hstrict⟩ :=
    borel_four_initial_compatible_strict_backward h e hz hk u hR
  obtain ⟨d,t,x,hx,hxd,hxt,hat,hdt,hgen',hfixed',q,hqt,hover,hnorm⟩ :=
    borel_four_normalized_backward_selection h e hz hk u hR p r hrz hgen (small p) hfixed
  have hqa : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by decide)
  have hq3 : q.walk.getVert 3 = p.walk.getVert 1 := hover 1 (by decide)
  have hxG := Ltilde_le_stabilizer a hx
  have hUa : (U Rg a).map (MulAut.conj x⁻¹).toMonoidHom = U Rg a := by
    rw [←U_act,show act Rg x a = a from hxG]
  have hi : 2 < (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg a) := by
    rw [←hxd,Escape.PairingControl.FirstPairing.B_act (geometry := sourceGeometry h)
      hb2 x (p.walk.getVert 2) r.start_color,←hUa,
      relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hstrict
  have next := borel_four_normalized_backward_selection h e hz hk u hR (y := z) q
  rw [hqa] at next
  obtain ⟨d',t',x',hx',hxd',hxt',hat',hdt',hgen'',hfixed'',s,hst,hover',hnorm'⟩ :=
    next p rfl (by simpa only [hqt] using hgen') (small q)
      (by simpa only [hq3,hqt] using hfixed')
  have hsa : s.walk.getVert 2 = d := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover' 0 (by decide)
  have hs3 : s.walk.getVert 3 = q.walk.getVert 1 := hover' 1 (by decide)
  have hB : (B Rg d ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj x'⁻¹).toMonoidHom = B Rg d ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (geometry := sourceGeometry h)
        hb2 d q.start_color ((stabilizer Rg d).inv_mem (Ltilde_le_stabilizer _ hx')))
  have hi' : 2 < (B Rg d ((sourceGeometry h).Z_normal _)).relIndex (U Rg d') := by
    rw [←hxd',U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj x'⁻¹).injective]
    exact hi
  have hZX : Z Rg (p.walk.getVert 2) ≤ X Rg (p.walk.getVert 2) :=
    (sourceGeometry h).omega_bound _ q.end_color (by
      rw [(sourceGeometry h).distance_constant _ q.end_color]
      exact sourceDistance_pos h)
  have hc := borel_strict_small_kernel_actor_obstruction h e hz hk u hR q.start_color
    s (small s) hst hat' hdt' (Z Rg (p.walk.getVert 2)) hgen'' hi' (hZX.trans hnorm')
  exact Or.inr ⟨d,a,p.walk.getVert 2,d',t',s,q,hst,hsa,hs3,hqa,
    (small_critical_indices h e hz hk s (small s)).1,
    (small_critical_indices h e hz hk q (small q)).1,hat',hdt',hi',x',hx',hxd',hxt',
    hgen'',hfixed'',hnorm',hc.1,hc.2.1,hc.2.2.1,hc.2.2.2⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
