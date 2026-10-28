module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourComparisons
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardRigidity

import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.WholeCoreMovement

/-!
# Excluding strict small critical kernels at Borel distance four

Let c--d--a--b--w be a small critical path. Suppose an actor A generates
G_a with Q_d, centralizes the critical line D = [Z_c,Z_w], and normalizes
(Z_c ∩ Q_w) Z_a. A strict Baumann slice forces Q_a into the proper mover
at c and makes D noncentral in G_a. Consequently Q_d moves D. Its two
conjugate critical kernels generate the full Z_c, and the checked
conjugate-kernel argument gives
[Z_c,Q_a] = D [Z_c ∩ Q_w,Q_a].

Both factors are normalized by A. The entire movement is thus G_a-invariant,
lies in X_a, and has order dividing eight on either full cover. The A6
residual fixes it; a transported small critical pair upgrades residual
fixedness in X_a to full-stabilizer fixedness. This contradicts the
noncentrality of D. The edge movement hypothesis is essential to the
conjugate-kernel argument and is derived here from the same generating actor.

The actual compatible strict configuration excludes the all-small branch.
There is therefore a large critical image at the original base vertex.
For the adjusted large-image selection, the full attachment and entire
critical commutator are retained, and its backward critical image is also
large. The remaining large-image exclusion in MS93 (5.12)(2), followed by
CoreExhaustion and the five whole-block clauses, is still required.
All groups, quotient maps and transporters are those of the original graph;
the cubic kernel E and its odd quotient E/Q are unchanged.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)--(5.6), (5.12)(2)--(3), printed pp.915--918,925--927;
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
private theorem small_pair_omega_residual_fixed_at
    {c w a : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) c w)
    (hp : (Q Rg w).relIndex (Z Rg c) < 4) (ha : color Rg a = false) :
    X Rg a ⊓ centralizer (Ltilde Rg a : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
  obtain ⟨x,hx⟩ := exists_mVertex_of_color Rg p.start_color
  obtain ⟨y,hy⟩ := exists_mVertex_of_color Rg ha
  let g := x⁻¹*y
  have he : act Rg g c = a := by
    rw [hx,hy]
    simp only [g,act_mVertex,mul_inv_cancel_left]
  have hs : (Q Rg (act Rg g w)).relIndex (Z Rg (act Rg g c)) < 4 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hp
  have hh := small_critical_omega_residual_fixed h e hz hk (p.act g) hs
  rwa [he] at hh

include h e hz hk in
/-- A strict small kernel normalized by the generating actor cannot occur
when that actor centralizes the same critical line. The whole seed/core
movement, including both full covers, supplies the contradiction. -/
theorem borel_strict_small_actor_false
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c d w : Vertex Rg} (ha : color Rg a = false)
    (p : CriticalPath Rg (sourceGeometry h) c w)
    (hp : (Q Rg w).relIndex (Z Rg c) < 4)
    (hfirst : p.walk.getVert 1 = d) (hmid : p.walk.getVert 2 = a)
    (had : Adjacent Rg a d) (hcd : Adjacent Rg c d)
    (A : Subgroup (FreeAmalgam Rg))
    (hgen : Q Rg d ⊔ A = stabilizer Rg a)
    (hstrict : 2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c))
    (hn : A ≤ normalizer (((Z Rg c ⊓ Q Rg w) ⊔ Z Rg a :
      Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)))
    (hDA : ⁅Z Rg c,Z Rg w⁆ ≤ centralizer (A : Set (FreeAmalgam Rg))) : False := by
  let D := ⁅Z Rg c,Z Rg w⁆
  let K := Z Rg c ⊓ Q Rg w
  let H := ⁅Z Rg c,Q Rg a⁆
  let F := ⁅K,Q Rg a⁆
  have hb := borel_distance_eq_four h e hz hk u hR
  have hb2 := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hc := borel_strict_small_kernel_actor_obstruction h e hz hk u hR ha
    p hp hfirst had hcd A hgen hstrict hn
  have hcore := hc.2.1
  have hDnon : ¬ D ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := hc.2.2.2
  have hDmove : ¬ Q Rg d ≤ centralizer (D : Set (FreeAmalgam Rg)) := by
    intro hh
    apply hDnon
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact sup_le hh (le_centralizer_iff.mp hDA)
  have hwa : (cosetGraph Rg).dist w a = 2 := by
    rw [←hmid,SimpleGraph.dist_comm,p.dist_end,hl]
  have hZwQa : Z Rg w ≤ Q Rg a := by
    apply Z_le_Q_of_dist_lt Rg w ((sourceGeometry h).exists_critical w p.end_color)
    rw [hwa,(sourceGeometry h).distance_constant _ p.end_color]
    exact hb2
  obtain ⟨J,_,hJ,_,hJT,_,_,hfix,hquad⟩ :=
    borel_edge_maximal_offenders h e hz hk u hR p.start_color hcd
  have hQJ : Q Rg a ≤ J := hcore.trans hJ.le
  have hdGc : Q Rg d ≤ stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hcd)
  have hdGa : Q Rg d ≤ stabilizer Rg a := fun _ hx => hx.2 _ (adjacent_symm Rg had)
  have hcomm : H = ⁅U Rg c,Q Rg a⁆ := by
    have hh := full_fixed_seed_edge_commutator h e hz p.start_color hcd
      (⊥ : Subgroup (FreeAmalgam Rg)) bot_le (Q Rg a) (hQJ.trans hJT)
    have hbot : centralizer ((⊥ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) = ⊤ := by
      apply top_unique
      intro x _ y hy
      rw [mem_bot.mp hy,mul_one,one_mul]
    simpa only [hbot,inf_top_eq] using hh
  have hHU : H ≤ U Rg c := by
    rw [hcomm]
    exact le_normalizer_iff_commutator_le_left.mp
      ((hQJ.trans hJT).trans (hdGc.trans (U_normalized c)))
  have hHQ : H ≤ Q Rg a := (hHU.trans (DistanceEight.U_le_Z Rg c)).trans
    ((terminal_neighbor_seed_radius had hcd).trans ((sourceGeometry h).V_le_Q hb2 a ha))
  have hHJ : H ≤ centralizer (J : Set (FreeAmalgam Rg)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply le_bot_iff.mp
    rw [hcomm]
    exact (commutator_mono (commutator_mono le_rfl hQJ) le_rfl).trans_eq hquad
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c p.start_color
  let : IsElementaryAbelian 2 H := IsElementaryAbelian.of_le (hHU.trans (DistanceEight.U_le_Z Rg c))
  have hHX : H ≤ X Rg a := by
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hHQ hx,elemPow_eq_one_of_isElementaryAbelian x hx,
      (hHJ.trans (centralizer_le hQJ)) hx⟩
  have hTN : Q Rg d ≤ normalizer (H : Set (FreeAmalgam Rg)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅Z Rg c,Q Rg a⁆ : Subgroup (FreeAmalgam Rg)).map _ = _
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized Rg c (hdGc hx)),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg a (hdGa hx))]
  have hDH : D ≤ H := commutator_mono le_rfl hZwQa
  let := finite_Z Rg c
  have hsmall : Nat.card H ∣ 8 := by
    let C := U Rg c ⊓ centralizer (J : Set (FreeAmalgam Rg))
    have hi : C.relIndex (U Rg c) = 4 := by
      rw [show C = U Rg c ⊓ centralizer (J : Set (FreeAmalgam Rg)) from rfl,inf_relIndex_left]
      exact hfix
    have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam Rg)) C (U Rg c) bot_le inf_le_left
    simp only [relIndex_bot_left,hi] at hm
    have hc : Nat.card C ∣ 8 := by
      rcases graph_U_card h e hz hk c p.start_color with hh | hh
      · have he : Nat.card C = 4 := by omega
        rw [he]; decide
      · have he : Nat.card C = 8 := by omega
        rw [he]
    let : Finite C := Finite.of_injective
      (inclusion (inf_le_left.trans (DistanceEight.U_le_Z Rg c))) (inclusion_injective _)
    exact (card_dvd_of_le (le_inf hHU hHJ)).trans hc
  have hKQ : K ≤ Q Rg a :=
    (inf_le_left.trans (terminal_neighbor_seed_radius had hcd)).trans
      ((sourceGeometry h).V_le_Q hb2 a ha)
  have hF : ⁅K ⊔ Z Rg a,Q Rg a⁆ = F := by
    rw [commutator_comm (K ⊔ Z Rg a)]
    change ⁅Q Rg a,K ⊔ Z Rg a⁆ = ⁅K,Q Rg a⁆
    rw [commutator_comm K]
    symm
    exact commutator_eq_of_centralizing_sup (sup_comm _ _)
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a ha))
      (hKQ.trans (Q Rg a).le_normalizer)
  have hAG : A ≤ stabilizer Rg a := le_sup_right.trans hgen.le
  have hFN : A ≤ normalizer (F : Set (FreeAmalgam Rg)) := by
    rw [←hF]
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [map_commutator,mem_normalizer_iff_map_conj_eq.mp (hn hx),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg a (hAG hx))]
  have hcommon := borel_moving_common_kernel h e hz hk u hR p hp (hfirst.symm ▸ hDmove)
  dsimp only at hcommon
  rw [hfirst] at hcommon
  have hd : color Rg d = true := by
    have hh := adjacent_color_ne Rg had
    rw [ha] at hh
    cases he : color Rg d <;> simp_all
  have hTV := hdGc.trans (Z_normalized Rg c)
  have hTQ := hdGa.trans (Q_normalized Rg a)
  obtain ⟨x,hx,hxmove⟩ := SetLike.not_le_iff_exists.mp hDmove
  have hxn : x ∉ normalizer (K : Set (FreeAmalgam Rg)) := by
    intro hn
    have hh : x ∈ stabilizer Rg c ⊓ normalizer (K : Set (FreeAmalgam Rg)) := ⟨hdGc hx,hn⟩
    rw [small_critical_kernel_normalizer_eq_line_centralizer h e hz hk p hp] at hh
    exact hxmove hh.2
  let f := (MulAut.conj x).toMonoidHom
  have hV : (Z Rg c).map f = Z Rg c := mem_normalizer_iff_map_conj_eq.mp (hTV hx)
  have hKi : K.relIndex (Z Rg c) = 2 := by
    rw [show K = Z Rg c ⊓ Q Rg w from rfl,inf_relIndex_left]
    exact (small_critical_indices h e hz hk p hp).1
  have hKgen : K ⊔ K.map f = Z Rg c :=
    (Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelPair.two_hyperplanes
      (Z Rg c) K (K.map f) inf_le_left
      ((map_mono (show K ≤ Z Rg c from inf_le_left)).trans_eq hV) hKi
      (by rw [←hV,relIndex_map_map_of_injective _ _ (MulAut.conj x).injective]; exact hKi)
      (fun he => hxn (mem_normalizer_iff_map_conj_eq.mpr he.symm))).1
  have hKB : K ≤ centralizer (Z Rg w : Set (FreeAmalgam Rg)) :=
    (critical_seed_centralizer_intersection h e p).symm.le.trans inf_le_right
  have hDC : D ⊔ Z Rg d ≤ Z Rg c := sup_le (critical_seed_commutator_le h p)
    (adjacent_Z_le Rg p.start_color hcd)
  have hbound : H ≤ D ⊔ Z Rg d :=
    ((commutator_mono le_rfl hcore).trans hcommon.2.2.2.2.2.2).trans_eq hcommon.2.2.2.1
  have hdecomp : H = D ⊔ F :=
    conjugate_kernel_movement (Z Rg c) K (Q Rg a) (Z Rg w) D (Z Rg d) x
      inf_le_left hZwQa ((hQJ.trans hJT).trans hTV) (hTV hx) (hTQ hx) hKgen hKB rfl
      hDC (le_centralizer_iff.mp (terminal_edge_seed_central hd) hx) hbound
  have hAN : A ≤ normalizer (H : Set (FreeAmalgam Rg)) := by
    rw [hdecomp]
    exact (le_inf ((le_centralizer_iff.mp hDA).trans (Subgroup.centralizer_le_normalizer _)) hFN).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hGN : stabilizer Rg a ≤ normalizer (H : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    exact sup_le hTN hAN
  have hfixed := small_invariant_core_le_fixed h e hz hk ha H hHQ hGN hsmall
  exact hDnon (hDH.trans ((le_inf hHX (hfixed.trans inf_le_right)).trans
    (small_pair_omega_residual_fixed_at h e hz hk p hp ha)))

include h e hz hk in
private theorem four_midpoint_line_centralizes_endpoint
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {c w a y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) c w)
    (r : CriticalPath Rg (sourceGeometry h) a y) (hr : r.walk.getVert 2 = w) :
    ⁅Z Rg c,Z Rg w⁆ ≤ centralizer (Z Rg y : Set (FreeAmalgam Rg)) := by
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : r.walk.length = 4 := r.length_eq_b.trans hb
  have hwy : (cosetGraph Rg).dist w y = 2 := by rw [←hr,r.dist_end,hl]
  have hZ : Z Rg w ≤ Q Rg y := by
    apply Z_le_Q_of_dist_lt Rg w ((sourceGeometry h).exists_critical w p.end_color)
    rw [hwy,(sourceGeometry h).distance_constant _ p.end_color]
    exact distance_gt_two h e hz hk
  have hD : ⁅Z Rg c,Z Rg w⁆ ≤ Z Rg w := by
    rw [commutator_comm]
    exact critical_seed_commutator_le h (CriticalPath.ofPair p.end_color (reverse_pair h e p))
  exact (hD.trans hZ).trans (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg y r.end_color)))

include h e hz hk in
/-- The original distance-four Borel graph has a large critical image.
The all-small branch is excluded by whole neighboring-core invariance. -/
theorem borel_four_exists_large_critical
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    ∃ z : Vertex Rg, ∃ _p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z,
      4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg)) := by
  obtain ⟨a,z,p,hp⟩ : ∃ a z : Vertex Rg,
      ∃ _p : CriticalPath Rg (sourceGeometry h) a z,
        4 ≤ (Q Rg z).relIndex (Z Rg a) := by
    rcases borel_four_terminal_core_comparison h e hz hk u hR with hlarge |
      ⟨a,z,y,d,t,p,r,hp1,hp2,hp3,hr2,hp,hr,hat,hdt,hstrict,x,hx,hxd,hxt,hgen,
        hfixed,hn,hnot,hcore,hDX,hDnon⟩
    · exact hlarge
    · have hZX : Z Rg y ≤ X Rg y := (sourceGeometry h).omega_bound y r.end_color (by
        rw [(sourceGeometry h).distance_constant _ r.end_color]; exact sourceDistance_pos h)
      exact (borel_strict_small_actor_false h e hz hk u hR r.start_color p
        (by rw [hp]; decide) hp1 hp2 hat hdt (Z Rg y) hgen hstrict (hZX.trans hn)
        (four_midpoint_line_centralizes_endpoint h e hz hk u hR p r hr2)).elim
  obtain ⟨x,hx⟩ := exists_mVertex_of_color Rg p.start_color
  have he : act Rg x⁻¹ a = alpha Rg := by
    rw [hx,act_mVertex,mul_inv_cancel]
    rfl
  have hi : 4 ≤ (Q Rg (act Rg x⁻¹ z)).relIndex (Z Rg (act Rg x⁻¹ a)) := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hp
  have hh : ∃ z : Vertex Rg, ∃ _p : CriticalPath Rg (sourceGeometry h) (act Rg x⁻¹ a) z,
      4 ≤ (Q Rg z).relIndex (Z Rg (act Rg x⁻¹ a)) := ⟨act Rg x⁻¹ z,p.act x⁻¹,hi⟩
  rw [he] at hh
  exact hh

include h e hz hk in
/-- The adjusted large-image selector has a large backward image, retaining
its full attachment, critical commutator and residual transporter. -/
theorem borel_four_large_backward_large
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
          4 ≤ (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) := by
  obtain ⟨A,hAZ,hattach,hi,hcomm,d,t,x,hx,hxd,hxt,hat,hdt,hJgen,hfix,hgen,hgenZ,
    q,hqt,hover,hbound,hnorm,hstrict,_⟩ :=
    borel_four_large_backward_comparison h e hz hk u hR p hp
  have hqa : q.walk.getVert 2 = alpha Rg := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by decide)
  have hlarge : 4 ≤ (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) := by
    by_contra! hs
    exact borel_strict_small_actor_false h e hz hk u hR rfl q hs hqt hqa hat hdt A
      hgen hstrict hnorm
      ((four_midpoint_line_centralizes_endpoint h e hz hk u hR q p rfl).trans (centralizer_le hAZ))
  exact ⟨A,hAZ,hattach,hi,hcomm,d,t,x,hx,hxd,hxt,hat,hdt,hJgen,hfix,hgen,hgenZ,
    q,hqt,hover,hbound,hnorm,hstrict,hlarge⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
