module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.ResidualSelectors
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourStabilizers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusPair
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration
/-!
# Backward criticality from trapped-seed normalization

MS93 proves (5.12)(1) before asserting that the selected backward pair is
critical. Here a selected seed wholly contained in the midpoint core is
handled without assuming that criticality. Failed normalization gives a
line on the whole selected seed. Its small movement places the actor in
the proper Thompson mover, which fixes the line. Opposite generation and
the actual residual transporter carry this fixedness to the midpoint.
The same-path full fixed-subgroup comparison then makes the line central,
contradicting the faithful full-cover action at the selected endpoint.

Normalization makes the two-seed span invariant under the starting
stabilizer. Its section has order dividing eight, so the genuine A6 action
puts it in the Baumann slice. Forward eligibility excludes that containment.
This constructs a backward critical path on the chosen edges. The residual
selectors retain their full fixed-subgroup comparison for the next overlap,
and a small backward image yields the existing kernel normalization on
these very choices.

The initial compatible forward path and its full fixed-subgroup comparison
remain explicit. Equal movers, the remaining critical images and the
terminal contradiction still require proof before CoreExhaustion and whole
exceptional reconstruction. Both full moving covers, their central
attachments and the original cubic kernel E with odd E/Q are preserved.
OriginalSylowExceptional supplies the literal c.L,d.S applications.

The internal imports share proved whole-seed and restricted-kernel lemmas
on this original graph; no natural replacement graph is identified with it.
Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)--(5.6), (5.8), (5.12)(1), printed pp.915--920,924--925;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Representation.NormalElementaryQuotient
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
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
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)

include h e hz hk in
private theorem whole_seed_edge_movement_not_central
    {d t : Vertex Rg} (hd : color Rg d = false) (hdt : Adjacent Rg d t)
    (F : Subgroup (FreeAmalgam Rg)) [IsElementaryAbelian 2 F]
    (hFt : F ≤ Q Rg t) (hne : ⁅Z Rg d,F⁆ ≠ ⊥) :
    ¬ ⁅Z Rg d,F⁆ ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) := by
  intro hcent
  have hFG : F ≤ stabilizer Rg d := hFt.trans (fun _ hv => hv.2 _ (adjacent_symm Rg hdt))
  obtain ⟨i,hi,hir,hiQ,_,hiU,_⟩ := graph_cover h e hz hk d hd
  have hmF : (F.comap i).map i = F := map_comap_eq_self (hFG.trans_eq hir.symm)
  have hcentral : ⁅W₀,F.comap i⁆ ≤ center M := by
    intro v hv
    apply mem_center_iff.mpr
    intro m
    apply hi
    simp only [map_mul]
    apply hcent
    · have hh := mem_map_of_mem i hv
      rw [map_commutator,hiU,hmF] at hh
      exact commutator_mono (DistanceEight.U_le_Z Rg d) le_rfl hh
    · rw [←hir]
      exact ⟨m,rfl⟩
  have hcore := map_mono (f := i) (cover_central_commutator_forces_core h e hz hk
    (F.comap i) ((IsElementaryAbelian.isPGroup (p := 2) (G := F)).comap_of_injective i hi) hcentral)
  rw [hmF,hiQ] at hcore
  exact hne (commutator_eq_bot_iff_le_centralizer.mpr
    ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg d hd)).trans
      (centralizer_le hcore)))

include h e hz hk in
/-- The trapped case in the selected distance-four configuration. The new
backward seed need not form a critical pair: it is wholly contained in the
midpoint core. The same transporter, generation and full fixed-subgroup
comparison give normalization on both covers. -/
theorem borel_four_trapped_seed_normalized
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d t y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t)
    (hgen' : Q Rg t ⊔ Z Rg z = stabilizer Rg a)
    (x : FreeAmalgam Rg) (hx : x ∈ Ltilde Rg a)
    (hxd : act Rg x (p.walk.getVert 2) = d)
    (hxt : act Rg x (p.walk.getVert 1) = t)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (htrap : Z Rg d ≤ Q Rg (p.walk.getVert 2))
    (hne : edgeOffenderJoin a (p.walk.getVert 1) ≠
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1))
    (hfixed : Z Rg (p.walk.getVert 3) ⊓ centralizer
        (edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) :
    X Rg z ≤ normalizer ((Z Rg d ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set _) := by
  by_contra hn
  let c := p.walk.getVert 2
  let b := p.walk.getVert 1
  let F := Z Rg z ⊓ Q Rg a
  let H := ⁅Z Rg d,F⁆
  let D := ⁅Z Rg a,Z Rg z⁆
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hrl : r.walk.length = 4 := r.length_eq_b.trans hb
  have hc : color Rg c = false := r.start_color
  have hd : color Rg d = false := by rw [←hxd,action_preserves_color]; exact hc
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hab : Adjacent Rg a b := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hcb : Adjacent Rg c b := adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
    (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hct : Adjacent Rg c (p.walk.getVert 3) :=
    (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 2) (by omega))
  have hzt : Adjacent Rg z (p.walk.getVert 3) := by
    have hh := (cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 3) (by omega))
    change Adjacent Rg (p.walk.getVert 3) (p.walk.getVert 4) at hh
    rw [←hl,SimpleGraph.Walk.getVert_length] at hh
    exact adjacent_symm Rg hh
  have hdV : Z Rg d ≤ V Rg a := terminal_neighbor_seed_radius hat hdt
  have htrap' : Z Rg d ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using htrap
  have hQN : Q Rg a ≤ normalizer (Z Rg d : Set (FreeAmalgam Rg)) :=
    ((Q_le_adjacent_h Rg ht hat).trans
      (fun _ hv => hv.2 _ (adjacent_symm Rg hdt))).trans (Z_normalized Rg d)
  have hsplit := (restricted_omega_generation_or_control h e hz hk p hp
    (Z Rg d) hdV htrap' (inf_le_right.trans hQN)).resolve_right (fun hh => hn hh.2)
  have hgen_all (v : Vertex Rg) (hv : color Rg v = false) :
      X Rg v = U Rg v ⊔ (X Rg v ⊓ centralizer (stabilizer Rg v : Set (FreeAmalgam Rg))) :=
    omega_generation_transport p.end_color hv hsplit
  have hXZ (v : Vertex Rg) (hv : color Rg v = false) : X Rg v = Z Rg v :=
    omega_eq_seed_of_central_generation h v hv (hgen_all v hv)
  have hnZ : ¬ Z Rg z ≤ normalizer ((Z Rg d ⊔ Z Rg a : Subgroup (FreeAmalgam Rg)) : Set _) := by
    rwa [hXZ z p.end_color] at hn
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) d hd
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.of_le inf_le_left
  have hline := restricted_kernel_line h e hz hk u hR p hp (Z Rg d) hdV htrap'
    (inf_le_right.trans hQN) hnZ
  have hHcard : Nat.card H = 2 := hline.1
  have hHne : H ≠ ⊥ := by intro he; rw [he,card_bot] at hHcard; omega
  have halign : H ≤ D ⊔ (U Rg z ⊓ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg))) :=
    restricted_kernel_alignment h e hz hk p hp (Z Rg d) hdV htrap'
      (inf_le_right.trans hQN) hnZ
  have hFt : F ≤ Q Rg t := inf_le_right.trans (Q_le_adjacent_h Rg ht hat)
  have hwhole : H = ⁅U Rg d,F⁆ := full_seed_commutator_eq_moving h e hz hd hdt F hFt
  have hFJ := borel_small_commutator_actor_le_mover h e hz hk u hR hd hdt F hFt
    (by rw [←hwhole]; exact hHcard.le)
  have hHJ : H ≤ centralizer (edgeOffenderJoin d t : Set (FreeAmalgam Rg)) :=
    commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp
      ((commutator_mono (commutator_mono le_rfl hFJ) le_rfl).trans_eq
        (remaining_edge_full_seed_quadratic h e hz hk u (Or.inr hR) hd hdt)))
  have hDZa : D ≤ Z Rg a := critical_seed_commutator_le h p
  have hDZz : D ≤ Z Rg z := by
    dsimp only [D]
    rw [commutator_comm]
    exact critical_seed_commutator_le h (CriticalPath.ofPair p.end_color (reverse_pair h e p))
  have hDZc : D ≤ Z Rg c := by
    rw [←hXZ c hc]
    exact (commutator_mono
      ((Z_le_localZSpan Rg a c).trans (localZSpan_le_V Rg (by rw [p.dist_start (by omega)])))
      ((Z_le_localZSpan Rg z c).trans (localZSpan_le_V Rg (by rw [SimpleGraph.dist_comm,p.dist_end,hl])))).trans
      (radius_bounds_at h e hz hk c hc a z).2.1
  have hDb : D ≤ Z Rg b := by
    rw [←borel_distinct_centrally_generated_seed_intersection h e hz hk u hR
      p.start_color hc hab hcb hne (hgen_all c hc)]
    exact le_inf hDZa hDZc
  have hyQ : Z Rg y ≤ Q Rg z := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ r.end_color)
    have hdist : (cosetGraph Rg).dist z y = 2 := by
      simpa only [hrz,hrl,Nat.reduceSub] using r.dist_end 2
    rw [SimpleGraph.dist_comm,hdist,(sourceGeometry h).distance_constant _ r.end_color]
    exact distance_gt_two h e hz hk
  have hDy : D ≤ centralizer (Z Rg y : Set (FreeAmalgam Rg)) :=
    hDZz.trans ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg z p.end_color)).trans
      (centralizer_le hyQ))
  have hbcol : color Rg b = true := by
    have hh := adjacent_color_ne Rg hab
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hDC : D ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mpr
    rw [←hgen]
    exact sup_le (le_centralizer_iff.mp (hDb.trans (terminal_edge_seed_central hbcol)))
      (le_centralizer_iff.mp hDy)
  have hHright : H ≤ Z Rg (p.walk.getVert 3) := halign.trans (sup_le
    ((le_inf hDZc hDC).trans (seed_center_le_incident_edge h hc hct))
    ((inf_le_inf_right _ (DistanceEight.U_le_Z Rg z)).trans
      (seed_center_le_incident_edge h p.end_color hzt)))
  have hHZz : H ≤ Z Rg z := halign.trans (sup_le hDZz
    (inf_le_left.trans (DistanceEight.U_le_Z Rg z)))
  have hxG := Ltilde_le_stabilizer a hx
  have hJa := remaining_edge_join_act h e hz hk u (Or.inr hR) p.start_color hab x
  have hJc := remaining_edge_join_act h e hz hk u (Or.inr hR) hc hcb x
  rw [show act Rg x a = a from hxG,hxt] at hJa
  rw [hxd,hxt] at hJc
  have hne' : edgeOffenderJoin a t ≠ edgeOffenderJoin d t := by
    intro he
    exact hne ((map_injective (MulAut.conj x⁻¹).injective) (hJa.symm.trans (he.trans hJc)))
  have hcore : ¬ Q Rg a ≤ edgeOffenderJoin d t := fun hh =>
    borel_opposite_containing_core_nonsplit h e hz hk u hR p.start_color hd hat hdt hne' hh
      (hgen_all a p.start_color)
  have hres := (borel_opposite_generation_of_core_not_le h e hz hk u hR
    p.start_color hd hat hdt (Z Rg z) hgen' hcore).2
  have hHL : H ≤ centralizer (Ltilde Rg a : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mpr (hres.trans (sup_le (le_centralizer_iff.mp hHJ)
      (le_centralizer_iff.mp (hHZz.trans (Z Rg z).le_centralizer))))
  have hHJc : H ≤ centralizer (edgeOffenderJoin c b : Set (FreeAmalgam Rg)) := by
    intro v hv j hj
    have hvx : (MulAut.conj x⁻¹) v = v := by
      change x⁻¹*v*(x⁻¹)⁻¹=v
      rw [hHL hv x⁻¹ ((Ltilde Rg a).inv_mem hx),mul_inv_cancel_right]
    have hjd : (MulAut.conj x⁻¹) j ∈ edgeOffenderJoin d t := by
      rw [hJc]
      exact mem_map_of_mem (MulAut.conj x⁻¹).toMonoidHom hj
    apply (MulAut.conj x⁻¹).injective
    simpa only [map_mul,hvx] using hHJ hv ((MulAut.conj x⁻¹) j) hjd
  have hHC : H ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) :=
    (le_inf hHright hHJc).trans hfixed
  have hHd : H ≤ centralizer (stabilizer Rg d : Set (FreeAmalgam Rg)) := by
    have hh := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hHC).trans
      (map_centralizer_le_centralizer_image _ _)
    rw [terminal_fixed_map H (Ltilde Rg a) hHL ((Ltilde Rg a).inv_mem hx)] at hh
    change H ≤ centralizer ((stabilizer Rg c).map (MulAut.conj x⁻¹).toMonoidHom : Set _) at hh
    rwa [←stabilizer_act,hxd] at hh
  exact whole_seed_edge_movement_not_central h e hz hk hd hdt F hFt hHne hHd

include h e hz hk in
/-- In a compatible distinct-mover configuration, the selected backward
seed cannot be trapped. Normalization would make its full two-seed span
invariant and put its moving cover in the Baumann slice, contradicting the
actual forward eligibility. This constructs backward criticality rather
than assuming it. -/
theorem borel_four_compatible_distinct_backward_path
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d t y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t)
    (hgen' : Q Rg t ⊔ Z Rg z = stabilizer Rg a)
    (x : FreeAmalgam Rg) (hx : x ∈ Ltilde Rg a)
    (hxd : act Rg x (p.walk.getVert 2) = d)
    (hxt : act Rg x (p.walk.getVert 1) = t)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hne : edgeOffenderJoin a (p.walk.getVert 1) ≠
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1))
    (hfixed : Z Rg (p.walk.getVert 3) ⊓ centralizer
        (edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) :
    ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
      q.walk.getVert 1 = t ∧ ∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hd : color Rg d = false := by
    rw [←hxd,action_preserves_color]
    exact r.start_color
  have hescape : ¬ Z Rg d ≤ Q Rg (p.walk.getVert 2) := by
    intro htrap
    let N := Z Rg d ⊔ Z Rg a
    have hn := borel_four_trapped_seed_normalized h e hz hk u hR
      p r hrz hgen hat hdt hgen' x hx hxd hxt hp htrap hne hfixed
    have hZX : Z Rg z ≤ X Rg z := (sourceGeometry h).omega_bound z p.end_color (by
      rw [(sourceGeometry h).distance_constant _ p.end_color]; exact sourceDistance_pos h)
    have hTGv (v : Vertex Rg) (hvt : Adjacent Rg v t) : Q Rg t ≤ stabilizer Rg v :=
      fun _ hv => hv.2 _ (adjacent_symm Rg hvt)
    have hTN : Q Rg t ≤ normalizer (N : Set (FreeAmalgam Rg)) :=
      (le_inf ((hTGv d hdt).trans (Z_normalized Rg d))
        ((hTGv a hat).trans (Z_normalized Rg a))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    have hGN : stabilizer Rg a ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
      rw [←hgen']
      exact sup_le hTN (hZX.trans hn)
    have hNV : N ≤ V Rg a := sup_le (terminal_neighbor_seed_radius hat hdt) (Z_le_VBall Rg a 2)
    have ht : color Rg t = true := by
      have hh := adjacent_color_ne Rg hat
      rw [p.start_color] at hh
      exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
    have hZaQ : Z Rg a ≤ Q Rg a := ((sourceGeometry h).omega_bound a p.start_color (by
      rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)).trans (omegaCenter_le _)
    have hZaN : Z Rg a ≤ normalizer (Z Rg d : Set (FreeAmalgam Rg)) :=
      ((hZaQ.trans (Q_le_adjacent_h Rg ht hat)).trans (hTGv d hdt)).trans (Z_normalized Rg d)
    let := finite_Z Rg a
    have hi : (Z Rg a).relIndex N ∣ 8 := by
      change (Z Rg a).relIndex (Z Rg d ⊔ Z Rg a) ∣ 8
      rw [relIndex_sup_of_normalizes (Z Rg d) (Z Rg a) hZaN]
      have hh := relIndex_dvd_of_le_left (Z Rg d) (adjacent_Z_le Rg p.start_color hat)
      rw [borel_full_seed_edge_index h e hz hk u hR hd hdt] at hh
      exact hh
    have hNB := terminal_residual_small_radius_le_slice h e hz hk p.start_color N
      hNV ((Ltilde_le_stabilizer a).trans hGN) hi
    have hUdB : U Rg d ≤ B Rg a ((sourceGeometry h).Z_normal _) :=
      (DistanceEight.U_le_Z Rg d).trans (le_sup_left.trans hNB)
    have hB : (B Rg a ((sourceGeometry h).Z_normal _)).map (MulAut.conj x⁻¹).toMonoidHom =
        B Rg a ((sourceGeometry h).Z_normal _) := mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (distance_gt_two h e hz hk) a p.start_color
        ((stabilizer Rg a).inv_mem (Ltilde_le_stabilizer a hx)))
    rw [←hxd,U_act,←hB] at hUdB
    exact (borel_critical_paths h e hz hk u hR p).2.2.2
      ((map_le_map_iff_of_injective (MulAut.conj x⁻¹).injective).mp hUdB)
  let w : (cosetGraph Rg).Walk d a :=
    .cons ((cosetGraph_adj Rg _ _).mpr hdt)
      (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
  have hw : w.length = 2 := rfl
  have hne' : ¬ Z Rg d ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    simpa only [hl,Nat.reduceSub] using hescape
  have hb2 : 2 ≤ (sourceGeometry h).b Rg := by change 2 ≤ sourceDistance h; omega
  let q := p.prepend_two hb2 hd w hw hne'
  have hq : ∃ q' : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
      q'.walk.getVert 1 = t ∧ ∀ i ≤ 2, q'.walk.getVert (i+2) = p.walk.getVert i := by
    refine ⟨q,?_,?_⟩
    · change (p.prepend_two hb2 hd w hw hne').walk.getVert 1 = t
      rw [p.prepend_two_walk hb2 hd w hw hne']
      simp only [SimpleGraph.Walk.getVert_append,
        hw,show 1<2 from by decide,ite_true,w,SimpleGraph.Walk.getVert_cons_succ,
        SimpleGraph.Walk.getVert_zero]
    · intro i hi
      exact p.prepend_two_overlap _ _ _ _ _ (by omega)
  rw [show p.walk.length-2=2 by omega] at hq
  exact hq

include h e hz hk in
/-- The compatible small-image normalization no longer assumes a backward
critical path. The selected edge data and the same-path full fixed-subgroup
comparison construct it first. -/
theorem borel_four_selected_small_kernel_normalized
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z d t y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hat : Adjacent Rg a t) (hdt : Adjacent Rg d t)
    (hgen' : Q Rg t ⊔ Z Rg z = stabilizer Rg a)
    (x : FreeAmalgam Rg) (hx : x ∈ Ltilde Rg a)
    (hxd : act Rg x (p.walk.getVert 2) = d)
    (hxt : act Rg x (p.walk.getVert 1) = t)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hd : (Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4)
    (hne : edgeOffenderJoin a (p.walk.getVert 1) ≠
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1))
    (hfixed : Z Rg (p.walk.getVert 3) ⊓ centralizer
        (edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) :
    X Rg z ≤ normalizer
      (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
        Subgroup (FreeAmalgam Rg)) : Set _) := by
  obtain ⟨q,hqt,hverts⟩ := borel_four_compatible_distinct_backward_path h e hz hk u hR
    p r hrz hgen hat hdt hgen' x hx hxd hxt hp hne hfixed
  have hqa : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hverts 0 (by decide)
  exact borel_four_compatible_kernel_normalized h e hz hk u hR p q hqa r hrz hgen
    (hqt.symm ▸ hgen') x hx hxd (hxt.trans hqt.symm) hp hd hne hfixed

include h e hz hk in
/-- Construct the backward source choices from the residual selectors.
Their full fixed-subgroup comparison is retained for the next overlapping
step, and a small backward image gives the normalization conclusion on
these very choices. The initial forward comparison remains explicit. -/
theorem borel_four_distinct_backward_selection
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z y : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) y)
    (hrz : r.walk.getVert 2 = z)
    (hgen : Q Rg (p.walk.getVert 1) ⊔ Z Rg y = stabilizer Rg (p.walk.getVert 2))
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (hne : edgeOffenderJoin a (p.walk.getVert 1) ≠
      edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1))
    (hfixed : Z Rg (p.walk.getVert 3) ⊓ centralizer
        (edgeOffenderJoin (p.walk.getVert 2) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ≤
      centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) :
    ∃ d t, ∃ x ∈ Ltilde Rg a,
      act Rg x (p.walk.getVert 2) = d ∧ act Rg x (p.walk.getVert 1) = t ∧
      Adjacent Rg a t ∧ Adjacent Rg d t ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg a ∧
      (Z Rg (p.walk.getVert 1) ⊓ centralizer (edgeOffenderJoin a t : Set (FreeAmalgam Rg)) ≤
        centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert 2),
        q.walk.getVert 1 = t ∧ (∀ i ≤ 2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        ((Q Rg (p.walk.getVert 2)).relIndex (Z Rg d) < 4 →
          X Rg z ≤ normalizer
            (((Z Rg d ⊓ Q Rg (p.walk.getVert 2)) ⊔ Z Rg a :
              Subgroup (FreeAmalgam Rg)) : Set _)) := by
  obtain ⟨t,hat,_,_,x,hx,hxt,_,_,hgen',_,hfix,_,_,_⟩ :=
    borel_small_residual_selectors h e hz hk u hR p hp
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hcb : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  let d := act Rg x (p.walk.getVert 2)
  have hdt : Adjacent Rg d t := by
    rw [←hxt]
    exact (adjacent_act_iff Rg x _ _).mpr hcb
  obtain ⟨q,hqt,hover⟩ := borel_four_compatible_distinct_backward_path h e hz hk u hR
    p r hrz hgen hat hdt hgen' x hx rfl hxt hp hne hfixed
  refine ⟨d,t,x,hx,rfl,hxt,hat,hdt,hgen',hfix,q,hqt,hover,?_⟩
  intro hd
  have hqa : q.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by decide)
  exact borel_four_compatible_kernel_normalized h e hz hk u hR p q hqa r hrz hgen
    (hqt.symm ▸ hgen') x hx rfl (hxt.trans hqt.symm) hp hd hne hfixed

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
