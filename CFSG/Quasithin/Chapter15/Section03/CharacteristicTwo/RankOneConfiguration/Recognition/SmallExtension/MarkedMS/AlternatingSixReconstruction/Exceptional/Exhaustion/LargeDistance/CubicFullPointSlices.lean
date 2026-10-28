module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicLargeClosure

/-!
# Strict cubic slices for both critical image sizes

Above distance four, every critical walk in the full point-core branch has
strict forward and reciprocal Baumann slices. The original critical image
may have either size, and both entire moving covers are retained.

The full-seed line calculation from CubicLargeClosure controls every
conjugate of the shifted span under its line centralizer. Both complete
orbits therefore lie in the old endpoint two-core. The restricted-actor
argument makes the shifted critical indices two. The orbit commutator R₃
has order two and equals the commutator of the full reverse critical kernel
with the old endpoint core. A conjugated seed realizes R₃; pulling its
actor back controls the shifted span modulo its center seed. Slice escape
forces that actor into the center two-core, contradicting the same witness.
Thus no eligible small slice survives. The actual backward extensions
supply eligibility and transport the strict bounds to both ends, in both
orientations, of every original critical walk.

The whole-core and literal C.1.32 applications below retain the genuine
full point-core equality. Radical-image identification, distance four,
R₄/R₆ and MS93 (5.11)--(5.12), natural exhaustion, and final reconstruction
of both outcomes remain open. The argument retains the odd covering kernel
and does not require an additional second-local centrality assertion for R₃.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), pp.866--867,
and the orbit and strict-slice argument (5.9), pp.920--922.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
namespace SmallSliceShift
variable {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
  (s : SmallSliceShift h p)

include e hz hk in
private theorem full_point_conjugated_span_le_old_endpoint_core
    (hb : 4 < sourceDistance h)
    (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (y : FreeAmalgam Rg) (hy : y ∈ stabilizer Rg (p.walk.getVert 2))
    (hline : (forwardSliceLine h (alpha Rg) (p.walk.getVert 2)).map
      (MulAut.conj y).toMonoidHom = s.line) :
    Z Rg (act Rg y⁻¹ (alpha Rg)) ≤ Q Rg a' ∧
      (localZSpan Rg (p.walk.getVert 2) (alpha Rg)).map
        (MulAut.conj y).toMonoidHom ≤ Q Rg a' := by
  let a := act Rg y⁻¹ (alpha Rg)
  let c := p.walk.getVert 2
  let v := p.walk.getVert (p.walk.length-2)
  let f := (MulAut.conj y).toMonoidHom
  let Y := (localZSpan Rg c (alpha Rg)).map f
  let T := (forwardSliceKernel h (alpha Rg) c).map f
  have hb2 : 2 < sourceDistance h := by omega
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have ha : color Rg a = false := action_preserves_color Rg y⁻¹ (alpha Rg)
  have hc : color Rg c = false := s.path.start_color
  have hv : color Rg v = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := sourceDistance_even h
    rw [Nat.even_iff] at he ⊢
    omega
  have hfix : act Rg y⁻¹ c = c := (stabilizer Rg c).inv_mem hy
  have hac : (cosetGraph Rg).dist a c = 2 := by
    change (cosetGraph Rg).dist (act Rg y⁻¹ (alpha Rg)) c = 2
    rw [←hfix,dist_act]
    exact p.dist_start (by omega)
  have hcv : (cosetGraph Rg).dist c v ≤ p.walk.length-4 := by
    have hh := SimpleGraph.dist_le ((p.walk.drop 2).take (p.walk.length-4))
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
      inf_eq_left.mpr (by omega : p.walk.length-4 ≤ p.walk.length-2),
      SimpleGraph.Walk.drop_getVert,
      show 2+(p.walk.length-4)=p.walk.length-2 by omega] at hh
    exact hh
  have hav : (cosetGraph Rg).dist a v ≤ sourceDistance h-2 := by
    have hh := (cosetGraph_connected Rg).dist_triangle (u := a) (v := c) (w := v)
    omega
  have hae : (cosetGraph Rg).dist a a' ≤ sourceDistance h := by
    have hh := (cosetGraph_connected Rg).dist_triangle (u := a) (v := c) (w := a')
    have hce : (cosetGraph Rg).dist c a' = p.walk.length-2 := p.dist_end 2
    omega
  have hYV : Y ≤ V Rg a := by
    have hh : localZSpan Rg c (alpha Rg) ≤ V Rg (alpha Rg) :=
      localZSpan_le_V Rg (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
    change Y ≤ V Rg (act Rg y⁻¹ (alpha Rg))
    rw [V_act,inv_inv]
    exact map_mono hh
  have hYQ := hYV.trans ((sourceGeometry h).V_le_Q hb2 a ha)
  have hYtwo : IsPGroup 2 Y :=
    (Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le a ha).to_le hYQ
  have hYN : stabilizer Rg a ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [stabilizer_act,inv_inv]
    exact (map_mono (localZSpan_normalized Rg c (alpha Rg))).trans
      (le_normalizer_map f)
  have hB := Escape.PairingControl.FirstPairing.B_act
    (geometry := sourceGeometry h) hb2 y⁻¹ (alpha Rg) rfl
  rw [inv_inv] at hB
  have hYB : ¬ Y ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
    intro hh
    rw [hB] at hh
    have hh' := (map_le_map_iff_of_injective (MulAut.conj y).injective).mp hh
    exact heligible ((DistanceEight.U_le_Z Rg c).trans ((Z_le_localZSpan Rg c _).trans hh'))
  have hT : T = forwardSliceKernel h a c := by
    have hU : (U Rg c).map f = U Rg c :=
      mem_normalizer_iff_map_conj_eq.mp (U_normalized c hy)
    have hUB : (U Rg c ⊓ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map f =
        U Rg c ⊓ B Rg a ((sourceGeometry h).Z_normal _) := by
      rw [map_inf _ _ f (MulAut.conj y).injective,hU,←hB]
    have hm := map_inf_centralizer_of_injective f (MulAut.conj y).injective
      (Q Rg (alpha Rg)) (U Rg c ⊓ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    have hQ : (Q Rg (alpha Rg)).map f = Q Rg a := by
      simpa only [inv_inv] using (Q_act Rg y⁻¹ (alpha Rg)).symm
    rw [hUB,hQ] at hm
    simpa only [forwardSliceKernel,Q_act,inv_inv,coe_inf,Set.inf_eq_inter,T,f] using hm.symm
  have hcomm : ⁅Y,T⁆ = s.line := by
    have hh := congrArg (Subgroup.map f)
      (full_point_selected_span_forward_commutator h e hz hk hb2 p u hfull hslice).1
    rw [map_commutator] at hh
    exact hh.trans hline
  have hvQc : Z Rg v ≤ Q Rg c := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hv)
    rw [(sourceGeometry h).distance_constant _ hv,SimpleGraph.dist_comm]
    change (cosetGraph Rg).dist c v < sourceDistance h
    omega
  have heQc : Z Rg a' ≤ Q Rg c := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ p.end_color)
    rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-2 < sourceDistance h
    omega
  have hvQa : Z Rg v ≤ Q Rg a := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hv)
    rw [(sourceGeometry h).distance_constant _ hv,SimpleGraph.dist_comm]
    change (cosetGraph Rg).dist a v < sourceDistance h
    omega
  have hQcC : Q Rg c ≤ centralizer
      (U Rg c ⊓ B Rg a ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg c hc))).trans
      (centralizer_le (inf_le_left.trans (DistanceEight.U_le_Z Rg c)))
  have hinner : Z Rg v ⊔ (Z Rg a' ⊓ Q Rg a) ≤ T := by
    rw [hT]
    exact le_inf (sup_le hvQa inf_le_right)
      ((sup_le hvQc (inf_le_left.trans heQc)).trans hQcC)
  have hez : (cosetGraph Rg).dist a' s.endpoint = 2 := by
    have hh := s.path.dist_end (p.walk.length-2)
    have hlen : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    rw [s.overlap _ (Nat.le_refl _),show p.walk.length-2+2=p.walk.length by omega,
      p.walk.getVert_length,hlen] at hh
    exact hh.trans (by omega)
  have hvz : (cosetGraph Rg).dist v s.endpoint ≤ 4 := by
    have hh := (cosetGraph_connected Rg).dist_triangle (u := v) (v := a') (w := s.endpoint)
    have hve : (cosetGraph Rg).dist v a' = 2 := by
      change (cosetGraph Rg).dist (p.walk.getVert (p.walk.length-2)) a' = 2
      rw [p.dist_end]
      omega
    omega
  have hZz (w : Vertex Rg) (hw : color Rg w = false)
      (hd : (cosetGraph Rg).dist w s.endpoint < sourceDistance h) :
      Z Rg w ≤ centralizer (Z Rg s.endpoint : Set (FreeAmalgam Rg)) := by
    apply le_trans _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg _ s.path.end_color)))
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hw)
    rwa [(sourceGeometry h).distance_constant _ hw]
  have hvC := hZz v hv (lt_of_le_of_lt hvz hb)
  have heC := hZz a' p.end_color (hez.symm ▸ hb2)
  have hcard := (s.full_point_line_facts e hz hk hb2 u hfull hslice).1
  let : Finite s.line := Nat.finite_of_card_ne_zero (by omega)
  have hkill (D : Subgroup (FreeAmalgam Rg)) (hD : D ≤ s.line)
      (hDC : D ≤ centralizer (Z Rg s.endpoint : Set (FreeAmalgam Rg))) : D = ⊥ := by
    by_contra hn
    let : Finite D := Finite.of_injective (inclusion hD) (inclusion_injective _)
    have hp := (one_lt_card_iff_ne_bot D).mpr hn
    have he : D = s.line := eq_of_le_of_card_ge hD (by omega)
    apply s.moves
    change s.line ≤ _
    rwa [he] at hDC
  have hYGv : Y ≤ stabilizer Rg v := by
    apply hYV.trans
    apply (V_le_iff Rg ha _).mpr
    intro w hw hd
    apply Z_le_stabilizer_of_dist_le w ((sourceGeometry h).exists_critical w hw)
    rw [(sourceGeometry h).distance_constant w hw]
    have hh := (cosetGraph_connected Rg).dist_triangle (u := w) (v := a) (w := v)
    change (cosetGraph Rg).dist w v ≤ sourceDistance h
    omega
  have hYv : ⁅Y,Z Rg v⁆ = ⊥ :=
    hkill _ ((commutator_mono le_rfl (le_sup_left.trans hinner)).trans_eq hcomm)
      ((le_normalizer_iff_commutator_le_right.mp (hYGv.trans (Z_normalized Rg v))).trans hvC)
  have hYQv : Y ≤ Q Rg v := two_subgroup_seed_centralizer_le_core h e hz hv Y hYtwo
    (le_inf hYGv (commutator_eq_bot_iff_le_centralizer.mp hYv))
  have hYGe : Y ≤ stabilizer Rg a' := by
    let t := p.walk.getVert (p.walk.length-1)
    have het : Adjacent Rg a' t := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
      rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    have hvt : Adjacent Rg v t := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
      rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have ht : color Rg t = true := by
      have hh := adjacent_color_ne Rg het
      rw [p.end_color] at hh
      cases he : color Rg t <;> simp_all
    exact (hYQv.trans (Q_le_adjacent_h Rg ht hvt)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg het))
  have hYK : ⁅Y,Z Rg a' ⊓ Q Rg a⁆ = ⊥ :=
    hkill _ ((commutator_mono le_rfl (le_sup_right.trans hinner)).trans_eq hcomm)
      (((commutator_mono le_rfl inf_le_left).trans
        (le_normalizer_iff_commutator_le_right.mp (hYGe.trans (Z_normalized Rg a')))).trans heC)
  have heQa : Z Rg a' ≤ Q Rg a := by
    by_contra hn
    have hlo := criticalDistance_le Rg a' ((sourceGeometry h).exists_critical _ p.end_color) hn
    rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm] at hlo
    have hp : CriticalPair Rg a' a ((sourceGeometry h).exists_critical _ p.end_color) := by
      refine ⟨?_,hn⟩
      rw [(sourceGeometry h).distance_constant _ p.end_color,SimpleGraph.dist_comm]
      exact le_antisymm hae hlo
    let q : CriticalPath Rg (sourceGeometry h) a a' := CriticalPath.ofPair ha
      (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e) a' p.end_color
        (by rw [(sourceGeometry h).distance_constant _ p.end_color]; exact sourceDistance_pos h) a ha hp)
    exact hYB (critical_kernel_normal_radius_le_slice h e hz hk hb2 q Y hYV hYN hYGe
      (commutator_eq_bot_iff_le_centralizer.mp hYK))
  have hYe : ⁅Y,Z Rg a'⁆ = ⊥ := by
    simpa only [inf_eq_left.mpr heQa] using hYK
  have hYQe := two_subgroup_seed_centralizer_le_core h e hz p.end_color Y hYtwo
    (le_inf hYGe (commutator_eq_bot_iff_le_centralizer.mp hYe))
  refine ⟨?_,hYQe⟩
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a ha
  apply two_subgroup_seed_centralizer_le_core h e hz p.end_color (Z Rg a)
    (IsElementaryAbelian.isPGroup 2 _)
  refine le_inf ?_ ?_
  · apply Z_le_stabilizer_of_dist_le a ((sourceGeometry h).exists_critical _ ha)
    rwa [(sourceGeometry h).distance_constant _ ha]
  · exact (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a ha)).trans
      (centralizer_le heQa)


include e hz hk in
/-- Both complete centralizer orbits lie in the old endpoint's two-core.
The conjugator ranges over the whole line centralizer, not only its residual. -/
theorem full_point_centralizer_orbits_le_old_endpoint_core
    (hb : 4 < sourceDistance h)
    (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    s.seedOrbit ≤ Q Rg a' ∧ s.spanOrbit ≤ Q Rg a' := by
  have hmap (A : Subgroup (FreeAmalgam Rg)) (x : FreeAmalgam Rg) :
      (A.map (MulAut.conj s.conjugator).toMonoidHom).map (MulAut.conj x).toMonoidHom =
        A.map (MulAut.conj (x*s.conjugator)).toMonoidHom := by
    rw [map_map]
    congr 1
    apply MonoidHom.ext
    intro z
    change x*(s.conjugator*z*s.conjugator⁻¹)*x⁻¹ =
      (x*s.conjugator)*z*(x*s.conjugator)⁻¹
    group
  have hconj (x : s.lineCentralizer) :
      (Z Rg s.centerVertex).map (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom ≤ Q Rg a' ∧
      s.span.map (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom ≤ Q Rg a' := by
    have hxH : s.line.map (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom = s.line :=
      mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _) x.property.2)
    have hxy : (x : FreeAmalgam Rg)*s.conjugator ∈ stabilizer Rg (p.walk.getVert 2) :=
      (stabilizer Rg _).mul_mem x.property.1 (Ltilde_le_stabilizer _ s.residual)
    have hh := s.full_point_conjugated_span_le_old_endpoint_core e hz hk hb u hfull hslice heligible
      ((x : FreeAmalgam Rg)*s.conjugator) hxy (by rw [←hmap]; exact hxH)
    rw [centerVertex,Z_act,inv_inv,hmap,s.span_map,hmap]
    simpa only [Z_act,inv_inv] using hh
  constructor
  · rw [seedOrbit,conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun x => (hconj x).1)
  · rw [spanOrbit,conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun x => (hconj x).2)


include e hz hk in
/-- Both shifted critical images have order two, for either entire cover.
If a shifted image were large, choose the shift using its controlled
restricted actor. Its centralizer orbit would then be a normal radius
subgroup modulo the seed and lie in the forbidden Baumann slice. -/
theorem full_point_shifted_indices
    (hb : 4 < sourceDistance h)
    (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) = 2 ∧
      (Q Rg (p.walk.getVert 2)).relIndex (Z Rg s.endpoint) = 2 := by
  have hb2 : 2 < sourceDistance h := by omega
  apply small_critical_indices h e hz hk s.path
  by_contra hn
  have hlarge : 4 ≤ (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) := by omega
  obtain ⟨A,hAU,hAn,hcontrol⟩ := large_critical_restricted_actor h e hz hk s.path hlarge
  let c := p.walk.getVert 2
  let v := s.path.walk.getVert (s.path.walk.length-2)
  let t := p.walk.getVert 1
  have hc : color Rg c = false := s.path.start_color
  have hAZ : A ≤ Z Rg s.endpoint := hAU.trans (DistanceEight.U_le_Z Rg s.endpoint)
  have hEC : Z Rg s.endpoint ≤ stabilizer Rg c :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) c hc
      (by rw [(sourceGeometry h).distance_constant c hc]; exact sourceDistance_pos h)
      s.path.critical
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) s.endpoint s.path.end_color
  have htwo : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 (Z Rg s.endpoint)).to_le hAZ
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hTG : forwardSliceKernel h (alpha Rg) c ≤ stabilizer Rg c :=
    (inf_le_left.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hHU : forwardSliceLine h (alpha Rg) c ≤ U Rg c :=
    le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))
  have hline := forward_slice_noncentral_line h e hz hk hb2 p hslice heligible
  obtain ⟨g,hg,hgen,hmove⟩ := exists_cover_line_generator_of_actor h e hz hk hc A
    (hAZ.trans hEC) htwo hAn (forwardSliceLine h (alpha Rg) c) hHU
    hline.1 hline.2.2
  let r : SmallSliceShift h p :=
    ⟨s.endpoint,s.path,s.overlap,g,hg,
      le_antisymm (sup_le inf_le_left hEC) (hgen.symm.le.trans (sup_le_sup_left hAZ _)),
      fun hh => hmove (hh.trans (centralizer_le hAZ))⟩
  have hrgen : r.lineCentralizer ⊔ A = stabilizer Rg c := hgen
  have hpre : v = a' := by
    dsimp only [v]
    have hq : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    rw [show s.path.walk.length-2 = p.walk.length-2 by omega,
      s.overlap _ (Nat.le_refl _),show p.walk.length-2+2=p.walk.length by omega,
      p.walk.getVert_length]
  have hDpre : r.seedOrbit ≤ Q Rg v := by
    rw [hpre]
    exact (r.full_point_centralizer_orbits_le_old_endpoint_core e hz hk hb u hfull hslice heligible).1
  have hDe : r.seedOrbit ≤ stabilizer Rg s.endpoint := by
    let t' := s.path.walk.getVert (s.path.walk.length-1)
    have hq : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    have het : Adjacent Rg s.endpoint t' := by
      have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-1) (by omega)
      rw [show s.path.walk.length-1+1=s.path.walk.length by omega,
        s.path.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    have hvt : Adjacent Rg v t' := by
      have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-2) (by omega)
      rw [show s.path.walk.length-2+1=s.path.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have ht' : color Rg t' = true := by
      have hh := adjacent_color_ne Rg het
      rw [s.path.end_color] at hh
      cases he : color Rg t' <;> simp_all
    exact (hDpre.trans (Q_le_adjacent_h Rg ht' hvt)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg het))
  have hDV : r.seedOrbit ≤ V Rg c := (r.seedOrbit_radius_and_escape e hz hb2).1
  have hDA : ⁅r.seedOrbit,A⁆ ≤ Z Rg c :=
    hcontrol r.seedOrbit (hDV.trans ((sourceGeometry h).V_le_Q hb2 c hc)) hDe
  let D := r.seedOrbit ⊔ Z Rg c
  have hVG : V Rg c ≤ stabilizer Rg c := (sourceGeometry h).V_local c hc (by
    rw [(sourceGeometry h).distance_constant c hc]; exact hb2)
  have hDVA : D ≤ V Rg c := sup_le hDV (Z_le_VBall Rg c 2)
  have hZA : ⁅Z Rg c,A⁆ ≤ Z Rg c :=
    le_normalizer_iff_commutator_le_left.mp ((hAZ.trans hEC).trans (Z_normalized Rg c))
  have hcomm : ⁅D,A⁆ ≤ Z Rg c :=
    commutator_sup_le_of_relative_normal (stabilizer Rg c) r.seedOrbit (Z Rg c)
      A (Z Rg c) (Z_normalized Rg c) (hDV.trans hVG)
      (Z_le_stabilizer Rg c) hDA hZA
  have hDN : stabilizer Rg c ≤ normalizer (D : Set (FreeAmalgam Rg)) := by
    rw [←hrgen]
    apply sup_le
    · exact (le_inf r.centralizer_orbits_normalized.1
        (inf_le_left.trans (Z_normalized Rg c))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr (hcomm.trans le_sup_right)
  have hDB := normalized_radius_le_slice_of_controlled_actor h e hz hb2 hc D A
    hDVA hDN (hAZ.trans hEC) htwo hAn hcomm
  exact (r.seedOrbit_radius_and_escape e hz hb2).2 (le_sup_left.trans hDB)


private theorem full_point_shifted_predecessor (hb : 2 < sourceDistance h) :
    s.path.walk.getVert (s.path.walk.length-2) = a' := by
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hq : s.path.walk.length = sourceDistance h := s.path.length_eq_b
  rw [show s.path.walk.length-2 = p.walk.length-2 by omega,
    s.overlap _ (Nat.le_refl _),show p.walk.length-2+2=p.walk.length by omega,
    p.walk.getVert_length]

include e hz hk in
/-- In the small shifted-image branch the entire orbit has exactly an
order-two commutator with A₀. Its vanishing would control the full endpoint
action and contradict the orbit's Baumann-slice escape. -/
private theorem full_point_orbitDisplacement_card_two
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _))
    (hshift : (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) < 4) :
    Nat.card s.orbitDisplacement = 2 := by
  have hb2 : 2 < sourceDistance h := by omega
  have hDpre : s.seedOrbit ≤ Q Rg (s.path.walk.getVert (s.path.walk.length-2)) := by
    rw [s.full_point_shifted_predecessor hb2]
    exact (s.full_point_centralizer_orbits_le_old_endpoint_core e hz hk hb u hfull hslice heligible).1
  have hcard := small_critical_kernel_predecessor_card h e hz hk hb2 u hfull.le s.path hshift
  let K := Z Rg s.endpoint ⊓ Q Rg (p.walk.getVert 2)
  have hN : ⁅K,Q Rg (s.path.walk.getVert (s.path.walk.length-2))⁆ ≤ Z Rg s.endpoint := by
    have hZ := Z_normalized Rg s.endpoint
    have hl : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    let t := s.path.walk.getVert (s.path.walk.length-1)
    have het : Adjacent Rg s.endpoint t := by
      have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-1) (by omega)
      rw [show s.path.walk.length-1+1=s.path.walk.length by omega,
        s.path.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    have hpt : Adjacent Rg (s.path.walk.getVert (s.path.walk.length-2)) t := by
      have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-2) (by omega)
      rw [show s.path.walk.length-2+1=s.path.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have ht : color Rg t = true := by
      have hh := adjacent_color_ne Rg het
      rw [s.path.end_color] at hh
      cases he : color Rg t <;> simp_all
    have hQG : Q Rg (s.path.walk.getVert (s.path.walk.length-2)) ≤
        stabilizer Rg s.endpoint :=
      (Q_le_adjacent_h Rg ht hpt).trans (fun _ hx => hx.2 _ (adjacent_symm Rg het))
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hQG.trans hZ))
  let := finite_Z Rg s.endpoint
  let : Finite (⁅K,Q Rg (s.path.walk.getVert (s.path.walk.length-2))⁆ :
      Subgroup (FreeAmalgam Rg)) := Finite.of_injective (inclusion hN) (inclusion_injective _)
  have hle : s.orbitDisplacement ≤ ⁅K,Q Rg (s.path.walk.getVert (s.path.walk.length-2))⁆ := by
    rw [orbitDisplacement,commutator_comm]
    exact commutator_mono le_rfl hDpre
  let : Finite s.orbitDisplacement := Finite.of_injective (inclusion hle) (inclusion_injective _)
  have hlecard : Nat.card s.orbitDisplacement ≤ 2 := (card_le_of_le hle).trans hcard
  have hne : s.orbitDisplacement ≠ ⊥ := by
    intro he
    have hfix : s.seedOrbit ≤ centralizer (Z Rg s.endpoint ⊓ Q Rg (p.walk.getVert 2) :
        Set (FreeAmalgam Rg)) := commutator_eq_bot_iff_le_centralizer.mp he
    exact s.seedOrbit_endpoint_commutator_not_le e hz hb2
      (small_critical_predecessor_commutator h e hz hk hb2 s.path hshift s.seedOrbit hDpre hfix)
  have hh := (one_lt_card_iff_ne_bot s.orbitDisplacement).mpr hne
  omega


include e hz hk in
/-- R₃ is the commutator of the entire reverse critical kernel with the
old endpoint's two-core, independently of its realization by the seed
orbit. It has order two and centralizes the full old endpoint radius. -/
theorem full_point_orbitDisplacement_full_core
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    s.orbitDisplacement = ⁅s.orbitKernel,Q Rg a'⁆ ∧
      Nat.card s.orbitDisplacement = 2 ∧
      s.orbitDisplacement ≤ Z Rg s.endpoint ⊓
        centralizer (V Rg a' : Set (FreeAmalgam Rg)) := by
  have hb2 : 2 < sourceDistance h := by omega
  have hs : (Q Rg s.endpoint).relIndex (Z Rg (p.walk.getVert 2)) < 4 := by
    rw [(s.full_point_shifted_indices e hz hk hb u hfull hslice heligible).1]
    decide
  have hcard := s.full_point_orbitDisplacement_card_two e hz hk hb u hfull hslice heligible hs
  have hp : s.path.walk.getVert (s.path.walk.length-2) = a' := by
    have hl : p.walk.length = sourceDistance h := p.length_eq_b
    have hq : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    rw [show s.path.walk.length-2 = p.walk.length-2 by omega,
      s.overlap _ (Nat.le_refl _),show p.walk.length-2+2=p.walk.length by omega,
      p.walk.getVert_length]
  have hbound := small_critical_kernel_predecessor_card h e hz hk hb2 u hfull.le s.path hs
  rw [hp] at hbound
  have hQG : Q Rg a' ≤ stabilizer Rg s.endpoint := by
    conv_lhs => rw [←hp]
    let t := s.path.walk.getVert (s.path.walk.length-1)
    have hl : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    have het : Adjacent Rg s.endpoint t := by
      have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-1) (by omega)
      rw [show s.path.walk.length-1+1=s.path.walk.length by omega,
        s.path.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    have hpt : Adjacent Rg (s.path.walk.getVert (s.path.walk.length-2)) t := by
      have hh := s.path.walk.adj_getVert_succ (i := s.path.walk.length-2) (by omega)
      rw [show s.path.walk.length-2+1=s.path.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have ht : color Rg t = true := by
      have hh := adjacent_color_ne Rg het
      rw [s.path.end_color] at hh
      cases he : color Rg t <;> simp_all
    exact (Q_le_adjacent_h Rg ht hpt).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg het))
  have hNZ : ⁅s.orbitKernel,Q Rg a'⁆ ≤ Z Rg s.endpoint :=
    (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hQG.trans (Z_normalized Rg s.endpoint)))
  let := finite_Z Rg s.endpoint
  let : Finite (⁅s.orbitKernel,Q Rg a'⁆ : Subgroup (FreeAmalgam Rg)) :=
    Finite.of_injective (inclusion hNZ) (inclusion_injective _)
  have hle : s.orbitDisplacement ≤ ⁅s.orbitKernel,Q Rg a'⁆ := by
    rw [orbitDisplacement,commutator_comm]
    exact commutator_mono le_rfl
      (s.full_point_centralizer_orbits_le_old_endpoint_core e hz hk hb u hfull hslice heligible).1
  have heq := eq_of_le_of_card_ge hle (hcard.symm ▸ hbound)
  refine ⟨heq,hcard,le_inf (hle.trans hNZ) ?_⟩
  have hdist : (cosetGraph Rg).dist a' s.endpoint = 2 := by
    have hh := s.path.dist_end (s.path.walk.length-2)
    rw [hp] at hh
    have hl : s.path.walk.length = sourceDistance h := s.path.length_eq_b
    exact hh.trans (by omega)
  have hZV : Z Rg s.endpoint ≤ V Rg a' :=
    le_iSup_of_le s.endpoint (le_iSup_of_le (by rw [SimpleGraph.dist_comm]; exact hdist.le) le_rfl)
  exact (hle.trans (commutator_mono (inf_le_left.trans hZV) le_rfl)).trans
    (radius_bounds_at h e hz hk a' p.end_color a' a').1


include e hz hk in
/-- Adjoining the whole shifted span orbit does not enlarge R₃.
The same reverse kernel normalizes both orbits separately. -/
theorem full_point_orbit_kernel_commutator
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    ⁅s.seedOrbit ⊔ s.spanOrbit,s.orbitKernel⁆ = s.orbitDisplacement ∧
      s.orbitKernel ≤ normalizer (s.seedOrbit : Set (FreeAmalgam Rg)) ⊓
        normalizer (s.spanOrbit : Set (FreeAmalgam Rg)) := by
  have ho := s.full_point_centralizer_orbits_le_old_endpoint_core e hz hk hb u hfull hslice heligible
  have hf := s.full_point_orbitDisplacement_full_core e hz hk hb u hfull hslice heligible
  have hKC : s.orbitKernel ≤ s.lineCentralizer :=
    inf_le_right.trans (s.second_core_le_lineCentralizer (by omega))
  refine ⟨le_antisymm ?_ (commutator_mono le_sup_left le_rfl),
    le_inf (hKC.trans s.centralizer_orbits_normalized.1)
      (hKC.trans s.centralizer_orbits_normalized.2.1)⟩
  rw [hf.1,commutator_comm s.orbitKernel]
  exact commutator_mono (sup_le ho.1 ho.2) le_rfl


include s e hz hk in
theorem full_point_small_slice_impossible
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (heligible : ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    False := by
  let c := p.walk.getVert 2
  have hb2 : 2 < sourceDistance h := by omega
  have hcard := (s.full_point_orbitDisplacement_full_core e hz hk hb u hfull hslice heligible).2.1
  obtain ⟨t,ht,hwitness⟩ := s.exists_seed_conjugate_orbitDisplacement hcard
  let f := (MulAut.conj t).toMonoidHom
  let fi := (MulAut.conj t⁻¹).toMonoidHom
  let A := s.orbitKernel.map fi
  have hAf : A.map f = s.orbitKernel := by
    rw [map_map]
    have he : f.comp fi = MonoidHom.id (FreeAmalgam Rg) := by
      apply MonoidHom.ext
      intro x
      change t*(t⁻¹*x*(t⁻¹)⁻¹)*t⁻¹ = x
      group
    rw [he,map_id]
  have hAQ : A ≤ Q Rg c := by
    have hQ := mem_normalizer_iff_map_conj_eq.mp
      ((Q_normalized Rg c) ((stabilizer Rg c).inv_mem ht.1))
    exact (map_mono (show s.orbitKernel ≤ Q Rg c from inf_le_right)).trans_eq hQ
  have hdist : (cosetGraph Rg).dist c s.centerVertex = 2 := by
    have hh := dist_act Rg s.conjugator⁻¹ c (alpha Rg)
    rw [s.fixes_second,SimpleGraph.dist_comm (u := c) (v := alpha Rg)] at hh
    exact hh.trans (p.dist_start (by
      have hl : p.walk.length = sourceDistance h := p.length_eq_b
      omega))
  have hAG : A ≤ stabilizer Rg s.centerVertex := hAQ.trans
    (Q_le_stabilizer_of_dist_le_two c s.centerVertex s.path.start_color
      s.center_color hdist.le)
  have hZA : ⁅Z Rg s.centerVertex,A⁆ ≤ Z Rg s.centerVertex :=
    le_normalizer_iff_commutator_le_left.mp (hAG.trans (Z_normalized Rg _))
  have hZAmap : (⁅Z Rg s.centerVertex,A⁆ : Subgroup (FreeAmalgam Rg)).map f =
      s.orbitDisplacement := by
    rw [map_commutator,hAf]
    exact hwitness
  have hspan : s.span.map f ≤ s.spanOrbit := by
    rw [spanOrbit,conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun x : s.lineCentralizer =>
      s.span.map (MulAut.conj (x : FreeAmalgam Rg)).toMonoidHom) ⟨t,ht⟩
  have hcomm : ⁅s.span,A⁆ ≤ Z Rg s.centerVertex := by
    apply le_trans _ hZA
    apply (map_le_map_iff_of_injective (f := f) (MulAut.conj t).injective).mp
    rw [hZAmap,map_commutator,hAf]
    exact (commutator_mono (hspan.trans le_sup_right) le_rfl).trans_eq
      (s.full_point_orbit_kernel_commutator e hz hk hb u hfull hslice heligible).1
  have hAcore : A ≤ Q Rg s.centerVertex := by
    by_contra hn
    have hAB := normalized_radius_le_slice_of_controlled_actor h e hz hb2
      s.center_color s.span A (localZSpan_le_V Rg hdist.le)
      (localZSpan_normalized Rg _ _) hAG
      ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le c
        s.path.start_color).to_le hAQ) hn hcomm
    exact s.span_not_le_slice hb2 heligible hAB
  have hzero : ⁅Z Rg s.centerVertex,A⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono le_rfl hAcore).trans_eq
      (Z_centralizes_Q Rg s.centerVertex s.center_color))
  rw [hzero,Subgroup.map_bot] at hZAmap
  rw [←hZAmap] at hcard
  simp at hcard

end SmallSliceShift

include e hz hk in
/-- In the full point-core branch, every forward slice above distance four
is strict. The original critical image may have either size. -/
theorem full_point_forward_slice_gt_two
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) := by
  by_contra! hslice
  obtain ⟨s,_,_,_,_,_⟩ := full_point_small_slice_shift_control h e hz hk
    (by omega) u hfull p hslice
  exact s.full_point_small_slice_impossible e hz hk hb u hfull hslice
    (full_point_critical_forward_eligible h e hz hk (by omega) u hfull p)

include e hz hk in
/-- The strict forward-slice estimate on any actual critical walk,
transporting its second vertex and Baumann slice by the same element. -/
theorem full_point_forward_slice_gt_two_at
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a') :
    2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ a) (act Rg g⁻¹ a'),
      p₀.walk.getVert 2 = act Rg g⁻¹ (p.walk.getVert 2) :=
    ⟨p.act g⁻¹,by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hvert⟩ := hpact
  have hB := Escape.PairingControl.FirstPairing.B_act
    (geometry := sourceGeometry h) (by change 2 < sourceDistance h; omega) g⁻¹ a p.start_color
  rw [hbase,inv_inv] at hB
  have hi := full_point_forward_slice_gt_two e hz hk hb u hfull p₀
  rw [hvert,U_act,inv_inv,hB,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective] at hi
  exact hi

include e hz hk in
/-- Every critical walk has both orientations of its initial slice strict.
The reciprocal orientation uses the actual extended reverse prefix. -/
theorem full_point_reciprocal_slices_gt_two
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a') :
    2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert 2)) ∧
      2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg a) := by
  obtain ⟨d,q,_,hq⟩ := full_point_critical_reverse_prefix h e hz hk (by omega) u hfull p
  refine ⟨full_point_forward_slice_gt_two_at e hz hk hb u hfull p,?_⟩
  have hh := full_point_forward_slice_gt_two_at e hz hk hb u hfull q
  rwa [hq] at hh

include e hz hk in
/-- Both end pairs, in both orientations, have strict Baumann slices on
the same original critical walk. This supplies the strict slices used by
the subsequent R₄/R₆ path argument. -/
theorem full_point_four_slices_gt_two
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hfull : (Rg).map (CubicAction.projection h e hz hk) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a') :
    (2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert 2)) ∧
      2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a)) ∧
    (2 < (B Rg a' ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert (p.walk.length-2))) ∧
      2 < (B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg a')) := by
  let q : CriticalPath Rg (sourceGeometry h) a' a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        a p.start_color (by
          rw [(sourceGeometry h).distance_constant _ p.start_color]
          exact sourceDistance_pos h) a' p.end_color p.critical⟩
  have hq : q.walk.getVert 2 = p.walk.getVert (p.walk.length-2) :=
    SimpleGraph.Walk.getVert_reverse _ _
  refine ⟨full_point_reciprocal_slices_gt_two e hz hk hb u hfull p,?_⟩
  have hh := full_point_reciprocal_slices_gt_two e hz hk hb u hfull q
  rwa [hq] at hh

omit hk in
include h e hz in
/-- Whole-core application of the strict forward and reciprocal slice
bounds for both critical image sizes and both moving covers. The full
point-core identity and the terminal contradictions remain to be proved. -/
theorem coreExhaustion_or_cubic_full_point_strict_slices :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ u : Equiv.Perm (Fin 6),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        4 < sourceDistance h →
        ∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
          (2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) ∧
            2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a)) ∧
          (2 < (B Rg a' ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert (p.walk.length-2))) ∧
            2 < (B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg a')) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,
      fun u hu hb4 _ _ p => full_point_four_slices_gt_two e hz hk hb4 u hu p⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the strict bounds at both ends of every
critical walk. Both reconstruction outcomes still require final assembly. -/
theorem rankTwo_or_cubic_full_point_strict_slices :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ u : Equiv.Perm (Fin 6),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        4 < sourceDistance h →
        ∀ (a a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) a a'),
          (2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) ∧
            2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg a)) ∧
          (2 < (B Rg a' ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert (p.walk.length-2))) ∧
            2 < (B Rg (p.walk.getVert (p.walk.length-2)) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg a')) :=
  (coreExhaustion_or_cubic_full_point_strict_slices e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
