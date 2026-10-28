module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicShiftContainment
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Centralizer orbits of the shifted cubic span

For the small-slice shift in MS93 (5.9), every conjugate under the full
line centralizer has the same controlled, noncentral commutator line.
The predecessor seed and full reverse critical kernel consequently
centralize the conjugated span. The normal-radius slice theorem excludes
criticality of its center with the old endpoint; the full-seed centralizer
then places both the conjugated seed and the whole span in that endpoint's
two-core. Taking the actual conjugate spans gives both source orbits.

The seed orbit remains in the second radius and outside its Baumann slice.
Both orbits are normalized by the same line centralizer, which generates
the second local group together with the prescribed new endpoint seed.
The whole-core and literal C.1.32 applications construct these orbits from
the original small-slice hypotheses. All statements retain the cubic kernel
and both full covers; no equality of conjugate edge kernels is assumed.

The remaining common-kernel commutator argument and strict small-slice
estimate, other radical images, R4/R6, MS93 (5.11)--(5.12), natural
exhaustion and final reconstruction of both outcomes remain necessary.

Source: Meierfrankenfeld--Stellmacher (1993), (5.9), printed p.921,
the centralizer orbits Z and W immediately after equation (**).
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
private theorem conjugated_span_le_old_endpoint_core
    (hb : 4 < sourceDistance h)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
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
      (small_selected_span_forward_commutator h e hz hk hb2 p hsmall hslice).1
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
  have hcard := (s.line_facts e hz hk hb2 hsmall hslice heligible).1
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

/-- The pointwise line centralizer in the second local group, used in (5.9). -/
@[expose] def lineCentralizer : Subgroup (FreeAmalgam Rg) :=
  stabilizer Rg (p.walk.getVert 2) ⊓ centralizer (s.line : Set (FreeAmalgam Rg))

/-- The full shifted seed spanned under its line centralizer. -/
@[expose] def seedOrbit : Subgroup (FreeAmalgam Rg) :=
  conjugateSpanBy (Z Rg s.centerVertex) s.lineCentralizer

/-- The entire shifted span spanned under the same line centralizer. -/
@[expose] def spanOrbit : Subgroup (FreeAmalgam Rg) :=
  conjugateSpanBy s.span s.lineCentralizer

include e hz hk in
/-- Both complete centralizer orbits lie in the old endpoint's two-core.
The conjugator ranges over the whole line centralizer, not only its residual. -/
theorem centralizer_orbits_le_old_endpoint_core
    (hb : 4 < sourceDistance h)
    (hsmall : (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4)
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
    have hh := s.conjugated_span_le_old_endpoint_core e hz hk hb hsmall hslice heligible
      ((x : FreeAmalgam Rg)*s.conjugator) hxy (by rw [←hmap]; exact hxH)
    rw [centerVertex,Z_act,inv_inv,hmap,s.span_map,hmap]
    simpa only [Z_act,inv_inv] using hh
  constructor
  · rw [seedOrbit,conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun x => (hconj x).1)
  · rw [spanOrbit,conjugateSpanBy_eq_iSup_conj]
    exact iSup_le (fun x => (hconj x).2)

include e hz in
/-- The seed orbit stays inside the second radius, and still escapes its
Baumann slice because the original reciprocal seed does. -/
theorem seedOrbit_radius_and_escape (hb : 2 < sourceDistance h) :
    s.seedOrbit ≤ V Rg (p.walk.getVert 2) ∧
      ¬ s.seedOrbit ≤ B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _) := by
  have hZV : Z Rg (alpha Rg) ≤ V Rg (p.walk.getVert 2) :=
    le_iSup_of_le (alpha Rg) (le_iSup_of_le (by
      have hl : p.walk.length = sourceDistance h := p.length_eq_b
      exact (p.dist_start (by omega)).le) le_rfl)
  have hy := Ltilde_le_stabilizer _ s.residual
  have hVm := mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized Rg _ hy)
  have hZaV : Z Rg s.centerVertex ≤ V Rg (p.walk.getVert 2) := by
    rw [centerVertex,Z_act,inv_inv]
    exact (map_mono hZV).trans_eq hVm
  refine ⟨conjugateSpanBy_le hZaV (inf_le_left.trans (DistanceEight.V_normalized Rg _)),?_⟩
  intro hbad
  have hh := (le_conjugateSpanBy (Z Rg s.centerVertex) s.lineCentralizer).trans hbad
  have hBm := mem_normalizer_iff_map_conj_eq.mp
    (Escape.Propagation.Rigidity.B_normalized hb _ s.path.start_color hy)
  rw [centerVertex,Z_act,inv_inv,←hBm] at hh
  exact critical_start_not_le_second_slice h e hz hb p
    ((DistanceEight.U_le_Z Rg _).trans
      ((map_le_map_iff_of_injective (MulAut.conj s.conjugator).injective).mp hh))

/-- The same literal centralizer normalizes both source orbits and generates
the second local group with the prescribed new critical endpoint. -/
theorem centralizer_orbits_normalized :
    s.lineCentralizer ≤ normalizer (s.seedOrbit : Set (FreeAmalgam Rg)) ∧
      s.lineCentralizer ≤ normalizer (s.spanOrbit : Set (FreeAmalgam Rg)) ∧
      s.lineCentralizer ⊔ Z Rg s.endpoint = stabilizer Rg (p.walk.getVert 2) :=
  ⟨le_normalizer_conjugateSpanBy _ _,le_normalizer_conjugateSpanBy _ _,s.generates⟩


end SmallSliceShift

omit hk in
include e hz in
/-- Whole-core application of the (5.9) centralizer-orbit containment. The
same constructed shift retains its generating centralizer, noncentral line,
both full covers and the literal old endpoint. -/
theorem coreExhaustion_or_cubic_centralizer_orbits :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) ≤ 2 →
          ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) →
          ∃ s : SmallSliceShift h p,
            ⁅s.span,s.kernel⁆ = s.line ∧ Nat.card s.line = 2 ∧
            s.line ≤ centralizer (stabilizer Rg s.centerVertex : Set (FreeAmalgam Rg)) ∧
            (¬ s.span ≤ B Rg s.centerVertex ((sourceGeometry h).Z_normal _)) ∧
            (4 < sourceDistance h →
              s.seedOrbit ⊔ s.spanOrbit ≤ Q Rg a' ∧
              s.seedOrbit ≤ V Rg (p.walk.getVert 2) ∧
              ¬ s.seedOrbit ≤ B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,graph_U_card h e hz hk,?_⟩
    intro u hfull a' p hsmall hslice hel
    obtain ⟨s⟩ := exists_small_slice_shift h e hz hk hb u hfull p hsmall hslice hel
    have hf := s.line_facts e hz hk hb hsmall hslice hel
    refine ⟨s,s.span_commutator e hz hk hb hsmall hslice,hf.1,hf.2,s.span_not_le_slice hb hel,?_⟩
    intro hb4
    have ho := s.centralizer_orbits_le_old_endpoint_core e hz hk hb4 hsmall hslice hel
    exact ⟨sup_le ho.1 ho.2,s.seedOrbit_radius_and_escape e hz hb⟩

omit hk in
include e hz in
/-- Literal C.1.32 application with both centralizer orbits constructed.
Strict small-slice exclusion and the remaining reconstruction branches
remain separate source obligations. -/
theorem rankTwo_or_cubic_centralizer_orbits :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false → Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∀ (u : Equiv.Perm (Fin 6)),
        (Rg).map (CubicAction.projection h e hz hk) = pointCore.map (MulAut.conj u).toMonoidHom →
        ∀ (a' : Vertex Rg) (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a'),
          (Q Rg a').relIndex (Z Rg (alpha Rg)) < 4 →
          (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) ≤ 2 →
          ¬ U Rg (p.walk.getVert 2) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) →
          ∃ s : SmallSliceShift h p,
            ⁅s.span,s.kernel⁆ = s.line ∧ Nat.card s.line = 2 ∧
            s.line ≤ centralizer (stabilizer Rg s.centerVertex : Set (FreeAmalgam Rg)) ∧
            (¬ s.span ≤ B Rg s.centerVertex ((sourceGeometry h).Z_normal _)) ∧
            (4 < sourceDistance h →
              s.seedOrbit ⊔ s.spanOrbit ≤ Q Rg a' ∧
              s.seedOrbit ≤ V Rg (p.walk.getVert 2) ∧
              ¬ s.seedOrbit ≤ B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)) :=
  (coreExhaustion_or_cubic_centralizer_orbits e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
