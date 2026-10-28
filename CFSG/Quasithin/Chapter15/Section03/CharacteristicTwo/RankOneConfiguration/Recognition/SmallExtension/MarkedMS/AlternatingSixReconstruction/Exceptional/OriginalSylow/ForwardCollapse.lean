module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.ForwardOrbits
public import Theory.GroupTheory.Commutator.NilpotentSaturation
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistinctShifts
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward

/-!
# The nonzero orbit line in the original Borel geometry

The controlled alternative for the whole seed orbit cannot occur. Joining
that orbit to the second seed gives a normal radius subgroup D. Modulo
[D,Q] times the second seed, the critical actor fixes D, so the original
component does too. The actual incident edge core already normalizes the
two-seed subgroup. Residual-edge generation and nilpotent commutator
saturation therefore collapse D to that subgroup. Its index over the
second seed divides eight, forcing D into the Baumann slice and contradicting
the retained orbit escape.

Consequently the full reverse-kernel commutator R₃ has order two. This
uses both moving covers and keeps the odd cubic kernel quotient E/Q;
it does not replace the local group by its component times Q. The literal
original-source application retains the conjugate-seed and proper-mover
witness from ForwardOrbits.

Source: Meierfrankenfeld--Stellmacher (1993), (5.9), printed p.921, the
non-normality assertion preceding R₃. Full-stabilizer centrality of R₃,
stabilization of the whole span orbit, strict slices and the terminal
distance contradictions remain necessary for CoreExhaustion.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags CoreCrossing
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
open AlternatingSixReconstruction.Exceptional.OriginalSylow
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
include e hz hk in
private theorem normal_section_residual_control_mod {c d : Vertex Rg}
    (q : CriticalPath Rg (sourceGeometry h) c d)
    (D N : Subgroup (FreeAmalgam Rg)) (hDG : D ≤ stabilizer Rg c)
    (hDN : stabilizer Rg c ≤ normalizer (D : Set (FreeAmalgam Rg)))
    (hNN : stabilizer Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)))
    (hNG : N ≤ stabilizer Rg c)
    (hcomm : ⁅D,Z Rg d⁆ ≤ N) : ⁅D,Ltilde Rg c⁆ ≤ N := by
  obtain ⟨i,hi,hir,hiQ,_⟩ := graph_cover h e hz hk c q.start_color
  let D₀ := D.comap i
  let Z₀ := N.comap i
  let A₀ := (Z Rg d).comap i
  have hDm : D₀.map i = D := map_comap_eq_self (hDG.trans_eq hir.symm)
  have hZm : Z₀.map i = N :=
    map_comap_eq_self (hNG.trans_eq hir.symm)
  have hAm : A₀.map i = Z Rg d := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) c q.start_color
      (by rw [(sourceGeometry h).distance_constant _ q.start_color]; exact sourceDistance_pos h)
      q.critical).trans_eq hir.symm)
  have hg (m : (L ⊔ R : Subgroup G)) : i m ∈ stabilizer Rg c := by
    rw [←hir]
    exact ⟨m,rfl⟩
  let : D₀.Normal := ⟨by
    intro z hd m
    change i (m*z*m⁻¹) ∈ D
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hDN (hg m)) (i z)).mp hd⟩
  let : Z₀.Normal := ⟨by
    intro z hd m
    change i (m*z*m⁻¹) ∈ N
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hNN (hg m)) (i z)).mp hd⟩
  have hcomm₀ : ⁅D₀,A₀⁆ ≤ Z₀ := by
    apply (map_le_map_iff_of_injective hi).mp
    rwa [map_commutator,hDm,hAm,hZm]
  have hne : ¬ A₀ ≤ pCore 2 (L ⊔ R : Subgroup G) := by
    intro he
    have hh := map_mono (f := i) he
    rw [hAm,hiQ] at hh
    exact (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      c q.start_color (by
        rw [(sourceGeometry h).distance_constant _ q.start_color]
        exact sourceDistance_pos h) d q.end_color q.critical).2 hh
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) d q.end_color
  have hAtwo : IsPGroup 2 A₀ :=
    (IsElementaryAbelian.isPGroup 2 (Z Rg d)).comap_of_injective i hi
  have hm := map_mono (f := i)
    (CubicAction.normal_commutator_le_of_escaping_two h e hz D₀ Z₀ A₀ hAtwo hne hcomm₀)
  let j : (L ⊔ R : Subgroup G) →* stabilizer Rg c := i.codRestrict _ hg
  have hjs : Function.Surjective j := by
    intro x
    have hx : (x : FreeAmalgam Rg) ∈ i.range := hir.symm ▸ x.property
    obtain ⟨m,hm⟩ := hx
    exact ⟨m,Subtype.ext hm⟩
  have hj : (stabilizer Rg c).subtype.comp j = i := rfl
  have hLm : (L.subgroupOf (L ⊔ R)).map i = Ltilde Rg c := by
    rw [←h.relative_residual,←hj,←map_map,map_pResidual_of_surjective 2 j hjs]
    rfl
  rwa [map_commutator,hDm,hZm,hLm] at hm

include e hz hk in
private theorem small_normal_radius_le_slice_at
    {c : Vertex Rg} (hc : color Rg c = false)
    (D : Subgroup (FreeAmalgam Rg)) (hDV : D ≤ V Rg c)
    (hDN : stabilizer Rg c ≤ normalizer (D : Set (FreeAmalgam Rg)))
    (hsmall : (Z Rg c).relIndex D ∣ 8) :
    D ≤ B Rg c ((sourceGeometry h).Z_normal _) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg hc
  have hbase : act Rg g⁻¹ c = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  let f := (MulAut.conj g).toMonoidHom
  have hV : (V Rg c).map f = V Rg (alpha Rg) := by
    simpa only [inv_inv,hbase] using (V_act Rg g⁻¹ c).symm
  have hZ : (Z Rg c).map f = Z Rg (alpha Rg) := by
    simpa only [inv_inv,hbase] using (Z_act Rg g⁻¹ c).symm
  have hG : (stabilizer Rg c).map f = stabilizer Rg (alpha Rg) := by
    simpa only [inv_inv,hbase] using (stabilizer_act Rg g⁻¹ c).symm
  have hb := distance_gt_two h e hz hk
  have hB : (B Rg c ((sourceGeometry h).Z_normal _)).map f =
      B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    simpa only [inv_inv,hbase] using
      (Escape.PairingControl.FirstPairing.B_act (geometry := sourceGeometry h) hb g⁻¹ c hc).symm
  have hN : stabilizer Rg (alpha Rg) ≤ normalizer (D.map f : Set (FreeAmalgam Rg)) := by
    rw [←hG]
    exact (map_mono hDN).trans (le_normalizer_map f)
  have hs : (Z Rg (alpha Rg)).relIndex (D.map f) ∣ 8 := by
    rw [←hZ,relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hsmall
  have hh := small_normal_radius_le_slice h e hz hk (D.map f)
    ((map_mono hDV).trans_eq hV) hN hs
  exact (map_le_map_iff_of_injective (f := f) (MulAut.conj g).injective).mp
    (hh.trans_eq hB.symm)

namespace SmallSliceShift
variable {a' : Vertex (edge L R)}
  {p : CriticalPath (edge L R) (sourceGeometry h) (alpha (edge L R)) a'}
  (s : SmallSliceShift h p)

include e hz hk in
private theorem borel_orbit_control_impossible
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) =
      Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (hcontrol : ⁅s.seedOrbit,Z Rg s.endpoint⁆ ≤
      Z Rg (p.walk.getVert 2) ⊔ s.orbitDisplacement) : False := by
  let c := p.walk.getVert 2
  let t := act Rg s.conjugator⁻¹ (p.walk.getVert 1)
  let D := s.seedOrbit ⊔ Z Rg c
  let Y := Z Rg s.centerVertex ⊔ Z Rg c
  let N := ⁅D,Q Rg c⁆ ⊔ Z Rg c
  have hb2 : 2 < sourceDistance h := by omega
  have hc : color Rg c = false := s.path.start_color
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hat : Adjacent Rg s.centerVertex t := by
    apply (adjacent_act_iff Rg s.conjugator⁻¹ _ _).mpr
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := by
    have hh := adjacent_symm Rg
      ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
    simpa only [s.fixes_second] using (adjacent_act_iff Rg s.conjugator⁻¹ _ _).mpr hh
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hct
    rw [hc] at hh
    cases he : color Rg t <;> simp_all
  have hdist : (cosetGraph Rg).dist c s.centerVertex ≤ 2 :=
    CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct
  have hDV : D ≤ V Rg c := sup_le (s.seedOrbit_radius_and_escape e hz hb2).1
    (Z_le_VBall Rg c 2)
  have hDQ : D ≤ Q Rg c := hDV.trans ((sourceGeometry h).V_le_Q hb2 c hc)
  have hDG : D ≤ stabilizer Rg c := hDQ.trans (fun _ hx => hx.1)
  have hEG : Z Rg s.endpoint ≤ stabilizer Rg c :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) c hc
      (by rw [(sourceGeometry h).distance_constant c hc]; exact sourceDistance_pos h)
      s.path.critical
  have hRD : s.orbitDisplacement ≤ D :=
    ((s.borel_orbit_displacement_nonzero_quadratic e hz hk hb u hR hslice).2.1.trans
      inf_le_left).trans le_sup_left
  have hDN : stabilizer Rg c ≤ normalizer (D : Set (FreeAmalgam Rg)) := by
    rw [←s.centralizer_orbits_normalized.2.2]
    apply sup_le
    · exact (le_inf s.centralizer_orbits_normalized.1
        (inf_le_left.trans (Z_normalized Rg c))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · have hEN := hEG.trans (Z_normalized Rg c)
      have hE : ⁅s.seedOrbit,Z Rg s.endpoint⁆ ≤ D :=
        hcontrol.trans (sup_le le_sup_right hRD)
      apply le_normalizer_iff.mpr
      intro x hx v hv
      have hm : D.map (MulAut.conj x).toMonoidHom ≤ D := by
        rw [Subgroup.map_sup]
        refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hEN hx)).le.trans le_sup_right)
        rintro _ ⟨y,hy,rfl⟩
        rw [commutator_comm] at hE
        have hm := D.mul_mem (hE (commutator_mem_commutator hx hy)) (mem_sup_left hy)
        simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hm
      exact hm (mem_map_of_mem (MulAut.conj x).toMonoidHom hv)
  have hYD : Y ≤ D := sup_le
    ((le_conjugateSpanBy (Z Rg s.centerVertex) s.lineCentralizer).trans le_sup_left) le_sup_right
  have hNN : stabilizer Rg c ≤ normalizer (N : Set (FreeAmalgam Rg)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    dsimp only [N]
    rw [Subgroup.map_sup,map_commutator,mem_normalizer_iff_map_conj_eq.mp (hDN hg),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg c hg),
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized Rg c hg)]
  have hND : N ≤ D := sup_le
    (le_normalizer_iff_commutator_le_left.mp ((show Q Rg c ≤ stabilizer Rg c from
      fun _ hx => hx.1).trans hDN)) le_sup_right
  have hNG : N ≤ stabilizer Rg c := hND.trans hDG
  have hRN : s.orbitDisplacement ≤ N :=
    (commutator_mono (show s.seedOrbit ≤ D from le_sup_left)
      (show s.orbitKernel ≤ Q Rg c from inf_le_right)).trans le_sup_left
  have hDE : ⁅D,Z Rg s.endpoint⁆ ≤ N := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg c)
      s.seedOrbit (Z Rg c) (Z Rg s.endpoint) N hNN (le_sup_left.trans hDG)
      (Z_le_stabilizer Rg c) (hcontrol.trans (sup_le le_sup_right hRN))
    exact (le_normalizer_iff_commutator_le_left.mp
      (hEG.trans (Z_normalized Rg c))).trans le_sup_right
  have hres : ⁅D,Ltilde Rg c⁆ ≤ N :=
    normal_section_residual_control_mod e hz hk s.path D N hDG hDN hNN hNG hDE
  have hQY : Q Rg c ≤ normalizer (Y : Set (FreeAmalgam Rg)) :=
    (le_inf ((Q_le_stabilizer_of_dist_le_two c s.centerVertex hc s.center_color hdist).trans
      (Z_normalized Rg _)) ((show Q Rg c ≤ stabilizer Rg c from fun _ hx => hx.1).trans
      (Z_normalized Rg c))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hQtG : Q Rg t ≤ stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  have hQtY : Q Rg t ≤ normalizer (Y : Set (FreeAmalgam Rg)) :=
    (le_inf ((show Q Rg t ≤ stabilizer Rg s.centerVertex from
      fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _))
      (hQtG.trans (Z_normalized Rg c))).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hYN : stabilizer Rg c ≤ normalizer ((Y ⊔ N : Subgroup (FreeAmalgam Rg)) :
      Set (FreeAmalgam Rg)) := by
    rw [←CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
      (by rw [h.relative_residual]; exact (codisjoint_subgroupOf_sup L R).eq_top) hc hct]
    refine sup_le ?_ ((le_inf hQtY (hQtG.trans hNN)).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _))
    apply le_normalizer_iff_commutator_le_left.mpr
    apply le_trans ?_ le_sup_right
    apply commutator_sup_le_of_relative_normal (stabilizer Rg c)
      Y N (Ltilde Rg c) N hNN (hYD.trans hDG) hNG
      ((commutator_mono hYD le_rfl).trans hres)
    exact le_normalizer_iff_commutator_le_left.mp ((Ltilde_le_stabilizer _).trans hNN)
  have hcover : D ≤ Y ⊔ ⁅D,Q Rg c⁆ := by
    have hs : s.seedOrbit ≤ Y ⊔ N :=
      conjugateSpanBy_le (show Z Rg s.centerVertex ≤ Y ⊔ N from
        le_sup_left.trans le_sup_left) (inf_le_left.trans hYN)
    have hd : D ≤ Y ⊔ N := sup_le hs (le_sup_right.trans le_sup_left)
    exact hd.trans (sup_le le_sup_left (sup_le le_sup_right (le_sup_right.trans le_sup_left)))
  let := finite_stabilizer Rg c
  let : Finite (Q Rg c) := Finite.of_injective
    (inclusion (show Q Rg c ≤ stabilizer Rg c from fun _ hx => hx.1)) (inclusion_injective _)
  have hDY : D ≤ Y := le_of_le_sup_commutator_of_isNilpotent (Q Rg c) D Y (Q Rg c)
    (Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le c hc).isNilpotent
    hDQ (hYD.trans hDQ) le_rfl hQY hcover
  have hD : D = Y := le_antisymm hDY hYD
  have hZQt : Z Rg c ≤ Q Rg t :=
    (((sourceGeometry h).omega_bound c hc (by
      rw [(sourceGeometry h).distance_constant c hc]; exact sourceDistance_pos h)).trans
      (omegaCenter_le _)).trans (Q_le_adjacent_h Rg ht hct)
  let := finite_Z Rg c
  have hsmall : (Z Rg c).relIndex D ∣ 8 := by
    rw [hD]
    change (Z Rg c).relIndex (Z Rg s.centerVertex ⊔ Z Rg c) ∣ 8
    rw [relIndex_sup_of_normalizes (Z Rg s.centerVertex) (Z Rg c)
      (hZQt.trans ((show Q Rg t ≤ stabilizer Rg s.centerVertex from
        fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _)))]
    have hd := relIndex_dvd_of_le_left (Z Rg s.centerVertex) (adjacent_Z_le Rg hc hct)
    rw [borel_full_seed_edge_index h e hz hk u hR s.center_color hat] at hd
    exact hd
  exact (s.seedOrbit_radius_and_escape e hz hb2).2
    (le_sup_left.trans (small_normal_radius_le_slice_at e hz hk hc D hDV hDN hsmall))

include e hz hk in
/-- The controlled alternative collapses to a small normal two-seed span,
contradicting the orbit's Baumann-slice escape. Thus R₃ has order two. -/
theorem borel_orbit_displacement_card_two
    (hb : 4 < sourceDistance h) (u : Equiv.Perm (Fin 6))
    (hR : (Rg).map (CubicAction.projection h e hz hk) =
      Theory.SpecificGroups.SymmetricSix.borel.map (MulAut.conj u).toMonoidHom)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) : Nat.card s.orbitDisplacement = 2 := by
  rcases s.borel_orbit_control_or_line e hz hk hb u hR hslice with hc | hl
  · exact (s.borel_orbit_control_impossible e hz hk hb u hR hslice hc).elim
  · exact hl

end SmallSliceShift
end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
