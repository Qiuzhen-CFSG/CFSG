module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourLargeSpan

/-!
# The whole derived radius and even critical actions in the original Borel graph

The moving radius and an abelian incident radius generate the whole radius.
Residual-fixed movement of the moving radius therefore makes the full derived
radius residual-fixed. The actual backward selection identifies this derived
group with both the selected span's derived group and its two-core movement.
It lies in the midpoint seed, has order dividing eight, and is moved by the
full starting stabilizer. The moving radius has exactly this core movement.

The critical endpoint centralizes that midpoint seed. The centralizer of the
whole derived radius contains the residual and two-core but is proper in the
stabilizer; its image under the literal cubic projection is consequently A6.
Thus each critical endpoint has even image and lies in the residual times
the two-core. Applying this to the generators of the entire midpoint radius
gives even image for that radius as well. Core-contained generators have
trivial image; the other generators form actual reverse critical pairs.

Both full moving covers and central attachments, and the odd quotient E/Q,
remain in the imported hypotheses. These consequences feed the remaining
large-image module contradiction in MS93 (5.12)(2). Whole-radius/core fixedness,
CoreExhaustion and exceptional reconstruction remain separate conclusions.
The literal c.L,d.S applications are in OriginalSylowExceptional.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.12)(2), printed pp.925--926; Aschbacher--Smith C.1.31--32,
printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
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
/-- The moving-radius bound and the abelian incident radius make the entire derived radius residual-fixed. -/
theorem borel_four_radius_derived_fixed_base
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    ⁅V Rg (alpha Rg),V Rg (alpha Rg)⁆ ≤ fixedCore Rg (alpha Rg) := by
  obtain ⟨z,p,_⟩ := borel_four_exists_large_critical h e hz hk u hR
  let a := alpha Rg
  let D := fixedCore Rg a
  have hb := distance_gt_two h e hz hk
  have hVQ := (sourceGeometry h).V_le_Q hb a rfl
  have hVG : V Rg a ≤ stabilizer Rg a := hVQ.trans (fun _ hx => hx.1)
  have hPN := fixedCore_normalized Rg a
  have hPG : Vcirc Rg a ≤ stabilizer Rg a :=
    (le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer a).trans (V_normalized a))).trans hVG
  have hEG := (edge_radius_le_radius rfl (base_adjacent Rg)).trans hVG
  have hdecomp : V Rg a = Vcirc Rg a ⊔ V Rg (beta Rg) :=
    radius_eq_moving_sup_edge_original h rfl (base_adjacent Rg)
  have hPV : ⁅Vcirc Rg a,V Rg a⁆ ≤ D :=
    (commutator_mono le_rfl hVQ).trans
      (borel_four_moving_radius_core_fixed h e hz hk u hR p)
  have hPE : ⁅Vcirc Rg a,V Rg (beta Rg)⁆ ≤ D :=
    (commutator_mono le_rfl (edge_radius_le_radius rfl (base_adjacent Rg))).trans hPV
  have hEE : ⁅V Rg (beta Rg),V Rg (beta Rg)⁆ ≤ D :=
    (commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr
        (edge_radius_commutative (sourceGeometry h) hb a (beta Rg) rfl (base_adjacent Rg)))).le.trans bot_le
  have hEV : ⁅V Rg (beta Rg),V Rg a⁆ ≤ D := by
    rw [commutator_comm,hdecomp]
    exact commutator_sup_le_of_relative_normal (stabilizer Rg a) _ _ _ _
      hPN hPG hEG hPE hEE
  change ⁅V Rg a,V Rg a⁆ ≤ D
  conv_lhs => lhs; rw [hdecomp]
  exact commutator_sup_le_of_relative_normal (stabilizer Rg a) _ _ _ _
    hPN hPG hEG hPV hEV

include h e hz hk in
/-- The whole radius and the selected span have the same derived subgroup, equal to the span core movement and contained in the midpoint seed. -/
theorem borel_four_radius_span_derived
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
    ⁅V Rg (alpha Rg),V Rg (alpha Rg)⁆ = ⁅P,P⁆ ∧
      ⁅P,P⁆ = ⁅P,Q Rg (alpha Rg)⁆ ∧
      ⁅V Rg (alpha Rg),V Rg (alpha Rg)⁆ ≤ Z Rg (p.walk.getVert 2) := by
  let a := alpha Rg
  let c := p.walk.getVert 2
  let P := localZSpan Rg c a
  let H := ⁅P,Q Rg a⁆
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
  have hPV : P ≤ V Rg a := localZSpan_le_V Rg (by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  have hVG : V Rg a ≤ stabilizer Rg a :=
    ((sourceGeometry h).V_le_Q hb a rfl).trans (fun _ hx => hx.1)
  have hPN : stabilizer Rg a ≤ normalizer (P : Set (FreeAmalgam Rg)) :=
    localZSpan_normalized Rg c a
  have hHN : stabilizer Rg a ≤ normalizer (H : Set (FreeAmalgam Rg)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅P,Q Rg a⁆).map (MulAut.conj g).toMonoidHom = ⁅P,Q Rg a⁆
    have hmP : P.map (MulAut.conj g).toMonoidHom = P :=
      mem_normalizer_iff_map_conj_eq.mp (hPN hg)
    have hmQ : (Q Rg a).map (MulAut.conj g).toMonoidHom = Q Rg a :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized Rg a hg)
    rw [map_commutator,hmP,hmQ]
  have hmQ : Vcirc Rg a ≤ Q Rg a :=
    (le_normalizer_iff_commutator_le_left.mp
      ((Ltilde_le_stabilizer a).trans (V_normalized a))).trans
        ((sourceGeometry h).V_le_Q hb a rfl)
  have hupper : ⁅V Rg a,V Rg a⁆ ≤ H := by
    rw [radius_derived_eq_moving_derived_original h (sourceGeometry h) hb a (beta Rg)
      rfl (base_adjacent Rg) (borel_four_radius_derived_fixed_base h e hz hk u hR)]
    apply (commutator_mono
      (borel_four_moving_radius_le_span_seed h e hz hk u hR p) hmQ).trans
    exact commutator_sup_le_of_relative_normal (stabilizer Rg a) _ _ _ _ hHN
      (hPV.trans hVG) (Z_le_stabilizer Rg a) le_rfl
      ((Z_centralizes_Q Rg a rfl).le.trans bot_le)
  obtain ⟨A,hAZ,hattach,hi,hcomm,d,t,x,hx,hxd,hxt,hat,hdt,hJgen,hfix,hgen,hgenZ,
    q,hqt,hover,hbound,hnorm,hstrict,hlarge,hcore,hDF,hne,hspan,hDN⟩ :=
    borel_four_large_backward_span h e hz hk u hR p
      (borel_four_critical_images_large h e hz hk u hR p)
  have hxG := Ltilde_le_stabilizer _ hx
  have hseed : Z Rg c ≤ localZSpan Rg d a := by
    have he : act Rg x⁻¹ d = c := by
      rw [←hxd,←act_mul,mul_inv_cancel,act_one]
    rw [←he,Z_act,inv_inv]
    exact (map_mono (Z_le_localZSpan Rg d a)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized Rg d a hxG))
  have hP : P ≤ localZSpan Rg d a := by
    change localZSpan Rg c a ≤ _
    conv_lhs => rw [localZSpan_eq_conjugates]
    apply iSup_le
    intro g
    exact (map_mono hseed).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized Rg d a ((stabilizer Rg a).inv_mem g.property)))
  have hdP : Z Rg d ≤ P := by
    rw [←hxd,Z_act]
    exact (map_mono (Z_le_localZSpan Rg c a)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (hPN ((stabilizer Rg a).inv_mem hxG)))
  have hlower : H ≤ ⁅P,P⁆ := ((commutator_mono hP le_rfl).trans hspan.le).trans
    (commutator_mono hdP (Z_le_localZSpan Rg c a))
  have hsub := commutator_mono hPV hPV
  have hDseed : ⁅Z Rg d,Z Rg c⁆ ≤ Z Rg c := by
    have hrev := critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      d q.start_color (by
        rw [(sourceGeometry h).distance_constant _ q.start_color]
        exact sourceDistance_pos h) c q.end_color q.critical
    have hn := (critical_Z_le_stabilizer Rg (sourceGeometry h) c q.end_color
      (by rw [(sourceGeometry h).distance_constant _ q.end_color]; exact sourceDistance_pos h)
      hrev).trans (Z_normalized Rg c)
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hn
  exact ⟨le_antisymm (hupper.trans hlower) hsub,
    le_antisymm (hsub.trans hupper) hlower,
    hupper.trans (((commutator_mono hP le_rfl).trans hspan.le).trans hDseed)⟩

include h e hz hk in
/-- The entire derived radius is small and residual-fixed, and the whole stabilizer moves it. -/
theorem borel_four_radius_derived_configuration
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    let H := ⁅V Rg (alpha Rg),V Rg (alpha Rg)⁆
    H ≤ fixedCore Rg (alpha Rg) ∧ H ≤ X Rg (alpha Rg) ∧ Nat.card H ∣ 8 ∧
      ¬ H ≤ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  obtain ⟨z,p,hp⟩ := borel_four_exists_large_critical h e hz hk u hR
  have he := borel_four_radius_span_derived h e hz hk u hR p
  dsimp only
  rw [he.1,he.2.1]
  exact borel_four_large_span_core_fixed h e hz hk u hR p hp

include h e hz hk in
/-- The two-core movement of the moving radius is exactly the derived subgroup of the whole radius. -/
theorem borel_four_moving_core_eq_derived
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    ⁅Vcirc Rg (alpha Rg),Q Rg (alpha Rg)⁆ = ⁅V Rg (alpha Rg),V Rg (alpha Rg)⁆ := by
  obtain ⟨z,p,hp⟩ := borel_four_exists_large_critical h e hz hk u hR
  let a := alpha Rg
  let P := localZSpan Rg (p.walk.getVert 2) a
  let H := ⁅V Rg a,V Rg a⁆
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
  have hVG : V Rg a ≤ stabilizer Rg a :=
    ((sourceGeometry h).V_le_Q hb a rfl).trans (fun _ hx => hx.1)
  have hPV : P ≤ V Rg a := localZSpan_le_V Rg (by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  have he := borel_four_radius_span_derived h e hz hk u hR p
  have hPQ : ⁅P,Q Rg a⁆ = H := (he.1.trans he.2.1).symm
  have hHN : stabilizer Rg a ≤ normalizer (H : Set (FreeAmalgam Rg)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅V Rg a,V Rg a⁆).map (MulAut.conj g).toMonoidHom = ⁅V Rg a,V Rg a⁆
    have hm : (V Rg a).map (MulAut.conj g).toMonoidHom = V Rg a :=
      mem_normalizer_iff_map_conj_eq.mp (V_normalized a hg)
    rw [map_commutator,hm]
  apply le_antisymm
  · exact (commutator_mono (borel_four_moving_radius_le_span_seed h e hz hk u hR p) le_rfl).trans
      (commutator_sup_le_of_relative_normal (stabilizer Rg a) _ _ _ _ hHN
        (hPV.trans hVG) (Z_le_stabilizer Rg a) hPQ.le
        ((Z_centralizes_Q Rg a rfl).le.trans bot_le))
  · rw [radius_derived_eq_moving_derived_original h (sourceGeometry h) hb a (beta Rg)
      rfl (base_adjacent Rg) (borel_four_radius_derived_fixed_base h e hz hk u hR)]
    exact commutator_mono le_rfl
      ((le_normalizer_iff_commutator_le_left.mp
        ((Ltilde_le_stabilizer a).trans (V_normalized a))).trans
          ((sourceGeometry h).V_le_Q hb a rfl))

include h e hz hk in
/-- A critical endpoint fixes the entire derived radius, so its literal cubic image is even. -/
theorem borel_four_critical_endpoint_even
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    CubicAction.graphImage h e hz hk (Z Rg z) ≤ alternatingGroup (Fin 6) := by
  let a := alpha Rg
  let H := ⁅V Rg a,V Rg a⁆
  let C := (centralizer (H : Set (FreeAmalgam Rg))).comap (embedM Rg)
  have hconf := borel_four_radius_derived_configuration h e hz hk u hR
  have hHC : H ≤ centralizer (Ltilde Rg a : Set (FreeAmalgam Rg)) :=
    hconf.1.trans inf_le_right
  have hHL : Ltilde Rg a ≤ centralizer (H : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp hHC
  have hHQ : Q Rg a ≤ centralizer (H : Set (FreeAmalgam Rg)) :=
    (Q_le_centralizer_X Rg a).trans (centralizer_le hconf.2.1)
  have hLC : L.subgroupOf (L ⊔ R) ≤ C := by
    intro x hx
    apply hHL
    rw [Ltilde_alpha,h.relative_residual]
    exact mem_map_of_mem (embedM Rg) hx
  have hQC : pCore 2 (L ⊔ R : Subgroup G) ≤ C := by
    intro x hx
    apply hHQ
    rw [Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact mem_map_of_mem (embedM Rg) hx
  have hker : (π).ker ≤ C := by
    rw [CubicAction.projection_kernel]
    exact sup_le ((map_subtype_le _).trans hLC) hQC
  have hAlt : alternatingGroup (Fin 6) ≤ C.map π := by
    rw [←CubicAction.component_image h e hz hk]
    exact map_mono hLC
  have hdiv : (C.map π).index ∣ 2 := by
    rw [←alternatingGroup.index_eq_two (α := Fin 6)]
    exact index_dvd_of_le hAlt
  have hCimage : C.map π = alternatingGroup (Fin 6) := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
    · have hm : C.map π = ⊤ := index_eq_one.mp h1
      have hc : C = ⊤ := by
        have hh := congrArg (Subgroup.comap π) hm
        simpa only [comap_map_eq,sup_eq_left.mpr hker,comap_top] using hh
      exfalso
      apply hconf.2.2.2
      apply le_centralizer_iff.mp
      intro x hx
      change x ∈ stabilizer Rg (mVertex Rg 1) at hx
      rw [stabilizer_m_base] at hx
      obtain ⟨m,rfl⟩ := hx
      exact show m ∈ C from hc.symm ▸ mem_top m
    · exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two h2
  have hHseed := (borel_four_radius_span_derived h e hz hk u hR p).2.2
  have hl : p.walk.length = 4 := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
  have hc : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hZQ : Z Rg (p.walk.getVert 2) ≤ Q Rg z := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hc)
    rw [(sourceGeometry h).distance_constant _ hc,p.dist_end,hl]
    exact distance_gt_two h e hz hk
  have hZC : Z Rg z ≤ centralizer (H : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg z p.end_color)).trans
      (centralizer_le (hHseed.trans hZQ))
  exact (map_mono (comap_mono (f := embedM Rg) hZC)).trans_eq hCimage

include h e hz hk in
/-- Each critical endpoint lies in the actual residual times the two-core; the latter factor is retained. -/
theorem borel_four_critical_endpoint_residual_core
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    Z Rg z ≤ Ltilde Rg (alpha Rg) ⊔ Q Rg (alpha Rg) := by
  let K := L.subgroupOf (L ⊔ R)
  let Q₀ := pCore 2 (L ⊔ R : Subgroup G)
  have he : (alternatingGroup (Fin 6)).comap π = K ⊔ Q₀ := by
    rw [←CubicAction.component_image h e hz hk,comap_map_eq,CubicAction.projection_kernel]
    exact le_antisymm
      (sup_le le_sup_left (sup_le ((map_subtype_le _).trans le_sup_left) le_sup_right))
      (sup_le le_sup_left (le_sup_right.trans le_sup_right))
  have hh := (map_le_iff_le_comap).mp (borel_four_critical_endpoint_even h e hz hk u hR p)
  rw [he] at hh
  have hm := map_mono (f := embedM Rg) hh
  have hZG := critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
    (sourceDistance_pos h) p.critical
  have hLm : K.map (embedM Rg) = Ltilde Rg (alpha Rg) := by
    rw [Ltilde_alpha,h.relative_residual]
  rw [map_comap_eq_self (hZG.trans_eq (stabilizer_m_base Rg)),Subgroup.map_sup,hLm,
    show Q₀.map (embedM Rg) = Q Rg (alpha Rg) from
      (Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le).symm] at hm
  exact hm

include h e hz hk in
/-- Every seed generating the entire midpoint radius has even image in the original cubic projection. -/
theorem borel_four_midpoint_radius_even
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    CubicAction.graphImage h e hz hk (V Rg (p.walk.getVert 2)) ≤ alternatingGroup (Fin 6) := by
  let c := p.walk.getVert 2
  let F := (alternatingGroup (Fin 6)).comap π
  let D := F.map (embedM Rg)
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hca : (cosetGraph Rg).dist c (alpha Rg) = 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)]
  have hQF : pCore 2 (L ⊔ R : Subgroup G) ≤ F := by
    intro x hx
    change π x ∈ alternatingGroup (Fin 6)
    have hkx : x ∈ (π).ker := by
      rw [CubicAction.projection_kernel]
      exact mem_sup_right hx
    rw [MonoidHom.mem_ker.mp hkx]
    exact (alternatingGroup (Fin 6)).one_mem
  have hQD : Q Rg (alpha Rg) ≤ D := by
    rw [Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact map_mono hQF
  have hVD : V Rg c ≤ D := by
    apply NaturalStructure.Exclusion.radius_le_of_m_ball hc
    intro v hv hvc
    by_cases hcore : Z Rg v ≤ Q Rg (alpha Rg)
    · exact hcore.trans hQD
    have hmin := criticalDistance_le Rg v ((sourceGeometry h).exists_critical v hv) hcore
    rw [(sourceGeometry h).distance_constant _ hv] at hmin
    change sourceDistance h ≤ _ at hmin
    have htri := (cosetGraph_connected Rg).dist_triangle (u := v) (v := c) (w := alpha Rg)
    have hpair : CriticalPair Rg v (alpha Rg) ((sourceGeometry h).exists_critical v hv) := by
      refine ⟨?_,hcore⟩
      rw [(sourceGeometry h).distance_constant _ hv]
      change _ = sourceDistance h
      omega
    have hrev := critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      v hv (by rw [(sourceGeometry h).distance_constant _ hv]; exact sourceDistance_pos h)
      (alpha Rg) rfl hpair
    let q := CriticalPath.ofPair (geometry := sourceGeometry h) rfl hrev
    have he := borel_four_critical_endpoint_even h e hz hk u hR q
    have hZG := critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) hrev
    have hm := map_mono (f := embedM Rg) ((map_le_iff_le_comap).mp he)
    rw [map_comap_eq_self (hZG.trans_eq (stabilizer_m_base Rg))] at hm
    exact hm
  have hh := comap_mono (f := embedM Rg) hVD
  rw [show D = F.map (embedM Rg) from rfl,
    comap_map_eq_self_of_injective (embedM_injective Rg)] at hh
  exact map_le_iff_le_comap.mpr hh


end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
