module
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneComparison
import all Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneEscape
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBorelThompson
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeAlignment
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.PredecessorResidual
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlanePredecessor

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.KernelMovers
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.EndSlices
public import Theory.GroupTheory.Commutator.PerfectLayerLift
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.Escape

/-!
# Radius escape when all original Borel slices are small

The two-slice residual rotation controls the endpoint commutator modulo
its full reverse-kernel commutator, without comparing the starting movers.
In the distinct-mover central-generation branch, that kernel commutator is
fixed by the starting residual, so the endpoint commutator lies in the
Baumann slice. Equal movers already give the stronger seed bound.

A normal radius subgroup fixed by a critical actor modulo the Baumann
slice lies in that slice. Normal generation first bounds its component
commutator by the slice. The slice commutator lies in the seed, and
perfectness lowers this second commutator bound to the first. This uses the
literal cubic kernel and does not assert that residual centrality implies
centrality under the whole stabilizer.

On an actual generating Borel edge, the trapped neighbor and the Baumann
slice therefore generate a normal radius subgroup contained in the slice.
Eligibility excludes trapping. If every two-edge slice has index at most
two, this argument gives radius escape on every original critical path,
including central generation and both full moving covers. The resulting
backward paths retain their whole overlap, and reversed prefixes supply
forward eligibility.

The unconditional source reduction now retains compatible paths everywhere
or central generation together with an actual strict slice. The strict-slice
central-generation argument and the terminal distance contradictions still
need proof. Whole-core exhaustion is not asserted. The literal c.L,d.S
applications are in OriginalSylowExceptional.

The private imports share the established cover charts and residual-rotation
calculations within exceptional reconstruction. The natural import supplies
only the existing six-letter model calculation, never a graph identification.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.7)--(5.8), printed pp.919--920;
Aschbacher--Smith C.1.31--32, printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R


open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
local notation "π" => CubicAction.projection h e hz hk

include h e hz hk in
/-- Two small slices control the full endpoint commutator modulo the
starting seed and the full reverse-kernel commutator, for every mover comparison. -/
theorem borel_two_slice_endpoint_mod_kernel
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hforward : (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2)
    (hpre : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2))) :
    ⁅Z Rg c,Z Rg z⁆ ≤ Z Rg a ⊔ ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ := by
  by_contra hescape
  have hb := distance_gt_two h e hz hk
  have hs : (Q Rg z).relIndex (Z Rg a) < 4 := by
    rw [(critical_predecessor_small_slice h e hz hk hb p hpre).2.2]
    decide
  have hc : color Rg c = false := by
    have h1 := adjacent_color_ne Rg hat
    have h2 := adjacent_color_ne Rg hct
    rw [p.start_color] at h1
    cases hh : color Rg c <;> cases hh' : color Rg t <;> simp_all
  have hne : ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ ≠ ⊥ := by
    intro hh
    rw [commutator_comm] at hh
    exact hescape ((small_critical_predecessor_commutator h e hz hk hb p hs
      (Z Rg c) hbad (commutator_eq_bot_iff_le_centralizer.mp hh)).trans le_sup_left)
  obtain ⟨k,hkm,hkt,q,hq1,hqverts,hqi,hqir,hcard,htrans,hmove,hcentral,hnon⟩ :=
    two_slice_residual_line h e hz hk p hforward hpre hat hct hbad hne
  have hJ : Z Rg (act Rg k⁻¹ c) ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
    rw [Z_act,inv_inv]
    apply (map_mono hbad).trans_eq
    exact mem_normalizer_iff_map_conj_eq.mp
      ((Q_normalized Rg _) (Ltilde_le_stabilizer _ hkm))
  have hfixed : ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),Z Rg c⁆ =
      ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ := by
    rw [←critical_moving_kernel_eq_fixed h e p]
    exact ((critical_kernel_predecessor_moving h e hz hb p).2.2 _ hbad).symm
  have hfixedJ : ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),Z Rg (act Rg k⁻¹ c)⁆ =
      ⁅Z Rg z ⊓ Q Rg a,Z Rg c⁆ := by
    rw [←critical_moving_kernel_eq_fixed h e p]
    exact ((critical_kernel_predecessor_moving h e hz hb p).2.2 _ hJ).symm.trans htrans
  have hcontrol : ¬ ⁅U Rg z,Z Rg c⁆ ≤
      ⁅U Rg z ⊓ centralizer (Z Rg a : Set (FreeAmalgam Rg)),Z Rg c⁆ ⊔ ⁅U Rg z,Z Rg a⁆ := by
    intro hh
    apply hescape
    rw [commutator_comm,critical_predecessor_seed_movement h e hz hb p _ hbad]
    rw [hfixed] at hh
    exact hh.trans (sup_le le_sup_right (by
      rw [commutator_comm]
      exact ((commutator_mono le_rfl (DistanceEight.U_le_Z Rg z)).trans
        (critical_seed_commutator_le h p)).trans le_sup_left))
  let := h.relative_normal
  obtain ⟨i,hi,hir,hiR,hiQ,hiU,hA,hP,hJmap,hAr,hPr,hJr,hApi,hPpi,hJpi,hFi,hfix⟩ :=
    borel_predecessor_cover_chart h e hz hk u hR p (Z Rg c) hbad k hkm
  have hZ : (Z Rg c).map (MulAut.conj k).toMonoidHom = Z Rg (act Rg k⁻¹ c) := by
    rw [Z_act,inv_inv]
  rw [hZ] at hJmap
  obtain ⟨⟨τ,hτ,hτswap,hτeq⟩,hcrit⟩ :=
    plane_small_critical_chart_actor h e hz hk p hs i hi hiQ hiU hA hAr
  have hobs := plane_cover_commutator_obstruction h e hz hk k i hi hiU hA hP hJmap
    hne hfixed hfixedJ hmove.symm hcontrol
  let A := (Z Rg a).comap i
  let P := (Z Rg c).comap i
  let J := (Z Rg (act Rg k⁻¹ c)).comap i
  have hZcX := (sourceGeometry h).omega_bound c hc (by
    rw [(sourceGeometry h).distance_constant c hc]
    exact sourceDistance_pos h)
  have h2 : ∀ g ∈ P.map π, g^2=1 := by
    rintro _ ⟨g,hg,rfl⟩
    rw [←map_pow]
    have hg2 : g^2=1 := by
      apply hi
      simpa only [map_pow,map_one] using (mem_omegaCenter_iff.mp (hZcX hg)).2.1
    rw [hg2,map_one]
  have hab : ∀ g ∈ P.map π, ∀ k ∈ P.map π, Commute g k := by
    rintro _ ⟨g,hg,rfl⟩ _ ⟨j,hj,rfl⟩
    change _ * _ = _ * _
    rw [←map_mul,←map_mul]
    congr 1
    apply hi
    simp only [map_mul]
    exact ((mem_omegaCenter_iff.mp (hZcX hg)).2.2 (i j)
      (omegaCenter_le _ (hZcX hj))).symm
  have hPcQ : Z Rg c ≤ Q Rg a :=
    ((Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct))).trans
        ((sourceGeometry h).V_le_Q hb a p.start_color)
  have hcomm : ∀ g ∈ P.map π, Commute τ g := by
    obtain ⟨j,hj,hje⟩ := hτ
    rintro _ ⟨g,hg,rfl⟩
    rw [←hje]
    change _ * _ = _ * _
    rw [←map_mul,←map_mul]
    congr 1
    apply hi
    simp only [map_mul]
    exact (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a p.start_color)
      hj (i g) (hPcQ hg)).symm
  obtain ⟨hobs1,hobs2,hobs3,hobs4⟩ := hobs
  apply borel_cover_rotation_false h e hz hk u τ (hApi hτ) hτswap
    (P.map π) (J.map π) hPpi h2 hab hcomm
  · simpa only [hτeq] using hobs1
  · simpa only [hτeq] using hobs2
  · simpa only [hτeq] using hobs3
  · simpa only [hτeq] using hobs4

include h e hz hk in
/-- A normal radius subgroup fixed modulo the Baumann slice by a critical
actor lies in that slice; perfectness removes the extra commutator layer. -/
theorem normalized_radius_le_slice_of_critical_mod_slice
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (D : Subgroup (FreeAmalgam Rg)) (hDV : D ≤ V Rg (alpha Rg))
    (hDN : stabilizer Rg (alpha Rg) ≤ normalizer (D : Set (FreeAmalgam Rg)))
    (hcomm : ⁅D,Z Rg z⁆ ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)) :
    D ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  have hb := distance_gt_two h e hz hk
  let D₀ := D.comap (embedM Rg)
  let Z₀ := (Z Rg (alpha Rg)).comap (embedM Rg)
  let B₀ := (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).comap (embedM Rg)
  let A₀ := (Z Rg z).comap (embedM Rg)
  let K := L.subgroupOf M
  have hVG := (sourceGeometry h).V_local (alpha Rg) rfl hb
  have hBV : B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) ≤ V Rg (alpha Rg) :=
    fun v hv => ((mem_B_iff Rg (alpha Rg) _ hVG v).mp hv).1
  have hDm : D₀.map (embedM Rg) = D := map_comap_eq_self
    ((hDV.trans hVG).trans_eq (stabilizer_m_base Rg))
  have hZm : Z₀.map (embedM Rg) = Z Rg (alpha Rg) := map_comap_eq_self
    ((Z_le_stabilizer Rg _).trans_eq (stabilizer_m_base Rg))
  have hBm : B₀.map (embedM Rg) = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    map_comap_eq_self ((hBV.trans hVG).trans_eq (stabilizer_m_base Rg))
  have hAm : A₀.map (embedM Rg) = Z Rg z := map_comap_eq_self
    ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base Rg))
  have hKm : K.map (embedM Rg) = Ltilde Rg (alpha Rg) := by
    rw [Ltilde_alpha,h.relative_residual]
  have hg (m : M) : embedM Rg m ∈ stabilizer Rg (alpha Rg) := by
    change embedM Rg m ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let : D₀.Normal := ⟨by
    intro v hv m
    change embedM Rg (m*v*m⁻¹) ∈ D
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp (hDN (hg m)) (embedM Rg v)).mp hv⟩
  let : Z₀.Normal := ⟨by
    intro v hv m
    change embedM Rg (m*v*m⁻¹) ∈ Z Rg (alpha Rg)
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp ((Z_normalized Rg _) (hg m)) (embedM Rg v)).mp hv⟩
  let : B₀.Normal := ⟨by
    intro v hv m
    change embedM Rg (m*v*m⁻¹) ∈ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp
      (Escape.Propagation.Rigidity.B_normalized hb (alpha Rg) rfl (hg m)) (embedM Rg v)).mp hv⟩
  have hcomm₀ : ⁅D₀,A₀⁆ ≤ B₀ := by
    apply (map_le_map_iff_of_injective (embedM_injective Rg)).mp
    rwa [map_commutator,hDm,hAm,hBm]
  have hne : ¬ A₀ ≤ pCore 2 M := by
    intro he
    have hh := map_mono (f := embedM Rg) he
    rw [hAm,←Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le] at hh
    exact (critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
      (alpha Rg) rfl (sourceDistance_pos h) z p.end_color p.critical).2 hh
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) z p.end_color
  have hAtwo : IsPGroup 2 A₀ :=
    (IsElementaryAbelian.isPGroup 2 (Z Rg z)).comap_of_injective _ (embedM_injective Rg)
  have hDL : ⁅D₀,K⁆ ≤ B₀ :=
    CubicAction.normal_commutator_le_of_escaping_two h e hz D₀ B₀ A₀ hAtwo hne hcomm₀
  have hBL : ⁅B₀,K⁆ ≤ Z₀ := by
    apply (map_le_map_iff_of_injective (embedM_injective Rg)).mp
    rw [map_commutator,hBm,hKm,hZm,commutator_comm]
    apply commutator_le.mpr
    intro l hl v hv
    exact ((mem_B_iff Rg (alpha Rg) _ hVG v).mp hv).2 l hl
  let := h.component_perfect
  let d := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  let : Group.IsPerfect K := Group.IsPerfect.ofSurjective
    (f := d.symm.toMonoidHom) d.symm.surjective
  have hDZ : ⁅D₀,K⁆ ≤ Z₀ := commutator_le_of_iterated_le D₀ K Z₀
    ((commutator_mono hDL le_rfl).trans hBL)
  have hm := map_mono (f := embedM Rg) hDZ
  rw [map_commutator,hDm,hKm,hZm,commutator_comm] at hm
  intro v hv
  exact (mem_B_iff Rg (alpha Rg) _ hVG v).mpr
    ⟨hDV hv,fun l hl => hm (commutator_mem_commutator hl hv)⟩

include h e hz hk in
private theorem borel_central_two_slice_endpoint_le_slice
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg))
    (hsplit : X Rg (alpha Rg) = U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))
    (hforward : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2)
    (hpre : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2))) :
    ⁅Z Rg c,Z Rg z⁆ ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  have hb := distance_gt_two h e hz hk
  have hVG := (sourceGeometry h).V_local (alpha Rg) rfl hb
  have hZB : Z Rg (alpha Rg) ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    intro v hv
    apply (mem_B_iff Rg (alpha Rg) _ hVG v).mpr
    refine ⟨Z_le_VBall Rg _ 2 hv,?_⟩
    intro l hl
    exact (le_normalizer_iff_commutator_le_right.mp
      ((Ltilde_le_stabilizer (alpha Rg)).trans (Z_normalized Rg _)))
        (commutator_mem_commutator hl hv)
  by_cases heq : edgeOffenderJoin (alpha Rg) t = edgeOffenderJoin c t
  · exact (borel_equal_mover_two_slice_endpoint_control h e hz hk u hR p
      hat hct heq hforward hpre hbad).trans hZB
  let H := ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hKG : Z Rg z ⊓ Q Rg (alpha Rg) ≤ stabilizer Rg c :=
    (inf_le_right.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hHZ : H ≤ Z Rg c := le_normalizer_iff_commutator_le_right.mp
    (hKG.trans (Z_normalized Rg c))
  have hZV : Z Rg c ≤ V Rg (alpha Rg) := (Z_le_localZSpan Rg _ _).trans
    (localZSpan_le_V Rg
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct))
  have hHL : H ≤ centralizer (Ltilde Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    (borel_central_two_slice_distinct_control h e hz hk u hR p hat hct hgen
      hsplit heq hforward hpre hbad).2.2.trans (centralizer_le (fun _ hx => mem_sup_left hx))
  have hHB : H ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
    intro v hv
    apply (mem_B_iff Rg (alpha Rg) _ hVG v).mpr
    refine ⟨hZV (hHZ hv),?_⟩
    intro l hl
    have hz := commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hHL)
    exact (bot_le : (⊥ : Subgroup (FreeAmalgam Rg)) ≤ Z Rg (alpha Rg))
      (hz ▸ commutator_mem_commutator hl hv)
  exact (borel_two_slice_endpoint_mod_kernel h e hz hk u hR p hat hct hforward hpre hbad).trans
    (sup_le hZB hHB)

include h e hz hk in
/-- At an actual generating edge, central generation and the two small
slices put every trapped neighboring seed in the starting Baumann slice. -/
theorem borel_central_two_slice_trapped_le_slice
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg))
    (hsplit : X Rg (alpha Rg) = U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))
    (hforward : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2)
    (hpre : (B Rg (p.walk.getVert (p.walk.length-2))
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg z) ≤ 2)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2))) :
    Z Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  have hb := distance_gt_two h e hz hk
  let Ba := B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)
  let Y := Z Rg c ⊔ Ba
  have hVG := (sourceGeometry h).V_local (alpha Rg) rfl hb
  have hBV : Ba ≤ V Rg (alpha Rg) := fun v hv => ((mem_B_iff Rg (alpha Rg) _ hVG v).mp hv).1
  have hBN : stabilizer Rg (alpha Rg) ≤ normalizer (Ba : Set (FreeAmalgam Rg)) :=
    Escape.Propagation.Rigidity.B_normalized hb (alpha Rg) rfl
  have hZV : Z Rg c ≤ V Rg (alpha Rg) := (Z_le_localZSpan Rg _ _).trans
    (localZSpan_le_V Rg
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct))
  have hAG : Z Rg z ≤ stabilizer Rg (alpha Rg) :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl (sourceDistance_pos h) p.critical
  have hcomm : ⁅Y,Z Rg z⁆ ≤ Ba := by
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      (Z Rg c) Ba (Z Rg z) Ba hBN (hZV.trans hVG) (hBV.trans hVG)
    · exact borel_central_two_slice_endpoint_le_slice h e hz hk u hR p
        hat hct hgen hsplit hforward hpre hbad
    · exact le_normalizer_iff_commutator_le_left.mp (hAG.trans hBN)
  have hYN : stabilizer Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    rw [←hgen]
    apply sup_le
    · exact (le_inf
        ((show Q Rg t ≤ stabilizer Rg c from
          fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg c))
        ((show Q Rg t ≤ stabilizer Rg (alpha Rg) from
          fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans hBN)).trans
            (normalizer_inf_normalizer_le_normalizer_sup _ _)
    · exact le_normalizer_iff_commutator_le_left.mpr (hcomm.trans le_sup_right)
  exact le_sup_left.trans (normalized_radius_le_slice_of_critical_mod_slice h e hz hk p Y
    (sup_le hZV hBV) hYN hcomm)

include h e hz hk in
private theorem borel_uniform_radius_escape_base
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (hsmall : ∀ a c t : Vertex Rg, color Rg a = false → Adjacent Rg a t →
      Adjacent Rg c t → (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    ¬ V Rg (alpha Rg) ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  by_cases hsplit : X Rg (alpha Rg) = U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)))
  · intro hbad
    have hb := distance_gt_two h e hz hk
    have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
    obtain ⟨t,hat,hgen⟩ := borel_critical_generating_neighbor h e hz hk u hR p
    obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge h e hz hk hb rfl hat
    have hZV : Z Rg c ≤ V Rg (alpha Rg) := (Z_le_localZSpan Rg _ _).trans
      (localZSpan_le_V Rg
        (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct))
    have hprecol : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
      apply (p.vertex_color (Nat.sub_le _ _)).mpr
      have he := sourceDistance_even h
      rw [Nat.even_iff] at he ⊢
      have hh : p.walk.length = sourceDistance h := p.length_eq_b
      omega
    have hprelast : Adjacent Rg (p.walk.getVert (p.walk.length-2))
        (p.walk.getVert (p.walk.length-1)) := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
      rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
      exact (cosetGraph_adj Rg _ _).mp hh
    have hzlast : Adjacent Rg z (p.walk.getVert (p.walk.length-1)) := by
      have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
      rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
      exact adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp hh)
    exact hel ((DistanceEight.U_le_Z Rg c).trans
      (borel_central_two_slice_trapped_le_slice h e hz hk u hR p hat hct hgen hsplit
        (hsmall _ _ _ rfl hat hct) (hsmall _ _ _ hprecol hprelast hzlast) (hZV.trans hbad)))
  · exact borel_radius_escape_of_not_central_generation h e hz hk u hR hsplit p

include h e hz hk in
/-- Uniformly small two-edge slices force radius escape on every original
Borel critical path, including the central-generation case. -/
theorem borel_radius_escape_of_uniform_slices
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (hsmall : ∀ a c t : Vertex Rg, color Rg a = false → Adjacent Rg a t →
      Adjacent Rg c t → (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    ¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath Rg (sourceGeometry h)
      (act Rg g⁻¹ a) (act Rg g⁻¹ z),
      (∀ i, p₀.walk.getVert i = act Rg g⁻¹ (p.walk.getVert i)) ∧
      p₀.walk.length = p.walk.length :=
    ⟨p.act g⁻¹,fun i => by simp only [CriticalPath.act,actWalk_getVert],
      actWalk_length Rg g⁻¹ p.walk⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hverts,hlen⟩ := hpact
  apply borel_uniform_radius_escape_base h e hz hk u hR hsmall p₀
  rw [hlen,hverts,←hbase,V_act,Q_act]
  exact map_mono hbad

include h e hz hk in
/-- The uniformly-small-slice case has compatible backward paths, reversed
prefixes and forward eligibility throughout the original graph. -/
theorem borel_paths_of_uniform_slices
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (hsmall : ∀ a c t : Vertex Rg, color Rg a = false → Adjacent Rg a t →
      Adjacent Rg c t → (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    (¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∧
    (∃ d, ∃ w : (cosetGraph Rg).Walk d a,
      ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
        w.length = 2 ∧ q.walk = w.append (p.walk.take (p.walk.length-2)) ∧
        ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
    (∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) d,
      q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = a) ∧
    ¬ U Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _) := by
  have hb := distance_gt_two h e hz hk
  have escape := fun a z (p : CriticalPath Rg (sourceGeometry h) a z) =>
    borel_radius_escape_of_uniform_slices h e hz hk u hR hsmall p
  have hprefix := reverse_prefix_of_radius_escape h e hb escape p
  refine ⟨escape _ _ p,backward_path_of_radius_escape h p (escape _ _ p) hb,hprefix,?_⟩
  obtain ⟨d,q,_,hqa⟩ := hprefix
  have hh := critical_start_not_le_second_slice h e hz hb q
  rwa [hqa] at hh

include h e hz hk in
/-- The remaining Borel geometry has compatible paths everywhere, or
full omega central generation and a concrete strict two-edge slice. -/
theorem borel_paths_or_central_strict_slice
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    (∀ a z (p : CriticalPath Rg (sourceGeometry h) a z),
      (¬ V Rg a ≤ Q Rg (p.walk.getVert (p.walk.length-2))) ∧
      (∃ d, ∃ w : (cosetGraph Rg).Walk d a,
        ∃ q : CriticalPath Rg (sourceGeometry h) d (p.walk.getVert (p.walk.length-2)),
          w.length = 2 ∧ q.walk = w.append (p.walk.take (p.walk.length-2)) ∧
          ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      (∃ d, ∃ q : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2) d,
        q.walk.getVert 1 = p.walk.getVert 1 ∧ q.walk.getVert 2 = a) ∧
      ¬ U Rg (p.walk.getVert 2) ≤ B Rg a ((sourceGeometry h).Z_normal _)) ∨
    ((∀ a : Vertex Rg, color Rg a = false →
      (X Rg a = U Rg a ⊔
        (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) ∧
      X Rg a = Z Rg a) ∧
      ∃ a c t : Vertex Rg, color Rg a = false ∧ Adjacent Rg a t ∧ Adjacent Rg c t ∧
        2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)) := by
  rcases borel_central_or_paths h e hz hk u hR with hcentral | hpaths
  · by_cases hsmall : ∀ a c t : Vertex Rg, color Rg a = false → Adjacent Rg a t →
        Adjacent Rg c t → (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ≤ 2
    · exact Or.inl (fun _ _ p => borel_paths_of_uniform_slices h e hz hk u hR hsmall p)
    · push Not at hsmall
      exact Or.inr ⟨hcentral,hsmall⟩
  · exact Or.inl hpaths

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
