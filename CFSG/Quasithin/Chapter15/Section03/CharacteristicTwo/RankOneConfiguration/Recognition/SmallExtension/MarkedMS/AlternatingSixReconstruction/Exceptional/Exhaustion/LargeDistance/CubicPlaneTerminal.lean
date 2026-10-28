module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneEscape
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicTerminal
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOppositeTransfer

/-!
# Opposite-core transfer on the original cubic plane midpoint

A small forward Baumann slice bounds the selected span's index over its
intersection with the opposite two-core by two. If the selected span has
derived subgroup of order two, its central quotient detects the original
component and has order greater than four. The class-two transfer theorem
therefore preserves that same derived line in the intersection. The two
literal midpoint slices supply the opposite-core derived and cross-commutator
bounds. They force this line to centralize the midpoint stabilizer, contrary
to its critical-pair action. This proves the terminal contradiction without
restricting the cubic radical image to the point core.

In the plane branch, the proved radius escape supplies forward eligibility.
Endpoint control from a small opposite slice then forces the selected span
to be nonabelian. Consequently the two midpoint slices cannot both have
index at most two. Transport retains the original midpoint conjugator.
A nonabelian selected span constructs its own critical conjugate and gives
a strict reciprocal slice without any extra conjugator premise.

The whole-core and literal C.1.32 applications retain the Borel branch, both
full covers, the original projection kernel E and the nontrivial odd E/Q.
They exclude the plane configuration with two small midpoint slices. The
source arguments producing the required selected paths and small slices,
the larger-distance R4/R6 and Borel exclusions, and both unconditional core
exhaustions remain. No identification with a natural replacement is used.

The internal import deliberately reuses the opposite-core fixedness proof
within this reconstruction implementation; its private API is unchanged.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.10) and the terminal argument of (5.12), printed pp.879--881,927;
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
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
include h e hz hk in
private theorem selected_terminal_false_of_slice_and_opposite_core_bounds
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hcard : Nat.card (⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ :
        Subgroup (FreeAmalgam Rg)) = 2)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (hCcard : Nat.card (⁅⁅Q Rg (p.walk.getVert 2),Ltilde Rg (p.walk.getVert 2)⁆,
      ⁅Q Rg (p.walk.getVert 2),Ltilde Rg (p.walk.getVert 2)⁆⁆ :
        Subgroup (FreeAmalgam Rg)) ≤ 2)
    (hcross : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊓
      Q Rg (p.walk.getVert 2),
      ⁅Q Rg (p.walk.getVert 2),Ltilde Rg (p.walk.getVert 2)⁆⁆ ≤
      ⁅⁅Q Rg (p.walk.getVert 2),Ltilde Rg (p.walk.getVert 2)⁆,
        ⁅Q Rg (p.walk.getVert 2),Ltilde Rg (p.walk.getVert 2)⁆⁆) : False := by
  have hb := distance_gt_two h e hz hk
  have hindex := (selected_span_index_of_forward_slice h e hz hk hb p hslice).2
  have htransfer := selected_span_derived_transfer h e hz hk hb p hcard
    (localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊓ Q Rg (p.walk.getVert 2))
    inf_le_left (by rwa [inf_relIndex_left])
  have hnonabelian : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ := by
    intro hz
    rw [hz,card_bot] at hcard
    omega
  obtain ⟨_,x,hx,q,_,_,_⟩ := selected_span_conjugate_critical_path h hb p hnonabelian
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan Rg c (alpha Rg)
  let D := P ⊓ Q Rg c
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcolor : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hQa : Q Rg t ≤ stabilizer Rg (alpha Rg) :=
    fun _ hz => hz.2 _ (adjacent_symm Rg hat)
  have hQc : Q Rg t ≤ stabilizer Rg c :=
    fun _ hz => hz.2 _ (adjacent_symm Rg hct)
  have hPN : stabilizer Rg (alpha Rg) ≤
      normalizer ((⁅P,P⁆ : Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq, map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized Rg c (alpha Rg) hg)]
  have hPC : ⁅P,P⁆ ≤ centralizer
      (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (hPN.trans (normalizer_le_centralizer_of_card_two _ hcard))
  have hDN : Q Rg t ≤ normalizer (D : Set (FreeAmalgam Rg)) :=
    (le_inf (hQa.trans (localZSpan_normalized Rg c (alpha Rg)))
      (hQc.trans (Q_normalized Rg c))).trans inf_normalizer_le_normalizer_inf
  have hDcard : Nat.card (⁅D,D⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
    change Nat.card (⁅P ⊓ Q Rg c,P ⊓ Q Rg c⁆ :
      Subgroup (FreeAmalgam Rg)) ≤ 2
    rw [htransfer,hcard]
  have hfixed := opposite_core_derived_fixed h e hz hk hcolor hct D
    inf_le_right hDN hDcard hCcard hcross
  rw [htransfer] at hfixed
  have hcenter : ⁅P,P⁆ ≤ centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mpr
    rw [←CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg
      (by rw [h.relative_residual]; exact (codisjoint_subgroupOf_sup L R).eq_top) hcolor hct]
    exact sup_le (le_centralizer_iff.mp hfixed)
      (hQa.trans (le_centralizer_iff.mp hPC))
  have hcP : Z Rg c ≤ P := Z_le_localZSpan Rg _ _
  have hxP : Z Rg (act Rg x c) ≤ P := by
    rw [Z_act]
    exact (map_mono hcP).trans_eq (mem_normalizer_iff_map_conj_eq.mp
      (localZSpan_normalized Rg c (alpha Rg)
        ((stabilizer Rg (alpha Rg)).inv_mem hx)))
  exact critical_commutator_not_central h e hz hk q
    ((commutator_mono hcP hxP).trans hcenter)

include h e hz hk in
/-- Two literal small midpoint slices contradict a nonabelian selected
span, for any of the original cubic radical images. -/
theorem selected_terminal_false_of_midpoint_slices
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hnonabelian : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥)
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (p.walk.getVert 2))
    (he : act Rg g (alpha Rg) = a')
    (hopposite : (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg a') ≤ 2) : False := by
  have hb := distance_gt_two h e hz hk
  have hb4 := (selected_span_conjugate_critical_path h hb p hnonabelian).1
  let c := p.walk.getVert 2
  have hci : color Rg c = false :=
    (p.vertex_color (by have hl := p.length_eq_b; change p.walk.length = sourceDistance h at hl; omega)).mpr (by decide)
  have hs := midpoint_slice_eq_reverse_kernel h e hz hk hb4 p g hg he hopposite
  have hd := small_selected_span_derived h e hz hk hb p
    (by rw [hs.2.2.1]; decide) hslice hnonabelian
  have hPQ := (selected_span_le_forward_kernel (h := h) hb p).trans inf_le_left
  have hnonOpp : ⁅localZSpan Rg (alpha Rg) c,localZSpan Rg (alpha Rg) c⁆ ≠ ⊥ := by
    have hstart : Z Rg (alpha Rg) ≤ localZSpan Rg (alpha Rg) c := Z_le_localZSpan Rg _ _
    have hend : Z Rg a' ≤ localZSpan Rg (alpha Rg) c := by
      rw [←he,Z_act]
      exact (map_mono hstart).trans_eq (mem_normalizer_iff_map_conj_eq.mp
        (localZSpan_normalized Rg (alpha Rg) c ((stabilizer Rg c).inv_mem hg)))
    intro hn
    exact critical_commutator_not_central h e hz hk p
      (((commutator_mono hstart hend).trans_eq hn).trans bot_le)
  obtain ⟨_,x,hx,q,_,hq,_⟩ := selected_span_conjugate_critical_path h hb p hnonabelian
  have hBn := Escape.Propagation.Rigidity.B_normalized (geometry := sourceGeometry h) hb c hci
  have hBm : (B Rg c ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg c ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (hBn ((stabilizer Rg c).inv_mem hg))
  have hforwardOpp : (B Rg c ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (q.walk.getVert 2)) ≤ 2 := by
    rw [hq]
    have hh := hopposite
    have hUe : U Rg a' = (U Rg (alpha Rg)).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [←he,U_act]
    rw [hUe,←hBm,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at hh
    exact hh
  have hBma : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (geometry := sourceGeometry h)
        hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hx))
  have hoppositeOpp : (B Rg (q.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (act Rg x c)) ≤ 2 := by
    rw [hq,U_act,←hBma,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hslice
  have hbounds := selected_core_bounds_of_midpoint_slices_at h e hz hk hb4 q
    (by simpa only [hq] using hnonOpp) hforwardOpp x (hq.symm ▸ hx) rfl hoppositeOpp
  dsimp only at hbounds
  rw [hq] at hbounds
  exact selected_terminal_false_of_slice_and_opposite_core_bounds h e hz hk p hd.2.1 hslice
    hbounds.1 ((commutator_mono (le_inf inf_le_right (inf_le_left.trans hPQ)) le_rfl).trans hbounds.2)

include h e hz hk in
private theorem plane_selected_span_nonabelian_of_endpoint
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hcomm : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊓
      Q Rg (p.walk.getVert 2),Z Rg a'⁆ ≤ Z Rg (alpha Rg)) :
    ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ := by
  intro he
  have hb := distance_gt_two h e hz hk
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let P := localZSpan Rg c (alpha Rg)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t := adjacent_symm Rg
    ((cosetGraph_adj Rg _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases hh' : color Rg t <;> simp_all
  have hPQ := (selected_span_le_forward_kernel (h := h) hb p).trans inf_le_left
  have hPG : P ≤ stabilizer Rg c :=
    (hPQ.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hPc : P ≤ Q Rg c := two_subgroup_seed_centralizer_le_core h e hz hcol P
    ((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
      (alpha Rg) rfl).to_le hPQ)
    (le_inf hPG ((commutator_eq_bot_iff_le_centralizer.mp he).trans
      (centralizer_le (Z_le_localZSpan Rg c (alpha Rg)))))
  have hPV : P ≤ V Rg (alpha Rg) := localZSpan_le_V Rg (by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)])
  change ⁅P ⊓ Q Rg c,Z Rg a'⁆ ≤ Z Rg (alpha Rg) at hcomm
  have hPB := normalized_radius_le_slice_of_critical_commutator h e hz hb p P hPV
    (localZSpan_normalized Rg _ _) (by simpa only [inf_eq_left.mpr hPc] using hcomm)
  exact (plane_critical_paths h e hz hk u hR p).2.2.2
    ((DistanceEight.U_le_Z Rg _).trans ((Z_le_localZSpan Rg _ _).trans hPB))

include h e hz hk in
/-- At distance four, a plane critical pair in one midpoint orbit has a
strict slice at one of the two ends of the same two-edge segment. -/
theorem plane_midpoint_slice_alternative
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb4 : sourceDistance h = 4)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (p.walk.getVert 2))
    (he : act Rg g (alpha Rg) = a') :
    2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert 2)) ∨
      2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg a') := by
  by_contra! hs
  have hb := distance_gt_two h e hz hk
  have hPQ := (selected_span_le_forward_kernel (h := h) hb p).trans inf_le_left
  have hm := (midpoint_common_kernel_endpoint_commutator h e hz hk hb4 p g hg he hs.2).2
  have hcomm : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg) ⊓
      Q Rg (p.walk.getVert 2),Z Rg a'⁆ ≤ Z Rg (alpha Rg) :=
    ((commutator_mono (inf_le_inf_right _ hPQ) le_rfl).trans_eq hm).trans
      (le_normalizer_iff_commutator_le_left.mp
        ((critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
          (sourceDistance_pos h) p.critical).trans (Z_normalized Rg _)))
  exact selected_terminal_false_of_midpoint_slices h e hz hk p
    (plane_selected_span_nonabelian_of_endpoint h e hz hk u hR p hcomm) hs.1 g hg he hs.2

include h e hz hk in
/-- Transport the two-slice exclusion with the original midpoint conjugator
and both literal Baumann subgroups. -/
theorem plane_midpoint_slice_alternative_at
    (u : S)
    (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    (hb : sourceDistance h = 4)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (g : FreeAmalgam Rg) (hg : g ∈ stabilizer Rg (p.walk.getVert 2))
    (he : act Rg g a = a') :
    2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert 2)) ∨
      2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg a') := by
  obtain ⟨x,rfl⟩ := exists_mVertex_of_color Rg p.start_color
  have hxbase : act Rg x⁻¹ (mVertex Rg x) = alpha Rg := by
    simp only [act_mVertex,mul_inv_cancel]
    rfl
  have base := plane_midpoint_slice_alternative h e hz hk u hR hb
    (a' := act Rg x⁻¹ a')
  rw [←hxbase] at base
  let k := x*g*x⁻¹
  have hrestore (v : Vertex Rg) : act Rg x (act Rg x⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hkg : k ∈ stabilizer Rg ((p.act x⁻¹).walk.getVert 2) := by
    change k ∈ stabilizer Rg ((actWalk Rg x⁻¹ p.walk).getVert 2)
    rw [actWalk_getVert,stabilizer_act]
    exact ⟨g,hg,by simp only [inv_inv]; rfl⟩
  have hke : act Rg k (act Rg x⁻¹ (mVertex Rg x)) = act Rg x⁻¹ a' := by
    simp only [k,act_mul]
    rw [hrestore,he]
  have hci : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by have hl : p.walk.length = sourceDistance h := p.length_eq_b; omega)).mpr (by decide)
  have hh := base (p.act x⁻¹) k hkg hke
  change 2 < (B Rg (act Rg x⁻¹ (mVertex Rg x))
      ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg ((actWalk Rg x⁻¹ p.walk).getVert 2)) ∨
    2 < (B Rg ((actWalk Rg x⁻¹ p.walk).getVert 2)
      ((sourceGeometry h).Z_normal _)).relIndex (U Rg (act Rg x⁻¹ a')) at hh
  rw [actWalk_getVert,
    Escape.PairingControl.FirstPairing.B_act (by omega : 2 < sourceDistance h) _ _ p.start_color,
    Escape.PairingControl.FirstPairing.B_act (by omega : 2 < sourceDistance h) _ _ hci,
    U_act,U_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective,
    relIndex_map_map_of_injective _ _ (MulAut.conj _).injective] at hh
  exact hh

include h e hz hk in
/-- A nonabelian selected plane span constructs its own midpoint-conjugate
critical pair and forces a strict reciprocal slice on the original span. -/
theorem plane_selected_reciprocal_slice_alternative
    (u : S) (hR : (Rg).map π = D.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hnon : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥) :
    2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert 2)) ∨
      2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (alpha Rg)) := by
  have hb := distance_gt_two h e hz hk
  obtain ⟨hb4,x,hx,q,_,hq,_⟩ := selected_span_conjugate_critical_path h hb p hnon
  have hh := plane_midpoint_slice_alternative_at h e hz hk u hR hb4 q x (hq.symm ▸ hx) rfl
  have hBm : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj x⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (geometry := sourceGeometry h)
        hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hx))
  rw [hq,U_act,←hBm,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective] at hh
  exact hh.symm

omit hk in
include h e hz in
/-- Whole-core assembly excludes two small midpoint slices in the original
plane branch and constructs the reciprocal alternative on every nonabelian
selected span. The Borel and remaining plane configurations stay explicit. -/
theorem coreExhaustion_or_cubic_plane_terminal_slices :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 → ∀ a z (p : CriticalPath Rg (sourceGeometry h) a z)
          (g : FreeAmalgam Rg), g ∈ stabilizer Rg (p.walk.getVert 2) →
          act Rg g a = z →
          2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) ∨
            2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg z)) ∧
        (∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
          ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
            localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ →
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) ∨
            2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (alpha Rg)))) := by
  rcases coreExhaustion_or_cubic_plane_paths h e hz with
    hex | ⟨hk,hs,hb,hcovers,u,hborel | ⟨hplane,_⟩⟩
  · exact Or.inl hex
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inl hborel⟩
  · exact Or.inr ⟨hk,hs,hb,hcovers,u,Or.inr ⟨hplane,
      fun hb4 a z p g hg he => plane_midpoint_slice_alternative_at h e hz hk u hplane hb4 p g hg he,
      fun z p hn => plane_selected_reciprocal_slice_alternative h e hz hk u hplane p hn⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the opposite-core terminal exclusion,
retaining both full covers, the original cubic projection and Borel case. -/
theorem rankTwo_or_cubic_plane_terminal_slices :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      (∀ a : Vertex Rg, color Rg a = false →
        Nat.card (U Rg a) = 16 ∨ Nat.card (U Rg a) = 32) ∧
      ∃ u : S,
        (Rg).map (CubicAction.projection h e hz hk) =
          borel.map (MulAut.conj u).toMonoidHom ∨
        ((Rg).map (CubicAction.projection h e hz hk) =
          D.map (MulAut.conj u).toMonoidHom ∧
        (sourceDistance h = 4 → ∀ a z (p : CriticalPath Rg (sourceGeometry h) a z)
          (g : FreeAmalgam Rg), g ∈ stabilizer Rg (p.walk.getVert 2) →
          act Rg g a = z →
          2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) ∨
            2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex (U Rg z)) ∧
        (∀ z (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z),
          ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
            localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥ →
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (p.walk.getVert 2)) ∨
            2 < (B Rg (p.walk.getVert 2) ((sourceGeometry h).Z_normal _)).relIndex
              (U Rg (alpha Rg)))) :=
  (coreExhaustion_or_cubic_plane_terminal_slices h e hz).imp
    (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
