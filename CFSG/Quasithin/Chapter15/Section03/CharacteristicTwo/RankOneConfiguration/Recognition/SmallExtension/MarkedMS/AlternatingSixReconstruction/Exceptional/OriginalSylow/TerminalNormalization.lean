module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.CommonKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.TerminalKernels
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicKernelTransport
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneRadiusNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardRigidity

/-!
# Terminal normalization above distance six on the original Borel graph

The common full kernel controls the displacement of the whole terminal
seed under the reverse critical kernel. Above distance six, the opposite
radius centralizes both preceding endpoint seeds. Generation and the actual
shift transporter then make the edge part of the displacement central under
the entire terminal stabilizer.

The faithful natural quotient detects actors moving the whole cover into
the critical line modulo its central attachment. Its lifted preimage uses
the full cubic kernel E, not the two-core Q. Consequently the reverse kernel
fixes the whole critical hyperplane, and its restricted commutator vanishes.
This excludes the nonnormalizing alternative of TerminalKernels and places
the entire intermediate core in the opposite proper Thompson mover. The
full endpoint omega group also normalizes the required join.

OriginalSylowExceptional constructs these shifts on the literal c.L,d.S
source. The distance-six case, the remaining mover comparison and the later
terminal exclusions are not asserted here. Both full moving covers and their
central attachments remain throughout.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii), (5.10), printed pp.866--867,922--923. The natural-branch
import supplies only the six-letter moved-space inclusion lemma. The
cover-to-graph transport is proved here with the original cubic kernel.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
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
local notation "π" => CubicAction.projection h e hz hk


local notation "M" => (L ⊔ R : Subgroup G)
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)
private abbrev terminalCoverAction : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive W₀) := by
  let := h.relative_normal
  exact NormalElementaryQuotient.representation W₀ π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)
private def terminalCoverMap : Additive W₀ →ₗ[ZMod 2] natural (Fin 6) :=
  Classical.choose (CubicAction.moved_natural_projection h e hz hk)
private theorem terminalCoverMap_surjective : Function.Surjective (terminalCoverMap h e hz hk) :=
  (Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).1
private theorem terminalCoverMap_equivariant (g : Equiv.Perm (Fin 6)) (v : Additive W₀) :
    terminalCoverMap h e hz hk (terminalCoverAction h e hz hk g v) =
      naturalRepresentation (Fin 6) g (terminalCoverMap h e hz hk v) := by
  let := h.relative_normal
  obtain ⟨a,rfl⟩ := CubicEven.projection_surjective h e hz hk g
  have he : terminalCoverAction h e hz hk (π a) v = Additive.ofMul (MulAut.conjNormal a v.toMul) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact NormalElementaryQuotient.representation_apply W₀ π
      (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk) a v
  rw [he]
  exact (Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).2.2 a v

include h e hz hk in
private theorem terminal_cover_actor_le_of_critical_line_mod_center
    (A B : Subgroup M)
    (hne : ¬ A ≤ extensionKernel h)
    (hindex : (centralizer (A : Set M)).relIndex (W₀) ≤ 2)
    (hcomm : ⁅W₀,B⁆ ≤ ⁅W₀,A⁆ ⊔
      (W₀ ⊓ center M)) :
    B ≤ extensionKernel h ⊔ A := by
  let := h.relative_normal
  let U := W₀
  let f := terminalCoverMap h e hz hk
  let W := subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map π)
  have hker := CubicAction.moved_projection_kernel h e hz hk
  have hm (D : Subgroup M) :
      (NormalElementaryQuotient.commutatorSpace U D).map f =
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (D.map π) := by
    rw [NormalElementaryQuotient.commutatorSpace_eq U π (CubicEven.projection_surjective h e hz hk) hker]
    change (subspaceCommutator (terminalCoverAction h e hz hk) ⊤ (D.map π)).map f = _
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (terminalCoverAction h e hz hk) (MonoidHom.id _) f
      (fun g v => (terminalCoverMap_equivariant h e hz hk g v).symm) (D.map π) ⊤
    have hf : f.range = ⊤ := LinearMap.range_eq_top.mpr
      (terminalCoverMap_surjective h e hz hk)
    simpa only [Submodule.map_top,hf,map_id] using hh.symm
  have hwhole (D : Subgroup M) :
      NormalElementaryQuotient.subgroupSpace U ⁅U,D⁆ =
        NormalElementaryQuotient.commutatorSpace U D := by
    rfl
  have hspace : NormalElementaryQuotient.commutatorSpace U B ≤ W.comap f := by
    have hle : NormalElementaryQuotient.subgroupSpace U ⁅U,B⁆ ≤
        NormalElementaryQuotient.subgroupSpace U (⁅U,A⁆ ⊔ (U ⊓ center M)) :=
      fun _ hv => hcomm hv
    rw [NormalElementaryQuotient.subgroupSpace_sup U (commutator_le_left U A) inf_le_left,
      hwhole B,hwhole A] at hle
    apply hle.trans
    apply sup_le
    · exact Submodule.map_le_iff_le_comap.mp (hm A).le
    · intro v hv
      have hf0 : f v = 0 :=
        (Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).2.1 v
          |>.mpr (by
            intro g hg
            exact (Subgroup.mem_center_iff.mp hv.2) g)
      change f v ∈ W
      rw [hf0]
      exact W.zero_mem
  have hsmall : fixedCodim (terminalCoverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim U π (CubicEven.projection_surjective h e hz hk) hker] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (terminalCoverAction h e hz hk) (naturalRepresentation (Fin 6))
      f (terminalCoverMap_surjective h e hz hk)
      (terminalCoverMap_equivariant h e hz hk) (A.map π)).trans hsmall
  have hnA : A.map π ≠ ⊥ := by
    intro he
    exact hne ((CubicAction.projection_kernel h e hz hk) ▸ (map_eq_bot_iff A).mp he)
  have him : B.map π ≤ A.map π :=
    Natural.Exhaustion.LargeDistance.SectionFive.small_actor_le_of_moved_le _ _ hnA hnat
      ((hm B).symm ▸ Submodule.map_le_iff_le_comap.mpr hspace)
  have hle := (le_comap_map π B).trans (comap_mono him)
  rw [Subgroup.comap_map_eq,(CubicAction.projection_kernel h e hz hk)] at hle
  exact hle.trans_eq (sup_comm _ _)

include h e hz hk in
/-- An actor moving the full seed into the critical line modulo its central
attachment fixes the entire critical kernel. The lifted actor retains E/Q. -/
theorem borel_critical_kernel_fixed_of_line_mod_center
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hp : (Q Rg z).relIndex (Z Rg a) < 4)
    (Y : Subgroup (FreeAmalgam Rg)) (hY : Y ≤ stabilizer Rg a)
    (hcomm : ⁅Z Rg a,Y⁆ ≤ ⁅Z Rg a,Z Rg z⁆ ⊔
      (U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)))) :
    ⁅Z Rg a ⊓ Q Rg z,Y⁆ = ⊥ := by
  let := h.relative_normal
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,_⟩ := graph_cover h e hz hk a p.start_color
  have hAG : Z Rg z ≤ stabilizer Rg a :=
    critical_Z_le_stabilizer Rg (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)
      p.critical
  let A := (Z Rg z).comap i
  let B := Y.comap i
  have hmA : A.map i = Z Rg z := map_comap_eq_self (hAG.trans_eq hir.symm)
  have hmB : B.map i = Y := map_comap_eq_self (hY.trans_eq hir.symm)
  have hmC : (W₀ ⊓ center M).map i =
      U Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
    have hh := map_inf_centralizer_of_injective i hi W₀ ⊤
    simpa only [←MonoidHom.range_eq_map,hir,hiU,coe_top,centralizer_univ] using hh.symm
  have hD : (⁅W₀,A⁆).map i = ⁅Z Rg a,Z Rg z⁆ := by
    rw [map_commutator,hiU,hmA,small_critical_moving_commutator_eq h e hz hk p hp]
  have hnA : ¬ A ≤ extensionKernel h :=
    critical_comap_not_le_extension h e hz p i hi (hAG.trans_eq hir.symm) hiQ
  let := finite_Z Rg a
  let : Finite (U Rg a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg a)) (inclusion_injective _)
  have hCA : Q Rg z ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg z p.end_color))
  have hidx : (centralizer (A : Set M)).relIndex W₀ ≤ 2 := by
    rw [←inf_relIndex_right,inf_comm,←relIndex_map_map_of_injective _ _ hi,
      ←map_inf_centralizer_of_injective i hi,hiU,hmA,inf_relIndex_left]
    exact ((relIndex_le_of_le_left hCA index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z Rg a) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices h e hz hk p hp).1
  have hcontrol : ⁅W₀,B⁆ ≤ ⁅W₀,A⁆ ⊔ (W₀ ⊓ center M) := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [Subgroup.map_sup,hD,hmC,map_commutator,hiU,hmB]
    exact (commutator_mono (DistanceEight.U_le_Z Rg a) le_rfl).trans hcomm
  have hle := map_mono (f := i)
    (terminal_cover_actor_le_of_critical_line_mod_center h e hz hk A B hnA hidx hcontrol)
  rw [hmB,Subgroup.map_sup,hiE,hmA] at hle
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mp
  apply hle.trans
  apply sup_le
  · exact (inf_le_right.trans (centralizer_le ((sourceGeometry h).omega_bound a p.start_color (by
      rw [(sourceGeometry h).distance_constant _ p.start_color]; exact sourceDistance_pos h)))).trans
        (centralizer_le inf_le_left)
  · exact le_centralizer_iff.mp (inf_le_right.trans hCA)

private theorem predecessor_radius_intersection_central
    (hb : 6 < sourceDistance h)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let I := V Rg v ⊓ Z Rg t.edge
    I ≤ centralizer (stabilizer Rg r.start : Set (FreeAmalgam Rg)) ∧
    I ≤ centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg)) ∧
    I ≤ centralizer (stabilizer Rg t.start : Set (FreeAmalgam Rg)) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let w := p.walk.getVert (p.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let I := V Rg v ⊓ Z Rg t.edge
  have htz : color Rg t.edge = true := by
    have hh := adjacent_color_ne Rg t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color Rg t.edge
    · exact (hh he.symm).elim
    · rfl
  have hrz : color Rg r.edge = true := by
    have hh := adjacent_color_ne Rg r.adjacent_start
    rw [q.path.start_color] at hh
    cases he : color Rg r.edge
    · exact (hh he.symm).elim
    · rfl
  have hvz : (cosetGraph Rg).dist v z = 2 := by
    rw [r.path.dist_end]
    have hl : r.path.walk.length = sourceDistance h := r.path.length_eq_b
    omega
  have hzw : (cosetGraph Rg).dist z w = 2 := by
    rw [q.path.dist_end]
    have hl : q.path.walk.length = sourceDistance h := q.path.length_eq_b
    omega
  have hvw : (cosetGraph Rg).dist v w ≤ 4 := by
    have hh := (cosetGraph_connected Rg).dist_triangle (u := v) (v := z) (w := w)
    omega
  have hVQz : V Rg v ≤ Q Rg z := by
    apply V_le_Q_of_dist_add_two_lt Rg (geometry := sourceGeometry h) t.path.end_color
    change (cosetGraph Rg).dist v z + 2 < sourceDistance h
    rw [hvz]
    omega
  have hVQw : V Rg v ≤ Q Rg w := by
    apply V_le_Q_of_dist_add_two_lt Rg (geometry := sourceGeometry h) t.path.end_color
    change (cosetGraph Rg).dist v w + 2 < sourceDistance h
    omega
  have hCz : V Rg v ≤ centralizer (Z Rg z : Set (FreeAmalgam Rg)) :=
    hVQz.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg z r.path.end_color)))
  have hCw : V Rg v ≤ centralizer (Z Rg w : Set (FreeAmalgam Rg)) :=
    hVQw.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg w q.path.end_color)))
  have hIr : I ≤ centralizer (stabilizer Rg r.start : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [←t.generation]
    exact sup_le (le_centralizer_iff.mp (inf_le_right.trans (terminal_edge_seed_central htz)))
      (le_centralizer_iff.mp (inf_le_left.trans hCz))
  have hIedge : I ≤ Z Rg r.edge := by
    obtain ⟨x,hx,hxe⟩ := stabilizer_transitive_neighbors Rg r.start
      t.adjacent_start r.adjacent_shift
    rw [←hxe,Z_act,←terminal_fixed_map I (stabilizer Rg r.start) hIr
      ((stabilizer Rg r.start).inv_mem hx)]
    exact map_mono inf_le_right
  have hIq : I ≤ centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [←r.generation]
    exact sup_le (le_centralizer_iff.mp (hIedge.trans (terminal_edge_seed_central hrz)))
      (le_centralizer_iff.mp (inf_le_left.trans hCw))
  have hr2 : r.path.walk.getVert 2 = q.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using r.overlap 0 (Nat.zero_le _)
  have hshift : act Rg t.transporter q.start = t.start := by
    simpa only [hr2] using t.start_eq
  have hIt : I ≤ centralizer (stabilizer Rg t.start : Set (FreeAmalgam Rg)) := by
    rw [←hshift,stabilizer_act]
    have hh := (map_mono (f := (MulAut.conj t.transporter⁻¹).toMonoidHom) hIq).trans
      (map_centralizer_le_centralizer_image _ _)
    rwa [terminal_fixed_map I (stabilizer Rg r.start) hIr
      ((stabilizer Rg r.start).inv_mem t.transporter_mem)] at hh
  exact ⟨hIr,hIq,hIt⟩


include h e hz hk in
/-- Above distance six, the full reverse kernel moves the whole last seed
into its critical line times its full central attachment. -/
theorem borel_three_shift_whole_seed_alignment
    (hb : 6 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    ⁅Z Rg t.start,Z Rg z ⊓ Q Rg r.start⁆ ≤ ⁅Z Rg t.start,Z Rg v⁆ ⊔
      (U Rg t.start ⊓ centralizer (stabilizer Rg t.start : Set (FreeAmalgam Rg))) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let F := Z Rg z ⊓ Q Rg r.start
  let H := ⁅Z Rg t.start,F⁆
  let D := ⁅Z Rg t.start,Z Rg v⁆
  let I := (H ⊔ D) ⊓ Z Rg t.edge
  have hb4 : 4 < sourceDistance h := by omega
  have ht := two_borel_backward_shifts_small_moving h e hz hk hb4 q.path r t
  have hsmall : (Q Rg v).relIndex (Z Rg t.start) < 4 := by rw [ht.2.1]; decide
  have hcommon := borel_moving_common_kernel h e hz hk u hR t.path hsmall ht.2.2.2.2
  dsimp only at hcommon
  rw [t.first] at hcommon
  have htcol : color Rg t.edge = true := by
    have hh := adjacent_color_ne Rg t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color Rg t.edge <;> simp_all
  have hzv : (cosetGraph Rg).dist z v = 2 := by
    rw [SimpleGraph.dist_comm,r.path.dist_end]
    have hl : r.path.walk.length = sourceDistance h := r.path.length_eq_b
    omega
  have hFT : F ≤ Q Rg t.edge := inf_le_right.trans
    (Q_le_adjacent_h Rg htcol t.adjacent_start)
  have hFv : F ≤ Q Rg v := inf_le_left.trans (Z_le_Q_of_dist_lt Rg z
    ((sourceGeometry h).exists_critical z r.path.end_color) (by
      rw [(sourceGeometry h).distance_constant z r.path.end_color,hzv]
      change 2 < sourceDistance h
      omega))
  have hDv : D ≤ Z Rg v := by
    dsimp only [D]
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp
      ((Z_le_stabilizer_of_dist_le t.start _ t.path.critical.1.le).trans (Z_normalized Rg v))
  have hFcent : F ≤ centralizer (D : Set (FreeAmalgam Rg)) :=
    hFv.trans ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg v t.path.end_color))).trans (centralizer_le hDv))
  have hFJ : F ≤ edgeOffenderJoin t.start t.edge := (le_inf hFT hFcent).trans_eq hcommon.1
  have hspan : H ⊔ D ≤ D ⊔ Z Rg t.edge := sup_le
    (((commutator_mono le_rfl hFJ).trans hcommon.2.2.2.2.2.2).trans_eq hcommon.2.2.2.1) le_sup_left
  have hFV : F ≤ V Rg v := inf_le_left.trans
    ((Z_le_localZSpan Rg z v).trans (localZSpan_le_V Rg hzv.le))
  have hHV : H ≤ V Rg v := (commutator_mono le_rfl hFV).trans
    (le_normalizer_iff_commutator_le_right.mp
      ((Z_le_stabilizer_of_dist_le t.start _ t.path.critical.1.le).trans (V_normalized v)))
  have hIt : I ≤ centralizer (stabilizer Rg t.start : Set (FreeAmalgam Rg)) :=
    (inf_le_inf_right _ (sup_le hHV (hDv.trans (Z_le_VBall Rg v 2)))).trans
      (predecessor_radius_intersection_central h hb p q r t).2.2
  have hHU : H ≤ U Rg t.start := (commutator_mono le_rfl hFT).trans
    (full_seed_edge_commutator_le_moving h e hz t.path.start_color t.adjacent_shift)
  have hDU : D ≤ U Rg t.start := by
    dsimp only [D]
    rw [←small_critical_moving_commutator_eq h e hz hk t.path hsmall]
    exact le_normalizer_iff_commutator_le_left.mp
      ((critical_Z_le_stabilizer Rg (sourceGeometry h) t.start t.path.start_color
        (by rw [(sourceGeometry h).distance_constant _ t.path.start_color]; exact sourceDistance_pos h)
        t.path.critical).trans (U_normalized t.start))
  have hIU : I ≤ U Rg t.start := inf_le_left.trans (sup_le hHU hDU)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) t.start t.path.start_color
  have hCN : Z Rg t.edge ≤ normalizer (D : Set (FreeAmalgam Rg)) :=
    ((adjacent_Z_le Rg t.path.start_color t.adjacent_shift).trans
      ((le_centralizer (Z Rg t.start)).trans
        (centralizer_le (critical_seed_commutator_le h t.path)))).trans
          (Subgroup.centralizer_le_normalizer _)
  have hdecomp : H ⊔ D ≤ D ⊔ I := by
    intro x hx
    have hxprod : x ∈ (D : Set (FreeAmalgam Rg)) * (Z Rg t.edge : Set (FreeAmalgam Rg)) := by
      rw [←coe_mul_of_right_le_normalizer_left D (Z Rg t.edge) hCN]
      exact hspan hx
    obtain ⟨d,hd,c,hc,hdc⟩ := hxprod
    have hcspan : c ∈ H ⊔ D := by
      have he : c = d⁻¹*x := by rw [←hdc]; simp
      rw [he]
      exact (H ⊔ D).mul_mem ((H ⊔ D).inv_mem (mem_sup_right hd)) hx
    rw [←hdc]
    exact (D ⊔ I).mul_mem (mem_sup_left hd) (mem_sup_right ⟨hcspan,hc⟩)
  exact le_sup_left.trans (hdecomp.trans (sup_le_sup_left (le_inf hIU hIt) D))

include h e hz hk in
/-- The nonnormalizing alternative is excluded above distance six on the
original Borel graph: the restricted double-kernel commutator vanishes. -/
theorem borel_three_shift_normalization
    (hb : 6 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let K := Z Rg t.start ⊓ Q Rg v
    ⁅K,Z Rg z ⊓ Q Rg r.start⁆ = ⊥ ∧
      Z Rg z ≤ normalizer ((K ⊔ Z Rg r.start : Subgroup (FreeAmalgam Rg)) : Set _) ∧
      Q Rg r.start ≤ edgeOffenderJoin t.start t.edge := by
  have hb4 : 4 < sourceDistance h := by omega
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z Rg t.start ⊓ Q Rg v
  let F := Z Rg z ⊓ Q Rg r.start
  have ht := two_borel_backward_shifts_small_moving h e hz hk hb4 q.path r t
  have hsmall : (Q Rg v).relIndex (Z Rg t.start) < 4 := by rw [ht.2.1]; decide
  have htcol : color Rg t.edge = true := by
    have hh := adjacent_color_ne Rg t.adjacent_start
    rw [r.path.start_color] at hh
    cases he : color Rg t.edge <;> simp_all
  have hFG : F ≤ stabilizer Rg t.start :=
    (inf_le_right.trans (Q_le_adjacent_h Rg htcol t.adjacent_start)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg t.adjacent_shift))
  have hzero : ⁅K,F⁆ = ⊥ := borel_critical_kernel_fixed_of_line_mod_center h e hz hk
    t.path hsmall F hFG (borel_three_shift_whole_seed_alignment h e hz hk hb u hR p q r t)
  have hnorm : Z Rg z ≤ normalizer ((K ⊔ Z Rg r.start : Subgroup (FreeAmalgam Rg)) : Set _) := by
    by_contra hn
    have hline := (borel_three_shift_restricted_kernel h e hz hk hb4 u hR p q r t).2.2.2.2 hn
    have hcard : Nat.card (⁅K,F⁆ : Subgroup (FreeAmalgam Rg)) = 2 := hline.1
    rw [hzero,Subgroup.card_bot] at hcard
    omega
  exact ⟨hzero,hnorm,(borel_three_shift_mover_comparison h e hz hk hb4 u hR p q r t).2 hnorm |>.1⟩

include h e hz hk in
/-- The whole endpoint omega group normalizes the restricted-kernel join
above distance six, including its component-fixed central factor. -/
theorem borel_three_shift_full_omega_normalization
    (hb : 6 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path)
    (t : BorelBackwardShift (h := h) r.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    X Rg z ≤ normalizer (((Z Rg t.start ⊓ Q Rg v) ⊔ Z Rg r.start :
      Subgroup (FreeAmalgam Rg)) : Set _) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let K := Z Rg t.start ⊓ Q Rg v
  let N := K ⊔ Z Rg r.start
  have hb4 : 4 < sourceDistance h := by omega
  have hb2 : 2 < sourceDistance h := by omega
  have hnorm := (borel_three_shift_normalization h e hz hk hb u hR p q r t).2.1
  have hNK := (borel_three_shift_restricted_kernel h e hz hk hb4 u hR p q r t).2.2.2.1
  have hr := two_borel_backward_shifts_small_moving h e hz hk hb4 p q r
  let pr : CriticalPath Rg (sourceGeometry h) z r.start :=
    CriticalPath.ofPair r.path.end_color (reverse_pair h e r.path)
  have hs : (Q Rg r.start).relIndex (Z Rg z) < 4 := by rw [hr.2.2.1]; decide
  rcases small_critical_omega_generation_or_control_at h e hz hk pr hs with hgen | hc
  · have heq := omega_eq_seed_of_central_generation h z r.path.end_color hgen
    change X Rg z ≤ normalizer (N : Set (FreeAmalgam Rg))
    rw [heq]
    exact hnorm
  · have hKG : K ≤ stabilizer Rg z := inf_le_right.trans (terminal_last_edge_inputs h r.path hb2).2.2
    have hKQ : K ≤ Q Rg r.start :=
      (inf_le_left.trans (terminal_neighbor_seed_radius t.adjacent_start t.adjacent_shift)).trans
        ((sourceGeometry h).V_le_Q hb2 r.start r.path.start_color)
    have hXN : X Rg z ≤ normalizer (Z Rg r.start : Set (FreeAmalgam Rg)) :=
      (critical_X_le_vertex h e z r.path.end_color r.start pr.critical).trans
        (Z_normalized Rg r.start)
    have hRZ : ⁅X Rg z,Z Rg r.start⁆ ≤ Z Rg r.start := le_normalizer_iff_commutator_le_right.mp hXN
    have hKR : K ≤ centralizer ((⁅X Rg z,Z Rg r.start⁆ :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) :=
      (hKQ.trans (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg r.start r.path.start_color)))).trans (centralizer_le hRZ)
    have hbound : ⁅X Rg z,K⁆ ≤ N := by
      rw [commutator_comm]
      exact (hc K hKG hKR).trans (sup_le (hRZ.trans le_sup_right)
        ((le_normalizer_iff_commutator_le_left.mp hNK).trans le_sup_left))
    change X Rg z ≤ normalizer (N : Set (FreeAmalgam Rg))
    apply le_normalizer_iff.mpr
    intro x hx y hy
    have hm : N.map (MulAut.conj x).toMonoidHom ≤ N := by
      rw [show N = K ⊔ Z Rg r.start from rfl,Subgroup.map_sup]
      refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hXN hx)).le.trans le_sup_right)
      rintro _ ⟨k,hkK,rfl⟩
      have hh := N.mul_mem (hbound (commutator_mem_commutator hx hkK)) (mem_sup_left hkK)
      simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
    exact hm (mem_map_of_mem (MulAut.conj x).toMonoidHom hy)

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
