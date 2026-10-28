module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalPath
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardRigidity

/-!
# Critical-line actor control with the full central attachment

If an actor's displacement on the entire moving cover lies in a critical
transposition line times the cover's central attachment, the faithful natural
quotient places its image in that same transposition group. The symplectic
pairing converts containment of moved spaces into the reverse containment
of fixed spaces. Lifting back through the original quotient gives containment
in the core times the critical actor, without discarding the central line
of the order-thirty-two cover.

The actual critical-pair application then shows that this actor fixes the
whole critical kernel. SylowTerminalNormalization uses this conclusion to
eliminate the nonnormalizing alternative in MS93 (5.10) above distance six.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3)(ii) and the last paragraph of printed p.922.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- The whole-cover displacement modulo its central attachment detects
containment in the actual core times the critical actor. -/
theorem cover_actor_le_of_critical_line_mod_center
    (A B : Subgroup d.overgroup)
    (hne : ¬ A ≤ pCore 2 d.overgroup)
    (hindex : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2)
    (hcomm : ⁅replacementMoved d,B⁆ ≤ ⁅replacementMoved d,A⁆ ⊔
      (replacementMoved d ⊓ center d.overgroup)) :
    B ≤ pCore 2 d.overgroup ⊔ A := by
  let := replacementMoved_normal h d
  let U := replacementMoved d
  let f := coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)
  let W := subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (A.map s.projection)
  have hk := s.projection_kernel.trans (moved_centralizer s).symm
  have hm (D : Subgroup d.overgroup) :
      (NormalElementaryQuotient.commutatorSpace U D).map f =
      subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (D.map s.projection) := by
    rw [NormalElementaryQuotient.commutatorSpace_eq U s.projection s.surjective hk]
    change (subspaceCommutator (coverAction s) ⊤ (D.map s.projection)).map f = _
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (coverAction s) (MonoidHom.id _) f
      (fun g v => (coverMap_equivariant s g v).symm) (D.map s.projection) ⊤
    have hf : f.range = ⊤ := LinearMap.range_eq_top.mpr
      (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
    simpa only [Submodule.map_top,hf,map_id] using hh.symm
  have hwhole (D : Subgroup d.overgroup) :
      NormalElementaryQuotient.subgroupSpace U ⁅U,D⁆ =
        NormalElementaryQuotient.commutatorSpace U D := by
    rfl
  have hspace : NormalElementaryQuotient.commutatorSpace U B ≤ W.comap f := by
    have hle : NormalElementaryQuotient.subgroupSpace U ⁅U,B⁆ ≤
        NormalElementaryQuotient.subgroupSpace U (⁅U,A⁆ ⊔ (U ⊓ center d.overgroup)) :=
      fun _ hv => hcomm hv
    rw [NormalElementaryQuotient.subgroupSpace_sup U (commutator_le_left U A) inf_le_left,
      hwhole B,hwhole A] at hle
    apply hle.trans
    apply sup_le
    · exact Submodule.map_le_iff_le_comap.mp (hm A).le
    · intro v hv
      have hv0 : coverProjection h e hz hn d v.toMul = 1 := by
        apply MonoidHom.mem_ker.mp
        rw [coverProjection_kernel_center s]
        exact hv.2
      have hf0 : f v = 0 := congrArg Multiplicative.toAdd hv0
      change f v ∈ W
      rw [hf0]
      exact W.zero_mem
  have hsmall : fixedCodim (coverAction s) (A.map s.projection) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim U s.projection s.surjective hk] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction s) (naturalRepresentation (Fin 6))
      f (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_equivariant s) (A.map s.projection)).trans hsmall
  have hnA : A.map s.projection ≠ ⊥ := by
    intro he
    exact hne (s.projection_kernel ▸ (map_eq_bot_iff A).mp he)
  have him : B.map s.projection ≤ A.map s.projection :=
    small_actor_le_of_moved_le _ _ hnA hnat
      ((hm B).symm ▸ Submodule.map_le_iff_le_comap.mpr hspace)
  have hle := (le_comap_map s.projection B).trans (comap_mono him)
  rw [Subgroup.comap_map_eq,s.projection_kernel] at hle
  exact hle.trans_eq (sup_comm _ _)


include s in
/-- On the actual critical pair, an actor whose whole-seed displacement is
in the critical line times the full central attachment fixes the whole kernel. -/
theorem small_critical_actor_le_of_line_mod_center
    (hc : DistanceTwo.CentralLayer d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (Y : Subgroup (FreeAmalgam d.radical)) (hY : Y ≤ stabilizer d.radical a)
    (hcomm : ⁅Z d.radical a,Y⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ ⊔
      (U d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))) :
    Y ≤ Q d.radical a ⊔ Z d.radical a' ∧
      ⁅Z d.radical a ⊓ Q d.radical a',Y⁆ = ⊥ := by
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a p.start_color
  have hAG : Z d.radical a' ≤ stabilizer d.radical a :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
      (by rw [(replacementGeometry h d).distance_constant _ p.start_color]
          exact replacementDistance_pos h d) p.critical
  let A := (Z d.radical a').comap i
  let B := Y.comap i
  have hmA : A.map i = Z d.radical a' := map_comap_eq_self (hAG.trans_eq hir.symm)
  have hmB : B.map i = Y := map_comap_eq_self (hY.trans_eq hir.symm)
  have hmC : (replacementMoved d ⊓ center d.overgroup).map i =
      U d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    have hh := map_inf_centralizer_of_injective i hi (replacementMoved d) ⊤
    simpa only [←MonoidHom.range_eq_map,hir,hiU,coe_top,centralizer_univ] using hh.symm
  have hD : (⁅replacementMoved d,A⁆).map i = ⁅Z d.radical a,Z d.radical a'⁆ := by
    rw [map_commutator,hiU,hmA,small_critical_moving_commutator_eq s hc p hsmall]
  have hnA : ¬ A ≤ pCore 2 d.overgroup := by
    intro hh
    have he := map_mono (f := i) hh
    rw [hmA,hiQ] at he
    exact (critical_reverse_pair s hc p).2 he
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  have hCA : Q d.radical a' ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color))
  have hidx : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    rw [←inf_relIndex_right,inf_comm,←relIndex_map_map_of_injective _ _ hi,
      ←map_inf_centralizer_of_injective i hi,hiU,hmA,inf_relIndex_left]
    exact ((relIndex_le_of_le_left hCA index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a) index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).1
  have hcontrol : ⁅replacementMoved d,B⁆ ≤ ⁅replacementMoved d,A⁆ ⊔
      (replacementMoved d ⊓ center d.overgroup) := by
    apply (map_le_map_iff_of_injective hi).mp
    rw [Subgroup.map_sup,hD,hmC,map_commutator,hiU,hmB]
    exact (commutator_mono (DistanceEight.U_le_Z d.radical a) le_rfl).trans hcomm
  have hle := map_mono (f := i) (cover_actor_le_of_critical_line_mod_center s A B hnA hidx hcontrol)
  rw [hmB,Subgroup.map_sup,hiQ,hmA] at hle
  refine ⟨hle,commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp (hle.trans ?_))⟩
  apply sup_le
  · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color))).trans (centralizer_le inf_le_left)
  · exact le_centralizer_iff.mp (inf_le_right.trans hCA)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
