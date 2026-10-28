module
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubeRadiusPlane
public import Theory.Representation.NormalElementaryQuotient.SubgroupSpaceTransport
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.NaturalMovement

/-!
# Full-cover critical movement modulo the central attachment

The natural quotient detects the movement of the whole midpoint core of a
large critical path. Lifting its symplectic displacement estimate retains
the entire central kernel of either moving cover. Thus the full movement
is contained in the critical commutator joined with the central part of the
starting moving cover. This records the precise additional term that must
be controlled on the order-thirty-two cover.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), (5.2)(ii), (5.12)(2), printed pp.867,914--915,925--926.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.GroupTheory Representation.NormalElementaryQuotient
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


/-- Natural quotient control, retaining the full central kernel of either cover. -/
theorem quadratic_cover_control_mod_center
    (A Y : Subgroup d.overgroup)
    (hcard : 4 ≤ Nat.card (A.map s.projection))
    (hAA : ⁅replacementMoved d,A⁆ ≤ centralizer (A : Set d.overgroup))
    (hAY : ⁅replacementMoved d,A⁆ ≤ centralizer (Y : Set d.overgroup)) :
    ⁅replacementMoved d,Y⁆ ≤ ⁅replacementMoved d,A⁆ ⊔
      (replacementMoved d ⊓ center d.overgroup) := by
  let := replacementMoved_normal h d
  let : IsElementaryAbelian 2 (A.map s.projection) :=
    elementary_of_faithful_quadratic (naturalRepresentation (Fin 6))
      (naturalRepresentation_injective (Fin 6) (by decide)) _
      (image_quadratic_of_commutator s A hAA)
  let π := coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d)
  have hmap (B : Subgroup d.overgroup) :
      (NormalElementaryQuotient.commutatorSpace (replacementMoved d) B).map π =
        subspaceCommutator (naturalRepresentation (Fin 6)) ⊤ (B.map s.projection) := by
    rw [NormalElementaryQuotient.commutatorSpace_eq (replacementMoved d) s.projection
      s.surjective (s.projection_kernel.trans (moved_centralizer s).symm)]
    have hh := subspaceCommutator_map_embedding (naturalRepresentation (Fin 6))
      (coverAction s) (MonoidHom.id S) π (fun g v => (coverMap_equivariant s g v).symm)
      (B.map s.projection) ⊤
    rw [Submodule.map_top,LinearMap.range_eq_top.mpr (coverMap_surjective
      (h := h) (e := e) (hz := hz) (hn := hn) (d := d)),Subgroup.map_id] at hh
    exact hh.symm
  have hmaple :
      (NormalElementaryQuotient.commutatorSpace (replacementMoved d) Y).map π ≤
        (NormalElementaryQuotient.commutatorSpace (replacementMoved d) A).map π := by
    rw [hmap Y,hmap A]
    exact natural_moved_control _ _ hcard (image_quadratic_of_commutator s A hAA)
      (image_centralizes_moved s A Y hAY)
  have hker : π.ker = subgroupSpace (replacementMoved d)
      (replacementMoved d ⊓ center d.overgroup) := by
    ext v
    change coverProjection h e hz hn d v.toMul = 1 ↔
      ((v.toMul : d.overgroup) ∈ replacementMoved d ∧
        (v.toMul : d.overgroup) ∈ center d.overgroup)
    rw [←MonoidHom.mem_ker,coverProjection_kernel_center s]
    simp only [Subgroup.mem_comap,v.toMul.property,true_and]
    rfl
  have hspaces := Submodule.map_le_iff_le_comap.mp hmaple
  rw [Submodule.comap_map_eq,hker] at hspaces
  have hwhole (B : Subgroup d.overgroup) :
      NormalElementaryQuotient.commutatorSpace (replacementMoved d) B =
        subgroupSpace (replacementMoved d) ⁅replacementMoved d,B⁆ := rfl
  rw [hwhole Y,hwhole A,←subgroupSpace_sup (replacementMoved d)
    (commutator_le_left _ _) inf_le_left] at hspaces
  intro x hx
  exact hspaces (show Additive.ofMul (⟨x,(commutator_le_left _ _) hx⟩ : replacementMoved d) ∈
    subgroupSpace (replacementMoved d) ⁅replacementMoved d,Y⁆ from hx)

include s in
private theorem embedded_quadratic_control_mod_center
    {H : Type*} [Group H] (i : d.overgroup →* H) (hi : Function.Injective i)
    (A Y : Subgroup H)
    (hA : A ≤ i.range) (hY : Y ≤ i.range)
    (hcard : 4 ≤ ((pCore 2 d.overgroup).map i).relIndex A)
    (hAA : ⁅(replacementMoved d).map i,A⁆ ≤ centralizer (A : Set H))
    (hAY : ⁅(replacementMoved d).map i,A⁆ ≤ centralizer (Y : Set H)) :
    ⁅(replacementMoved d).map i,Y⁆ ≤ ⁅(replacementMoved d).map i,A⁆ ⊔
      (((replacementMoved d) ⊓ center d.overgroup).map i) := by
  let A₀ := A.comap i
  let Y₀ := Y.comap i
  have hmA : A₀.map i = A := map_comap_eq_self hA
  have hmY : Y₀.map i = Y := map_comap_eq_self hY
  have hcard₀ : 4 ≤ Nat.card (A₀.map s.projection) := by
    rw [←hmA,relIndex_map_map_of_injective _ _ hi,←s.projection_kernel,relIndex_ker] at hcard
    exact hcard
  have hfix (B : Subgroup H)
      (hc : ⁅(replacementMoved d).map i,A⁆ ≤ centralizer (B : Set H)) :
      ⁅replacementMoved d,A₀⁆ ≤ centralizer (B.comap i : Set d.overgroup) := by
    intro x hx b hb
    apply hi
    simp only [map_mul]
    apply hc
    · rw [←hmA,←map_commutator]
      exact mem_map_of_mem i hx
    · exact hb
  have hh := map_mono (f := i) (quadratic_cover_control_mod_center s A₀ Y₀ hcard₀
    (hfix A hAA) (hfix Y hAY))
  rwa [map_commutator,Subgroup.map_sup,map_commutator,hmA,hmY] at hh


include s in
/-- On either full cover, the whole midpoint-core movement is in the critical
commutator times the starting cover's central kernel, with the literal path retained. -/
theorem large_midpoint_movement_le_commutator_sup_center
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    ⁅Z d.radical a,Q d.radical (p.walk.getVert 2)⁆ ≤
      ⁅Z d.radical a,Z d.radical z⁆ ⊔
        (U d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hat : Adjacent d.radical a t := by
    apply (cosetGraph_adj d.radical _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    exact Bool.eq_true_of_not_eq_false (Ne.symm hh)
  have hPc : Q d.radical c ≤ Q d.radical t := Q_le_adjacent_h d.radical ht hct
  have hAz : Z d.radical z ≤ Q d.radical c := by
    apply Z_le_Q_of_dist_lt d.radical z ((replacementGeometry h d).exists_critical z p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end,hl]
    exact show 2 < replacementDistance h d by omega
  rw [seed_commutator_eq_moving (h := h) (e := e) (hz := hz) p.start_color hat _ hPc]
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a p.start_color
  have hTG : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 _ (adjacent_symm d.radical hat)
  have hAY : ⁅U d.radical a,Z d.radical z⁆ ≤
      centralizer (Q d.radical c : Set (FreeAmalgam d.radical)) :=
    (commutator_mono (DistanceEight.U_le_Z d.radical a) hAz).trans
      (large_midpoint_core_quadratic s hc hb p hlarge)
  have hAA := hAY.trans (centralizer_le hAz)
  have hcontrol := embedded_quadratic_control_mod_center s i hi
    (Z d.radical z) (Q d.radical c)
    ((hAz.trans hPc).trans hTG |>.trans_eq hir.symm)
    (hPc.trans hTG |>.trans_eq hir.symm)
    (hiQ.symm ▸ reverse_critical_image_four_le s hc (replacementDistance_pos h d) p hlarge)
    (hiU.symm ▸ hAA) (hiU.symm ▸ hAY)
  have hmC : (replacementMoved d ⊓ center d.overgroup).map i =
      U d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    have hh := map_inf_centralizer_of_injective i hi (replacementMoved d) ⊤
    simpa only [←MonoidHom.range_eq_map,hir,hiU,coe_top,centralizer_univ] using hh.symm
  rw [hiU,hmC] at hcontrol
  exact hcontrol.trans (sup_le_sup_right
    (commutator_mono (DistanceEight.U_le_Z d.radical a) le_rfl) _)


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
