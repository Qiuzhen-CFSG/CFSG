module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticRootAction

/-!
# Subgroups with small commutator in the original opposite layer

At a distance-two critical pair, let Y lie in Z_z with [Y,Q_a] contained
in Z_a. Non-Frattini core movement forces Y into Q_a. Its local conjugate
span still has commutator in Z_a. The literal symplectic root action kills
that commutator modulo Q_z; normality and center-freeness kill its full
central attachment. Thus Y centralizes Q_a and lies in X_a = Z_a.

This extends the secondary-seed calculation to every such Y. The next
module uses it for successive intersections with a nilpotent central series,
so it needs no secondary flag or movement assertion.
Source: MS93 (3.6), pp.870--871; Aschbacher--Smith 9.3.10, pp.734--735.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.CoreReconstruction
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e}
namespace GenerationTwoOvergroup
variable (c : m.GenerationTwoOvergroup)

theorem original_small_mover_central_of_root_action
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {a z : Vertex R}, CriticalPath R geometry a z →
      ∀ Y : Subgroup (FreeAmalgam R), Y ≤ Z R z → ⁅Y,Q R a⁆ ≤ Z R a →
      ∀ f : Q R a →* Sp F,
        f.ker.map (Q R a).subtype = Q R a ⊓ Q R z →
        (∀ u : Q R a, (u:FreeAmalgam R) ∈ Z R a →
          Module.finrank F (InvolutionTypes.movedSpace (f u)) ≤ 1) →
        ⁅Y,Q R a⁆ = ⊥ ∧ Y ≤ Z R a := by
  intro R geometry hb a z path Y hYZ hcomm f hkf hroot
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,_,_,_⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      ChapterB.QuasisimpleSource.BinaryField.four.card_eq eK c.fitting_center.1
      c.component_product.2.2.2
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hp := Q_isPGroup R hodd.isPGroup hodd.twoCore_le a path.start_color
  obtain ⟨i,hi,hir,hiL,_,hiQ⟩ := vertex_coordinates_with_kernel R
    hodd.isPGroup hodd.twoCore_le path.start_color
  let κ := ElementaryMovedCover.embeddedQuotient q i hi (stabilizer R a) hir
  have hκ : Function.Surjective κ :=
    ElementaryMovedCover.embeddedQuotient_surjective q i hi _ hir (QuotientGroup.mk'_surjective _)
  have hkQ : κ.ker.map (stabilizer R a).subtype = Q R a := by
    rw [ElementaryMovedCover.embeddedQuotient_kernel,QuotientGroup.ker_mk']
    exact hiQ
  have hL : ((Ltilde R a).subgroupOf (stabilizer R a)).map κ = (pResidual 2 c.M).map q := by
    rw [←hiL]
    exact ElementaryMovedCover.embeddedQuotient_subgroup q i hi _ hir _
  let : (((Ltilde R a).subgroupOf (stabilizer R a)).map κ).Normal := hL ▸ inferInstance
  let : IsSimpleGroup (((Ltilde R a).subgroupOf (stabilizer R a)).map κ) := hL ▸ inferInstance
  have hna : ¬ IsMulCommutative (((Ltilde R a).subgroupOf (stabilizer R a)).map κ) := by
    rw [hL]
    exact Group.IsPerfect.not_isMulCommutative _
  have hcent : centralizer (((Ltilde R a).subgroupOf (stabilizer R a)).map κ :
      Set (c.M ⧸ pCore 2 c.M)) = ⊥ := by
    rw [hL]; exact hBC
  have hzS : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  have hYX : ⁅Y,Q R a⁆ ≤ X R a :=
    hcomm.trans_eq (c.original_distance_two_layers eK geometry hb path).1.symm
  have hYQ : Y ≤ Q R a := by
    by_contra hnot
    apply c.graph_core_nonfrattini eK a path.start_color
    apply core_le_frattini_of_local_commutator_le a Y (hYZ.trans hzS) hnot
      hp κ hκ hkQ hna hcent
    rw [commutator_comm]
    exact hYX.trans le_sup_right
  let := geometry.Z_elementary (show 0 < geometry.b R by omega) z path.end_color
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_le hYZ
  have hbound : ⁅conjugatesIn Y (stabilizer R a),Q R a⁆ ≤ Z R a :=
    conjugatesIn_commutator_le Y (stabilizer R a) (Q R a) (Z R a)
      hYQ (Q_normalized R a) (Z_normalized R a)
      ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Z_normalized R a)) hcomm
  have hNQ : ⁅conjugatesIn Y (stabilizer R a),Q R a⁆ ≤ Q R z := by
    have hh := conjugatesIn_commutator_le_marked_kernel (n := 2) hF (by decide)
      Y (stabilizer R a) (Q R a) (Z R a) hp hYQ (Q_normalized R a) hbound f hroot
    rw [hkf] at hh
    exact hh.trans inf_le_right
  let A := conjugatesIn Y (stabilizer R a)
  let S := stabilizer R a
  have hAP : A ≤ Q R a := conjugatesIn_le_of_normalized _ _ _
    hYQ (Q_normalized R a)
  have hAS : A ≤ S := hAP.trans (fun _ hx => hx.1)
  have hQS : Q R a ≤ S := fun _ hx => hx.1
  let : (A.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer
    (conjugatesIn_normalized Y S)
  let : ((Q R a).subgroupOf S).Normal := Q_normal R a
  let N := ⁅A.subgroupOf S,(Q R a).subgroupOf S⁆
  have hNm : N.map S.subtype = ⁅A,Q R a⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le hAS,map_subgroupOf_eq_of_le hQS]
  have hn : S ≤ normalizer (⁅A,Q R a⁆ : Subgroup (FreeAmalgam R)) := by
    have hh := N.le_normalizer_map S.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hNm] at hh
  have hzQ : ¬ Z R z ≤ Q R a :=
    (c.original_critical_reverse eK geometry (show 0 < geometry.b R by omega) path).critical.2
  have hzero : ⁅A,Q R a⁆ = ⊥ := normal_central_layer_eq_bot_of_opposite_kernel _
    (hbound.trans_eq (c.original_distance_two_layers eK geometry hb path).1.symm) hNQ hn
    hzS hzQ path.end_color κ hκ hkQ hna hcent
    (c.graph_X_fixed_eq_bot a path.start_color)

  have hYA : Y ≤ A := by
    change Y ≤ conjugatesIn Y S
    rw [conjugatesIn_eq_conjugateSpan]
    exact le_conjugateSpanBy Y S
  have hyzero : ⁅Y,Q R a⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono hYA le_rfl).trans_eq hzero)
  refine ⟨hyzero,?_⟩
  rw [←(c.original_distance_two_layers eK geometry hb path).1]
  intro y hy
  exact mem_omegaCenter_iff.mpr ⟨hYQ hy,
    elemPow_eq_one_of_isElementaryAbelian y hy,
    (commutator_eq_bot_iff_le_centralizer.mp hyzero) hy⟩

end GenerationTwoOvergroup
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
