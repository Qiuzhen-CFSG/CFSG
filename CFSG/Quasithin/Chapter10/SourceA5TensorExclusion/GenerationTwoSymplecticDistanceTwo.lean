module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticSmallMovers
public import Theory.GroupTheory.Commutator.NilpotentInduction

/-!
# Exclusion of original critical distance two

The original Q_a normalizes the opposite Z_z at distance two, and their
join is a finite two-group. Intersect Z_z with its upper central series.
The small-commutator theorem puts every intersection in Z_a, inductively.
Nilpotence then puts all of Z_z in Z_a, contradicting the reversed critical
pair. The restricted symplectic action and its kernel are constructed from
the original source hypotheses; no flag or movement premise remains.

The distance-two source reduction is still open. The conditional assembly
retains precisely that original-geometry premise and applies the contradiction
to the existing original-plane recognition consumer. This does not establish
SymplecticPlaneRecognition unconditionally.
Source: MS93 (3.6), pp.870--871; Aschbacher--Smith 9.3.10, pp.734--735.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.CoreReconstruction
open ChapterC.RankTwo.Sp4Four.SourceComparison Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e}
namespace GenerationTwoOvergroup
variable (c : m.GenerationTwoOvergroup)

theorem original_distance_ne_two
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R ≠ 2 := by
  intro R geometry hb
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := R) (geometry := geometry) (a := alpha R) rfl
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hc,hsq,hQne⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      BinaryField.four.card_eq eK c.fitting_center.1 c.component_product.2.2.2
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hself : centralizer (pCore 2 c.M : Set c.M) ≤ pCore 2 c.M := by
    simpa only [c.fitting_center.1] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := c.M))
  have hne : R ≠ ⊥ := fun hr => hQne (le_bot_iff.mp (hr ▸ hodd.twoCore_le))
  obtain ⟨F,hF,f,hk,hroot⟩ := original_kernel_root_action R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) hc hBC hsq path hb
    (c.graph_core_nonfrattini eK _ rfl)
  have hFc : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  have hpos : 0 < geometry.b R := by omega
  have hdist : (cosetGraph R).dist (alpha R) z = 2 :=
    path.critical.1.trans ((geometry.distance_constant _ rfl).trans hb)
  have hn : Q R (alpha R) ≤ normalizer (Z R z) :=
    (Q_le_stabilizer_of_dist_two R _ z rfl hdist).trans (Z_normalized R z)
  have hp := Q_isPGroup R hodd.isPGroup hodd.twoCore_le (alpha R) rfl
  let := geometry.Z_elementary hpos z path.end_color
  let N := Z R z ⊔ Q R (alpha R)
  have hzS : Z R z ≤ stabilizer R (alpha R) := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant _ rfl,
      geometry.distance_constant z path.end_color]
  let := finite_stabilizer R (alpha R)
  let : Finite N := Finite.of_injective
    (inclusion (sup_le hzS (show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1)))
    (inclusion_injective _)
  let : Group.IsNilpotent N :=
    ((IsElementaryAbelian.isPGroup 2 (Z R z)).to_sup_of_normal_left' hp hn).isNilpotent
  have hle : Z R z ≤ Z R (alpha R) := le_of_nilpotent_commutator_induction
    N (Z R z) (Q R (alpha R)) (Z R (alpha R)) le_sup_left le_sup_right hn
    (fun Y hYZ hcomm =>
      (c.original_small_mover_central_of_root_action eK hFc geometry hb path Y hYZ hcomm f hk hroot).2)
  exact (c.original_critical_reverse eK geometry hpos path).critical.2
    (hle.trans ((geometry.omega_bound _ rfl (by rwa [geometry.distance_constant _ rfl])).trans
      (omegaCenter_le _)))
end GenerationTwoOvergroup
end CFSG.Quasithin.Chapter10.SourceA5TensorModel

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open Chapter3.Section02 ChapterB.QuasisimpleSource Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e}

theorem GenerationTwoOvergroup.original_geometry_four_le (c : m.GenerationTwoOvergroup)
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 ≤ geometry.b R := by
  intro R geometry
  obtain ⟨g,hpos,heven⟩ := c.exists_positive_even_geometry eK
  have hn := c.original_distance_ne_two eK geometry
  change geometry.b R ≠ 2 at hn
  change 4 ≤ geometry.b R
  change 0 < geometry.b R at hpos
  obtain ⟨n,hn'⟩ := heven
  change geometry.b R = n+n at hn'
  omega

/-- The sole remaining premise of the original distance route. It concerns
exactly the original Sylow holomorph geometry, not a characteristic replacement. -/
@[expose] def SymplecticDistanceTwoSource (m : SourceA5TensorModel D e) : Prop :=
  ∀ c : m.GenerationTwoOvergroup,
    ((pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) →
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∃ geometry : Geometry R, geometry.b R = 2

/-- All secondary-action and movement premises are now discharged. -/
theorem symplecticPlaneRecognition_of_distance_two_source
    (hsource : m.SymplecticDistanceTwoSource) : m.SymplecticPlaneRecognition := by
  apply symplecticPlaneRecognition_of_core_bound
  intro c eK
  obtain ⟨geometry,hb⟩ := hsource c eK
  exact (c.original_distance_ne_two eK geometry hb).elim

theorem false_of_generationTwo_source_inputs_of_distance_two_source
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hnormal : m.NonzeroCoreCartanNormalization)
    (hzero : m.ZeroCoreLineCentralization) (hcontain : A5PairContainment G)
    (hrows : m.LinearAndG2Exclusion) (hsource : m.SymplecticDistanceTwoSource) : False :=
  m.false_of_generationTwo_source_inputs hout hnormal hzero hcontain hrows
    (symplecticPlaneRecognition_of_distance_two_source hsource)
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
