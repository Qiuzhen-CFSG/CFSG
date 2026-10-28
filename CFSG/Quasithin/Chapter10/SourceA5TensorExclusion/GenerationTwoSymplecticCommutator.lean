module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticSecondary
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.CoreReconstruction.RootCommutator

/-!
# The original secondary commutator and its restricted natural action

The maximal secondary seed lies in the original two-core. Its local orbit
therefore has commutator contained in the original Z-layer, by normal
generation. A marking of that two-core on the opposite natural layer,
with exact kernel Q_a intersect Q_z and transvection image of Z_a, makes
the commutator image trivial by the actual symplectic Sylow calculation.
The faithful simple quotient and center-freeness then kill the whole
commutator, including its central kernel.

The final theorem applies this to the existing original secondary-movement
contradiction. The restricted natural marking, critical distance two and
secondary movement remain explicit source obligations. No characteristic
replacement is used, and this is not yet SymplecticPlaneRecognition.
Source: MS93 (3.6), printed p.871; Aschbacher--Smith9.3.10, pp.734--735.
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

/-- The source bound [R_a,Q_a] <= Z_a holds on the original geometry. -/
theorem original_secondary_commutator_le_initial
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {a t z : Vertex R}, CriticalPath R geometry a z → Adjacent R a t → Adjacent R z t →
        ⁅secondaryOrbit R a (secondarySeed R a t z),Q R a⁆ ≤ Z R a := by
  intro R geometry hb a t z path hat hzt
  exact conjugatesIn_commutator_le _ _ _ _
    (c.original_secondary_seed_le_kernel eK geometry hb path hat hzt)
    (Q_normalized R a) (Z_normalized R a)
    (le_trans (show Q R a ≤ stabilizer R a from fun _ hx => hx.1) (Z_normalized R a))
    (((secondarySeed_greatest R geometry path.end_color hzt (by omega)).2.1).trans
      (edge_Z_le_endpoint R path.start_color hat))

/-- The exact source Sylow calculation, with its original natural-action map.
Only Q_a is marked, and the kernel is the actual opposite-kernel intersection. -/
theorem original_secondary_commutator_eq_bot_of_root_action
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {a t z : Vertex R}, CriticalPath R geometry a z → Adjacent R a t → Adjacent R z t →
      ∀ f : Q R a →* Sp F,
        f.ker.map (Q R a).subtype = Q R a ⊓ Q R z →
        (∀ u : Q R a, (u:FreeAmalgam R) ∈ Z R a →
          Module.finrank F (InvolutionTypes.movedSpace (f u)) ≤ 1) →
        ⁅secondaryOrbit R a (secondarySeed R a t z),Q R a⁆ = ⊥ := by
  intro R geometry hb a t z path hat hzt f hkf hroot
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
  let : IsElementaryAbelian 2 (secondarySeed R a t z) :=
    secondarySeed_elementary R geometry path.end_color (show 0 < geometry.b R by omega)
  have hbound := c.original_secondary_commutator_le_initial eK geometry hb path hat hzt
  have hNQ : ⁅secondaryOrbit R a (secondarySeed R a t z),Q R a⁆ ≤ Q R z := by
    have hh := conjugatesIn_commutator_le_marked_kernel (n := 2) hF (by decide)
      (secondarySeed R a t z) (stabilizer R a) (Q R a) (Z R a) hp
      (c.original_secondary_seed_le_kernel eK geometry hb path hat hzt)
      (Q_normalized R a) hbound f hroot
    rw [hkf] at hh
    exact hh.trans inf_le_right
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
  let A := secondaryOrbit R a (secondarySeed R a t z)
  let S := stabilizer R a
  have hAP : A ≤ Q R a := conjugatesIn_le_of_normalized _ _ _
    (c.original_secondary_seed_le_kernel eK geometry hb path hat hzt) (Q_normalized R a)
  have hAS : A ≤ S := hAP.trans (fun _ hx => hx.1)
  have hQS : Q R a ≤ S := fun _ hx => hx.1
  let : (A.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer
    (conjugatesIn_normalized (secondarySeed R a t z) S)
  let : ((Q R a).subgroupOf S).Normal := Q_normal R a
  let N := ⁅A.subgroupOf S,(Q R a).subgroupOf S⁆
  have hNm : N.map S.subtype = ⁅A,Q R a⁆ := by
    rw [map_commutator,map_subgroupOf_eq_of_le hAS,map_subgroupOf_eq_of_le hQS]
  have hn : S ≤ normalizer (⁅A,Q R a⁆ : Subgroup (FreeAmalgam R)) := by
    have hh := N.le_normalizer_map S.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,hNm] at hh
  have hzS : Z R z ≤ S := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant a path.start_color,
      geometry.distance_constant z path.end_color]
  have hzQ : ¬ Z R z ≤ Q R a :=
    (c.original_critical_reverse eK geometry (show 0 < geometry.b R by omega) path).critical.2
  exact normal_central_layer_eq_bot_of_opposite_kernel _
    (hbound.trans_eq (c.original_distance_two_layers eK geometry hb path).1.symm) hNQ hn
    hzS hzQ path.end_color κ hκ hkQ hna hcent
    (c.graph_X_fixed_eq_bot a path.start_color)

/-- This marked original action supplies the secondary commutator premise
of the already checked source contradiction. Movement remains a separate claim. -/
theorem false_of_original_secondary_root_action
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp ChapterB.QuasisimpleSource.BinaryField.four.Carrier)
    {F : Type*} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = 4) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {a t z : Vertex R}, CriticalPath R geometry a z → Adjacent R a t → Adjacent R z t →
      ∀ f : Q R a →* Sp F,
        f.ker.map (Q R a).subtype = Q R a ⊓ Q R z →
        (∀ u : Q R a, (u:FreeAmalgam R) ∈ Z R a →
          Module.finrank F (InvolutionTypes.movedSpace (f u)) ≤ 1) →
        (¬ ⁅secondaryOrbit R a (secondarySeed R a t z),Ltilde R a⁆ ≤ Z R a) → False := by
  intro R geometry hb a t z path hat hzt f hk hroot hmove
  apply c.false_of_original_secondary_movement eK geometry hb path hat hzt _ hmove
  rw [c.original_secondary_commutator_eq_bot_of_root_action eK hF geometry hb path hat hzt f hk hroot]
  exact bot_le
end GenerationTwoOvergroup
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
