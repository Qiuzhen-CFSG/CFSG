module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticCommutator
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalRootKernel

/-!
# The original secondary commutator is trivial

The original distance-two natural root marking is now constructed, including
its exact kernel Q_a intersect Q_z. Applying the explicit Sylow calculation
and original center-freeness proves [R_a,Q_a]=1, with no commutator or action
callback. The existing contradiction therefore needs only distance two and
the preceding secondary movement claim. Both claims remain genuine source
obligations; this is not yet SymplecticPlaneRecognition.

The generation-two consumer and GenerationTwoSymplecticMovementConsumers
apply this reduction to both original tensor assemblies.
Source: MS93 (3.6), printed p.871; Aschbacher--Smith9.3.10, pp.734--735.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
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

/-- The original distance-two secondary commutator vanishes. The restricted
natural action and its exact opposite-kernel intersection are constructed. -/
theorem original_secondary_commutator_eq_bot
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {a t z : Vertex R}, CriticalPath R geometry a z → Adjacent R a t → Adjacent R z t →
        ⁅secondaryOrbit R a (secondarySeed R a t z),Q R a⁆ = ⊥ := by
  intro R geometry hb a t z path hat hzt
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
    (c.graph_core_nonfrattini eK a path.start_color)
  have hFc : Nat.card F.Carrier = 4 := by rw [F.card_eq,hF]; norm_num
  exact c.original_secondary_commutator_eq_bot_of_root_action eK hFc geometry hb path hat hzt f hk hroot

/-- The actual secondary commutator premise has been discharged on the
original geometry; only the preceding movement claim is supplied here. -/
theorem false_of_original_secondary_movement_only
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {a t z : Vertex R}, CriticalPath R geometry a z → Adjacent R a t → Adjacent R z t →
        (¬ ⁅secondaryOrbit R a (secondarySeed R a t z),Ltilde R a⁆ ≤ Z R a) → False := by
  intro R geometry hb a t z path hat hzt hmove
  apply c.false_of_original_secondary_movement eK geometry hb path hat hzt _ hmove
  rw [c.original_secondary_commutator_eq_bot eK geometry hb path hat hzt]
  exact bot_le
end GenerationTwoOvergroup

/-- Remaining original source obligations: distance two and secondary movement.
The secondary commutator and its literal natural-action marking are proved. -/
@[expose] def SymplecticSecondaryMovementSource (m : SourceA5TensorModel D e) : Prop :=
  ∀ (c : m.GenerationTwoOvergroup),
    ((pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) →
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∃ (geometry : Geometry R), geometry.b R = 2 ∧
      ∃ (t z : Vertex R) (_path : CriticalPath R geometry (alpha R) z),
        Adjacent R (alpha R) t ∧ Adjacent R z t ∧
        ¬ ⁅secondaryOrbit R (alpha R) (secondarySeed R (alpha R) t z),Ltilde R (alpha R)⁆ ≤ Z R (alpha R)

theorem symplecticSecondarySource_of_movement_source
    (hsource : m.SymplecticSecondaryMovementSource) : m.SymplecticSecondarySource := by
  intro c eK
  obtain ⟨geometry,hb,t,z,path,hat,hzt,hmove⟩ := hsource c eK
  refine ⟨geometry,hb,t,z,path,hat,hzt,?_,hmove⟩
  rw [c.original_secondary_commutator_eq_bot eK geometry hb path hat hzt]
  exact bot_le

theorem symplecticPlaneRecognition_of_secondary_movement_source
    (hsource : m.SymplecticSecondaryMovementSource) : m.SymplecticPlaneRecognition :=
  symplecticPlaneRecognition_of_secondary_source (symplecticSecondarySource_of_movement_source hsource)

theorem false_of_generationTwo_source_inputs_of_secondary_movement_source
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hnormal : m.NonzeroCoreCartanNormalization)
    (hzero : m.ZeroCoreLineCentralization) (hcontain : A5PairContainment G)
    (hrows : m.LinearAndG2Exclusion) (hsource : m.SymplecticSecondaryMovementSource) : False :=
  m.false_of_generationTwo_source_inputs hout hnormal hzero hcontain hrows
    (symplecticPlaneRecognition_of_secondary_movement_source hsource)
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
