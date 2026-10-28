module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticRootAction
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticOriginalLayers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.CoreReconstruction.SecondaryFlag

/-!
# The original critical action is nonquadratic

Quadratic action would place the critical commutator in X_a and force the
whole core into its Frattini-central layer, contradicting the previously
proved original tensor obstruction. The actual secondary flag would instead
make the action quadratic, by the proved secondary commutator identity.

The original distance-two reduction and construction of that simultaneous
flag marking remain source obligations. The conditional consumer below does
not assert SymplecticPlaneRecognition without these premises.
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

theorem original_critical_action_not_quadratic
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {a z : Vertex R}, CriticalPath R geometry a z →
        ⁅⁅Z R z,Q R a⁆,Q R a⁆ ≠ ⊥ := by
  intro R geometry hb a z path hquad
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
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1
    BinaryField.four.card_eq eK c.fitting_center.1 c.component_product.2.2.2
  apply c.graph_core_nonfrattini eK a path.start_color
  apply core_le_frattini_of_critical_commutator_le path (by omega)
    (ChapterC.MSCentralOrbit.edgeCentralizerCondition R hodd.isPGroup hodd.twoCore_le hfaith)
    (Q_isPGroup R hodd.isPGroup hodd.twoCore_le a path.start_color) κ hκ hkQ hna hcent
  rw [commutator_comm]
  exact (critical_commutator_le_X_of_quadratic path hb hquad).trans le_sup_right

end GenerationTwoOvergroup
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.CoreReconstruction
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e}
namespace GenerationTwoOvergroup
variable (c : m.GenerationTwoOvergroup)

theorem false_of_original_secondary_flag
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp BinaryField.four.Carrier)
    {F : Type*} [Field F] :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {a t z : Vertex R}, CriticalPath R geometry a z → Adjacent R a t → Adjacent R z t →
      ∀ (φ : Z R z ≃* Multiplicative (Vector F)) (α : Q R a →* Sp F),
        (∀ p : Q R a, α p ∈ unipotent) →
        (∀ (p : Q R a) (w : Z R z) (hw : p.val*w.val*p.val⁻¹ ∈ Z R z),
          φ ⟨p.val*w.val*p.val⁻¹,hw⟩ = Multiplicative.ofAdd (α p • (φ w).toAdd)) →
        (∀ w : Z R z, (φ w).toAdd ∈ point F → (w:FreeAmalgam R) ∈ Z R t) → False := by
  intro R geometry hb a t z path hat hzt φ α hα hact hpoint
  exact c.original_critical_action_not_quadratic eK geometry hb path
    (critical_quadratic_of_secondary_flag path hb hzt φ α hα hact hpoint
      (c.original_secondary_commutator_eq_bot eK geometry hb path hat hzt))

/-- A surjective natural quotient is enough: the proved order of the original
layer makes it bijective. The quotient, actor, and fixed-point placement all
refer to the same marking. -/
theorem false_of_original_secondary_flag_quotient
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Sp BinaryField.four.Carrier)
    (F : BinaryField) (hF : F.degree = 2) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {a t z : Vertex R}, CriticalPath R geometry a z → Adjacent R a t → Adjacent R z t →
      ∀ (φ : Z R z →* Multiplicative (Vector F.Carrier)), Function.Surjective φ →
      ∀ (α : Q R a →* Sp F.Carrier),
        (∀ p : Q R a, α p ∈ unipotent) →
        (∀ (p : Q R a) (w : Z R z) (hw : p.val*w.val*p.val⁻¹ ∈ Z R z),
          φ ⟨p.val*w.val*p.val⁻¹,hw⟩ = Multiplicative.ofAdd (α p • (φ w).toAdd)) →
        (∀ w : Z R z, (φ w).toAdd ∈ point F.Carrier → (w:FreeAmalgam R) ∈ Z R t) → False := by
  intro R geometry hb a t z path hat hzt φ hφ α hα hact hpoint
  let := finite_Z R z
  have hcard : Nat.card (Z R z) = Nat.card (Multiplicative (Vector F.Carrier)) := by
    rw [c.original_Z_card eK z path.end_color]
    change 256 = Nat.card ((Fin 2 ⊕ Fin 2) → F.Carrier)
    rw [Nat.card_fun, Nat.card_sum, Nat.card_fin, F.card_eq, hF]
    decide
  let E := MulEquiv.ofBijective φ ((Nat.bijective_iff_surjective_and_card φ).mpr ⟨hφ,hcard⟩)
  exact c.false_of_original_secondary_flag eK geometry hb path hat hzt E α hα hact hpoint

end GenerationTwoOvergroup

/-- An alternative remaining geometric premise. It asks for actual coordinates
on the original opposite layer, its original core action, and placement of the
standard fixed point in the common edge layer. No commutator or movement claim
is included. Construction of these simultaneous coordinates and distance two
remains part of the original symplectic source proof. -/
@[expose] def SymplecticSecondaryFlagSource (m : SourceA5TensorModel D e) : Prop :=
  ∀ (c : m.GenerationTwoOvergroup),
    ((pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) →
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∃ (geometry : Geometry R), geometry.b R = 2 ∧
      ∃ (t z : Vertex R) (_path : CriticalPath R geometry (alpha R) z),
        Adjacent R (alpha R) t ∧ Adjacent R z t ∧
        ∃ (F : BinaryField), F.degree = 2 ∧
        ∃ (φ : Z R z →* Multiplicative (Vector F.Carrier)), Function.Surjective φ ∧
        ∃ (α : Q R (alpha R) →* Sp F.Carrier),
          (∀ p : Q R (alpha R), α p ∈ unipotent) ∧
          (∀ (p : Q R (alpha R)) (w : Z R z)
            (hw : p.val*w.val*p.val⁻¹ ∈ Z R z),
            φ ⟨p.val*w.val*p.val⁻¹,hw⟩ = Multiplicative.ofAdd (α p • (φ w).toAdd)) ∧
          (∀ w : Z R z, (φ w).toAdd ∈ point F.Carrier → (w:FreeAmalgam R) ∈ Z R t)

theorem symplecticPlaneRecognition_of_secondary_flag_source
    (hsource : m.SymplecticSecondaryFlagSource) : m.SymplecticPlaneRecognition := by
  apply symplecticPlaneRecognition_of_core_bound
  intro c eK
  obtain ⟨geometry,hb,t,z,path,hat,hzt,F,hF,φ,hφ,α,hα,hact,hpoint⟩ := hsource c eK
  exact (c.false_of_original_secondary_flag_quotient eK F hF geometry hb path hat hzt φ hφ α hα hact hpoint).elim

theorem false_of_generationTwo_source_inputs_of_secondary_flag_source
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hnormal : m.NonzeroCoreCartanNormalization)
    (hzero : m.ZeroCoreLineCentralization) (hcontain : A5PairContainment G)
    (hrows : m.LinearAndG2Exclusion) (hsource : m.SymplecticSecondaryFlagSource) : False :=
  m.false_of_generationTwo_source_inputs hout hnormal hzero hcontain hrows
    (symplecticPlaneRecognition_of_secondary_flag_source hsource)
end CFSG.Quasithin.Chapter10.SourceA5TensorModel
