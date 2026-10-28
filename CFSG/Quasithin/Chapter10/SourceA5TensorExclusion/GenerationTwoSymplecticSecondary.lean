module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticCoreBound
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.CoreReconstruction.OriginalSecondary

/-!
# The original center-free secondary-orbit reduction

The original residual supplements the original Sylow subgroup in a center-free
finite overgroup. Its centralizer in the two-core therefore vanishes. Transport
to every original graph vertex retains that full central kernel. At distance
two, the non-Frattini critical comparison now gives X = Z = U and order 256.
The greatest opposite secondary seed lies in the original two-core; at the base
critical path its order is at most 64.

For this original center-free case, the source identity [R_alpha,Q_alpha] =
[Y,Q_alpha] forces the whole secondary orbit into Z_alpha. This directly
contradicts the preceding source claim [R_alpha,Ltilde_alpha] not contained in
Z_alpha. Thus these two claims and the distance-two reduction suffice, without
the later natural-section and paired Frattini reconstruction. The conditional
assembly applies this to the constructed original plane maps.

The remaining distance and secondary source claims stay explicit in
SymplecticSecondarySource and must be proved by qt-d-tensor-sp4-plane.
They must hold on the original geometry: the paper's characteristic reduction
does not by itself transport these identities from its replacement group.
This is not yet SymplecticPlaneRecognition. Final tensor exclusion belongs to
qt-d-tensor-exclusion. Source: Aschbacher--Smith9.3.10 and its concluding
paragraph, pp.734--735; MS93 (3.6), printed p.871.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.LocalPackage
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterC.MSCentralOrbit
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.CoreReconstruction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e}

namespace GenerationTwoOvergroup
variable (c : m.GenerationTwoOvergroup)

theorem core_inf_residual_centralizer_eq_bot :
    pCore 2 c.M ⊓ centralizer (pResidual 2 c.M : Set c.M) = ⊥ := by
  obtain ⟨S,hS⟩ := c.sylow
  have he : (S : Subgroup c.M) =
      ((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M := by
    apply Subgroup.map_injective c.M.subtype_injective
    rw [hS,map_subgroupOf_eq_of_le (c.generated ▸ le_sup_right)]
  have hcover : pResidual 2 c.M ⊔ (S : Subgroup c.M) = ⊤ := by
    apply eq_top_iff.mpr
    intro g _
    obtain ⟨k,hk,r,hr,rfl⟩ := c.component_product.2.2.2 g
    exact (pResidual 2 c.M ⊔ (S : Subgroup c.M)).mul_mem
      (mem_sup_left hk) (mem_sup_right (by rwa [he]))
  exact inf_centralizer_eq_bot_of_centerfree_sylow_supplement S
    (pResidual 2 c.M) (pCore 2 c.M) hcover pCore_isPGroup c.fitting_center.2

theorem graph_X_fixed_eq_bot :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ a : Vertex R, color R a = false →
      X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥ := by
  intro R a ha
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨i,hi,hir,hiL,_,hiQ⟩ := vertex_coordinates_with_kernel R
    hodd.isPGroup hodd.twoCore_le ha
  apply le_bot_iff.mp
  rintro x ⟨hx,hcent⟩
  have hxQ : x ∈ Q R a := omegaCenter_le _ hx
  rw [←hiQ] at hxQ
  obtain ⟨y,hy,rfl⟩ := hxQ
  have hyC : y ∈ centralizer (pResidual 2 c.M : Set c.M) := by
    intro k hk
    apply hi
    simpa only [map_mul] using hcent (i k) (by rw [←hiL]; exact mem_map_of_mem i hk)
  have hy1 : y = 1 := mem_bot.mp (c.core_inf_residual_centralizer_eq_bot ▸ ⟨hy,hyC⟩)
  simp only [hy1,map_one,mem_bot]

theorem graph_core_nonfrattini
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ a : Vertex R, color R a = false →
      ¬ core R a ≤ (frattini (Q R a)).map (Q R a).subtype ⊔ X R a := by
  intro R a ha
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  apply nonfrattini_at_vertex R _ ha
  exact graph_core_nonfrattini_of_intrinsic (pResidual 2 c.M) R
    hodd.isPGroup hodd.twoCore_le rfl (c.blockU_not_le_frattini_central eK)

theorem original_distance_two_layers
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {a z : Vertex R}, CriticalPath R geometry a z →
        X R a = Z R a ∧ Z R a = U R a ∧ Nat.card (Z R a) = 256 := by
  intro R geometry hb a z path
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hc,hsq,hQne⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      ChapterB.QuasisimpleSource.BinaryField.four.card_eq eK c.fitting_center.1
      c.component_product.2.2.2
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
    (pResidual 2 c.M) c.component_product.1
    ChapterB.QuasisimpleSource.BinaryField.four.card_eq eK c.fitting_center.1
    c.component_product.2.2.2
  have hself : centralizer (pCore 2 c.M : Set c.M) ≤ pCore 2 c.M := by
    simpa only [c.fitting_center.1] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := c.M))
  have hne : R ≠ ⊥ := fun hr => hQne (le_bot_iff.mp (hr ▸ hodd.twoCore_le))
  have hXU := original_nonfrattini_X_decomposition R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hc hBC hsq path hb (c.graph_core_nonfrattini eK a path.start_color)
  rw [c.graph_X_fixed_eq_bot a path.start_color,sup_bot_eq] at hXU
  have hpos : 0 < geometry.b R := by omega
  have hba : 0 < criticalDistance R a (geometry.exists_critical a path.start_color) :=
    lt_of_lt_of_eq hpos (geometry.distance_constant a path.start_color).symm
  have hZU : Z R a = U R a := le_antisymm
    ((geometry.omega_bound a path.start_color hba).trans_eq hXU) (U_le_Z a)
  let := Z_elementary_of_positive R geometry a path.start_color hba
  let : IsElementaryAbelian 2 (U R a) := hZU ▸ inferInstance
  have hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥ := by
    rw [←hXU]
    exact c.graph_X_fixed_eq_bot a path.start_color
  have hcard := original_initial_card_of_fixed_eq_bot R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hc hBC hsq path.start_color hfixed
  exact ⟨hXU.trans hZU.symm,hZU,by rwa [hZU]⟩

theorem original_secondary_seed_le_kernel
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {a t z : Vertex R}, CriticalPath R geometry a z →
        Adjacent R a t → Adjacent R z t → secondarySeed R a t z ≤ Q R a := by
  intro R geometry hb a t z path hat hzt
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
  exact original_secondarySeed_le_kernel R hodd.isPGroup hodd.twoCore_le
    (QuotientGroup.mk' (pCore 2 c.M)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) hBC path hb hat hzt
    (c.graph_core_nonfrattini eK a path.start_color)

theorem original_secondary_orbit_le_kernel
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {a t z : Vertex R}, CriticalPath R geometry a z → Adjacent R a t → Adjacent R z t →
        secondaryOrbit R a (secondarySeed R a t z) ≤ Q R a := by
  intro R geometry hb a t z path hat hzt
  exact conjugatesIn_le_of_normalized _ _ _
    (c.original_secondary_seed_le_kernel eK geometry hb path hat hzt) (Q_normalized R a)

def original_critical_reverse
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 0 < geometry.b R →
      ∀ {a z : Vertex R}, CriticalPath R geometry a z → CriticalPath R geometry z a := by
  intro R geometry hb a z path
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1
    ChapterB.QuasisimpleSource.BinaryField.four.card_eq eK c.fitting_center.1
    c.component_product.2.2.2
  exact { start_color := path.end_color
          walk := path.walk.reverse
          shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
          critical := critical_reverse R geometry
            (ChapterC.MSCentralOrbit.edgeCentralizerCondition R hodd.isPGroup hodd.twoCore_le hfaith)
            a path.start_color (by rwa [geometry.distance_constant a path.start_color])
            z path.end_color path.critical }

theorem original_secondary_seed_card_le
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {t z : Vertex R}, CriticalPath R geometry (alpha R) z →
        Adjacent R (alpha R) t → Adjacent R z t →
          Nat.card (secondarySeed R (alpha R) t z) ≤ 64 := by
  intro R geometry hb t z path hat hzt
  have hpos : 0 < geometry.b R := by omega
  have rev := c.original_critical_reverse eK geometry hpos path
  have hcard := (c.original_distance_two_layers eK geometry hb rev).2.2
  have hind := (c.nonfrattini_critical_indices eK geometry hb path).2
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (Q R (alpha R) ⊓ Z R z) (Z R z) bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,hind,hcard] at hmul
  have hi : secondarySeed R (alpha R) t z ≤ Q R (alpha R) ⊓ Z R z :=
    le_inf (c.original_secondary_seed_le_kernel eK geometry hb path hat hzt)
      (secondarySeed_le R (alpha R) t z)
  let := finite_Z R z
  let : Finite ↥(Q R (alpha R) ⊓ Z R z : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (show Q R (alpha R) ⊓ Z R z ≤ Z R z from inf_le_right))
      (inclusion_injective _)
  have hle := Nat.card_le_card_of_injective (inclusion hi) (inclusion_injective hi)
  omega

theorem original_secondary_orbit_le_initial_of_seed_commutator
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {a t z : Vertex R}, CriticalPath R geometry a z → Adjacent R a t → Adjacent R z t →
      ⁅secondaryOrbit R a (secondarySeed R a t z),Q R a⁆ ≤ ⁅secondarySeed R a t z,Q R a⁆ →
      secondaryOrbit R a (secondarySeed R a t z) ≤ Z R a := by
  intro R geometry hb a t z path hat hzt hcomm
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
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1
    ChapterB.QuasisimpleSource.BinaryField.four.card_eq eK c.fitting_center.1
    c.component_product.2.2.2
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
  have hle := secondary_orbit_le_X_of_seed_commutator path hb hat hzt
    (ChapterC.MSCentralOrbit.edgeCentralizerCondition R hodd.isPGroup hodd.twoCore_le hfaith)
    (c.original_secondary_seed_le_kernel eK geometry hb path hat hzt) κ hκ hkQ hna hcent
    (c.graph_X_fixed_eq_bot a path.start_color) hcomm
  exact hle.trans_eq (c.original_distance_two_layers eK geometry hb path).1

/-- In the center-free original overgroup the source secondary movement and
commutator identity already contradict one another. The later natural section
and paired Frattini reconstruction are unnecessary for this specialized branch. -/
theorem false_of_original_secondary_movement
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 2 →
      ∀ {a t z : Vertex R}, CriticalPath R geometry a z → Adjacent R a t → Adjacent R z t →
      ⁅secondaryOrbit R a (secondarySeed R a t z),Q R a⁆ ≤ ⁅secondarySeed R a t z,Q R a⁆ →
      (¬ ⁅secondaryOrbit R a (secondarySeed R a t z),Ltilde R a⁆ ≤ Z R a) → False := by
  intro R geometry hb a t z path hat hzt hcomm hmove
  have hle := c.original_secondary_orbit_le_initial_of_seed_commutator
    eK geometry hb path hat hzt hcomm
  exact hmove ((commutator_mono hle le_rfl).trans (U_le_Z a))

end GenerationTwoOvergroup

/-- The remaining distance and secondary-orbit source claims on one original
critical path. Their proof remains with qt-d-tensor-sp4-plane. -/
@[expose] def SymplecticSecondarySource (m : SourceA5TensorModel D e) : Prop :=
  ∀ (c : m.GenerationTwoOvergroup),
    ((pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃*
      Matrix.symplecticGroup (Fin 2) ChapterB.QuasisimpleSource.BinaryField.four.Carrier) →
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∃ (geometry : Geometry R), geometry.b R = 2 ∧
      ∃ (t z : Vertex R) (_path : CriticalPath R geometry (alpha R) z),
        Adjacent R (alpha R) t ∧ Adjacent R z t ∧
        ⁅secondaryOrbit R (alpha R) (secondarySeed R (alpha R) t z),Q R (alpha R)⁆ ≤
          ⁅secondarySeed R (alpha R) t z,Q R (alpha R)⁆ ∧
        ¬ ⁅secondaryOrbit R (alpha R) (secondarySeed R (alpha R) t z),Ltilde R (alpha R)⁆ ≤
          Z R (alpha R)

theorem symplecticCoreBound_of_secondary_source
    (hsource : m.SymplecticSecondarySource) : m.SymplecticCoreBound := by
  intro c eK
  obtain ⟨geometry,hb,t,z,path,hat,hzt,hcomm,hmove⟩ := hsource c eK
  exact (c.false_of_original_secondary_movement eK geometry hb path hat hzt hcomm hmove).elim

theorem symplecticPlaneRecognition_of_secondary_source
    (hsource : m.SymplecticSecondarySource) : m.SymplecticPlaneRecognition :=
  symplecticPlaneRecognition_of_core_bound (symplecticCoreBound_of_secondary_source hsource)

theorem false_of_generationTwo_source_inputs_of_secondary_source
    (hout : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hnormal : m.NonzeroCoreCartanNormalization)
    (hzero : m.ZeroCoreLineCentralization) (hcontain : A5PairContainment G)
    (hrows : m.LinearAndG2Exclusion) (hsource : m.SymplecticSecondarySource) : False :=
  m.false_of_generationTwo_source_inputs hout hnormal hzero hcontain hrows
    (symplecticPlaneRecognition_of_secondary_source hsource)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
