module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticDistanceTwo
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticOriginalLayers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.RadiusObstruction

/-!
# Radius obstructions on the original tensor geometry

Original center-freeness eliminates the entire fixed two-core at every
M-vertex. The completed distance-two contradiction leaves distance at least
four. The residual-edge argument now gives [V_a:Z_a] at least 256 and
|V_a| at least 65536, on this same original geometry.

It also supplies the actual escaping neighboring join. The native backward
critical path follows once its displayed original radius displacement is
established. Neither a distance bound nor a comparison with characteristic
replacement is asserted. SymplecticPlaneRecognition remains open.

Source: Aschbacher--Smith 9.3.6--10, pp.734--735; MS93 (2.1)(vii), p.856,
and (5.7)--(5.8), pp.919--920.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

private theorem residual_sup_original_radical :
    pResidual 2 c.M ⊔ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M) = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨k,hk,r,hr,rfl⟩ := c.component_product.2.2.2 x
  exact Subgroup.mul_mem _ (mem_sup_left hk) (mem_sup_right hr)

/-- The entire original fixed core is trivial, not only its central omega layer. -/
theorem original_fixedCore_eq_bot :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ a : Vertex R, color R a = false → fixedCore R a = ⊥ := by
  intro R a ha
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨i,hi,_,hiL,_,hiQ⟩ := vertex_coordinates_with_kernel R hodd.isPGroup hodd.twoCore_le ha
  apply le_bot_iff.mp
  rintro x ⟨hx,hcent⟩
  rw [←hiQ] at hx
  obtain ⟨y,hy,rfl⟩ := hx
  have hyC : y ∈ centralizer (pResidual 2 c.M : Set c.M) := by
    intro k hk
    apply hi
    simpa only [map_mul] using hcent (i k) (by rw [←hiL]; exact mem_map_of_mem i hk)
  have hy1 : y = 1 := mem_bot.mp (c.core_inf_residual_centralizer_eq_bot ▸ ⟨hy,hyC⟩)
  simp only [hy1,map_one,mem_bot]

/-- The original radius quotient has at least 256 elements at every M-vertex. -/
theorem original_radius_index_ge_256
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (_geometry : Geometry R) (a : Vertex R), color R a = false →
      256 ≤ (Z R a).relIndex (V R a) := by
  intro R geometry a ha
  have hfour := c.original_geometry_four_le eK geometry
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
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
  obtain ⟨π,hπ,hπker⟩ := local_residual_projection R hodd.isPGroup hodd.twoCore_le
    q (QuotientGroup.ker_mk' _) ha
  have hne : Z R a ≠ ⊥ := by
    intro hz
    have hcard := c.original_Z_card eK a ha
    rw [hz,card_bot] at hcard
    omega
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  exact radius_index_ge_256_of_residual_edge_generation hms c.residual_sup_original_radical
    geometry (by omega) rfl
    ((adjacent_iff_exists_common R _ _).mpr ⟨g,Or.inl ⟨rfl,rfl⟩⟩) hne
    (Q_isPGroup R hodd.isPGroup hodd.twoCore_le _ rfl) π hπ hπker (by rw [hc]; decide)

/-- The original radius itself has at least 2^16 elements. -/
theorem original_radius_card_ge_65536
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (_geometry : Geometry R) (a : Vertex R), color R a = false →
      65536 ≤ Nat.card (V R a) := by
  intro R geometry a ha
  have hi := c.original_radius_index_ge_256 eK geometry a ha
  change 256 ≤ (Z R a).relIndex (V R a) at hi
  have hc := c.original_Z_card eK a ha
  change Nat.card (Z R a) = 256 at hc
  have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R)) (Z R a) (V R a)
    bot_le (Z_le_VBall R a 2)
  rw [relIndex_bot_left,relIndex_bot_left,hc] at hm
  omega

/-- An original critical endpoint has an actual escaping conjugate of a neighboring seed join. -/
theorem original_critical_neighbor_join_escape
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a t z : Vertex R}, CriticalPath R geometry a z → Adjacent R a t →
      ∃ d, Adjacent R d t ∧
        ¬ stabilizer R a ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) ∧
        ∃ g ∈ stabilizer R a,
          ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a).map (MulAut.conj g⁻¹).toMonoidHom) := by
  intro R geometry a t z path hat
  have hfour := c.original_geometry_four_le eK geometry
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,_,_,_⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      BinaryField.four.card_eq eK c.fitting_center.1 c.component_product.2.2.2
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hne : Z R a ≠ ⊥ := by
    intro hz
    have hcard := c.original_Z_card eK a path.start_color
    rw [hz,card_bot] at hcard
    omega
  exact exists_critical_neighbor_join_escape hms hodd.isPGroup hodd.twoCore_le
    c.residual_sup_original_radical q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hBC geometry (by omega)
    (ChapterC.MSCentralOrbit.edgeCentralizerCondition R hodd.isPGroup hodd.twoCore_le hfaith)
    path.start_color hat hne path

/-- The original source geometry supplies the escaping join and every local
quotient input. Only the displayed original radius displacement remains. -/
theorem original_backward_path_of_radius_displacement
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a t z : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t →
      ⁅V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)),Z R z⁆ ≤ Z R a →
      ∃ d t', Adjacent R a t' ∧ Adjacent R d t' ∧
        (∃ back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1 = t' ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∧
        ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  intro R geometry a t z path hat hdisp
  obtain ⟨d,hdt,_,g,hg,hn⟩ := c.original_critical_neighbor_join_escape eK geometry path hat
  exact backward_path_of_escaped_neighbor_join geometry
    (lt_of_lt_of_le (by decide : 2 < 4) (c.original_geometry_four_le eK geometry))
    path hat hdt g hg hn hdisp

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
