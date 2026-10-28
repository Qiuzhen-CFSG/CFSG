module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticCriticalPaths
public import Theory.GroupTheory.PResidual.SubnormalCoreAction

/-!
# Movement of the full original radius kernel

The two-perfect residual cannot act nontrivially on a two-section of order
less than 256. Commutator idempotence therefore shows that the original
radius has at least 256 images even modulo its full fixed preimage B.
Combining this with the order-64 radius-image bound leaves at least four
images modulo B in every nearby kernel. At the literal truncated critical
endpoint the full kernel consequently has residual displacement outside Z.
GenerationTwoSymplecticOrbitPaths applies these estimates on the same
conjugator-preserving critical sequence used by the large-distance argument.

The proof adapts the fixed-preimage argument in NonbinarySymplectic's
MovingRadius directly to the original tensor geometry, using its literal
neighborhood kernels. It makes no identification with a replacement core.
Source: MS93 (2.1)(iii), (5.7)--(5.11), pp.856,919--924;
Aschbacher--Smith 9.3.10, pp.734--735. The stronger radius-image estimate
and both distance exclusions remain separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterB.QuasisimpleSource ChapterC.MSCentralOrbit
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

/-- The full original fixed preimage still leaves at least 256 radius images. -/
theorem original_moving_radius_index_ge_256
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) (a : Vertex R), color R a = false →
      256 ≤ (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (V R a) := by
  intro R geometry a ha
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hcard,_,_⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      BinaryField.four.card_eq eK c.fitting_center.1 c.component_product.2.2.2
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨π,hπ,hπker⟩ := ChapterC.RankTwo.Sp4Four.local_residual_projection R
    hodd.isPGroup hodd.twoCore_le q (QuotientGroup.ker_mk' _) ha
  let S := stabilizer R a
  let A := CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)
  have hVQ := geometry.V_le_Q hb a ha
  have hVS : V R a ≤ S := hVQ.trans (fun _ hx => hx.1)
  have hnA : S ≤ normalizer (A : Set (FreeAmalgam R)) :=
    Escape.Propagation.Rigidity.B_normalized hb a ha
  let := finite_stabilizer R a
  let : Finite (V R a) := Finite.of_injective (inclusion hVS) (inclusion_injective _)
  let : Finite (Ltilde R a) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer a)) (inclusion_injective _)
  let : (A.subgroupOf (V R a)).Normal :=
    normal_subgroupOf_of_le_normalizer (hVS.trans hnA)
  have hpV := (Q_isPGroup R hodd.isPGroup hodd.twoCore_le a ha).to_le hVQ
  have hid : ⁅⁅V R a,Ltilde R a⁆,Ltilde R a⁆ = ⁅V R a,Ltilde R a⁆ := by
    let N := (V R a).subgroupOf S
    let : N.Normal := normal_subgroupOf_of_le_normalizer (DistanceEight.V_normalized R a)
    have hi := commutator_isPPerfect_idempotent (pResidual 2 S) N
      (isPPerfect_pResidual 2) hpV.comap_subtype le_normalizer_of_normal
    have hi' := congrArg (Subgroup.map S.subtype) hi
    have hN : N.map S.subtype = V R a := map_subgroupOf_eq_of_le hVS
    simp only [map_commutator,hN] at hi'
    exact hi'
  have hAZ : ⁅A,Ltilde R a⁆ ≤ Z R a := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    exact ((mem_B_iff R a (geometry.Z_normal a) hVS x).mp hx).2 l hl
  have hne : Z R a ≠ ⊥ := by
    intro hz
    have hc := c.original_Z_card eK a ha
    rw [hz,card_bot] at hc
    omega
  have hgen : pResidual 2 c.M ⊔ R = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨k,hk,r,hr,rfl⟩ := c.component_product.2.2.2 x
    exact Subgroup.mul_mem _ (mem_sup_left hk) (mem_sup_right hr)
  by_contra! hi
  have hVA : ⁅V R a,Ltilde R a⁆ ≤ A :=
    commutator_component_le_of_seventeen_section_lt_256 (Ltilde R a) (V R a) A
      (isPPerfect_embedded_pResidual_of_finite 2 _) π hπ hπker
      (by rw [hcard]; decide) hpV hi
      ((Ltilde_le_stabilizer a).trans (DistanceEight.V_normalized R a))
      ((Ltilde_le_stabilizer a).trans hnA)
  have hVZ : Vcirc R a ≤ Z R a :=
    hid.symm.le.trans ((commutator_mono hVA le_rfl).trans hAZ)
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  exact ChapterC.RankTwo.Sp4Four.radius_moving_not_le_Z_of_residual_edge_generation
    hms hgen geometry hb rfl
    ((adjacent_iff_exists_common R _ _).mpr ⟨g,Or.inl ⟨rfl,rfl⟩⟩) hne hVZ

/-- Every original radius kernel within critical range still moves modulo
B, retaining the entire intersection with the distant neighborhood kernel. -/
theorem original_radius_kernel_moving_index_ge_four
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R}, color R a = false → color R z = false →
        (cosetGraph R).dist a z + 2 ≤ geometry.b R →
        4 ≤ (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (V R a ⊓ Q R z) := by
  intro R geometry hb a z ha hz hd
  let A := CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)
  have hlo := c.original_moving_radius_index_ge_256 eK geometry a ha
  have hup := c.original_radius_image_index_le_64 eK geometry hb ha hz hd
  let := finite_stabilizer R a
  let : Finite (V R a) := Finite.of_injective
    (inclusion ((geometry.V_le_Q (by omega) a ha).trans (fun _ hx => hx.1)))
    (inclusion_injective _)
  have hi : A.relIndex (V R a) ≤ (A ⊓ Q R z).relIndex (V R a) :=
    relIndex_le_of_le_left inf_le_left index_ne_zero_of_finite
  have hprod := relIndex_inf_mul_relIndex A (Q R z) (V R a)
  rw [inf_comm (Q R z) (V R a)] at hprod
  change 256 ≤ A.relIndex (V R a) at hlo
  change (Q R z).relIndex (V R a) ≤ 64 at hup
  have hm := Nat.mul_le_mul_left (A.relIndex (V R a ⊓ Q R z)) hup
  rw [hprod] at hm
  change 4 ≤ A.relIndex (V R a ⊓ Q R z)
  omega

/-- At the literal truncated endpoint, the whole kernel escapes B. Its
residual commutator therefore escapes the original seed Z. -/
theorem original_truncated_radius_kernel_movement
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      let Y := V R a ⊓ Q R (path.walk.getVert (path.walk.length-2))
      4 ≤ (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex Y ∧
        ¬ Y ≤ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a) ∧ ¬ ⁅Y,Ltilde R a⁆ ≤ Z R a := by
  intro R geometry hb a z path Y
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have he : Even path.walk.length := by
    rw [path.shortest,path.critical.1]
    exact geometry.even a path.start_color
  have hw : color R (path.walk.getVert (path.walk.length-2)) = false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    rw [Nat.even_iff] at he ⊢
    omega
  have hi : 4 ≤ (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex Y := by
    apply c.original_radius_kernel_moving_index_ge_four eK geometry hb path.start_color hw
    rw [path.dist_start (Nat.sub_le _ _),Nat.sub_add_cancel (by omega : 2 ≤ path.walk.length)]
    exact path.length_eq_b.le
  have hn : ¬ Y ≤ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a) := by
    intro h
    rw [relIndex_eq_one.mpr h] at hi
    omega
  refine ⟨hi,hn,?_⟩
  intro h
  exact hn (ChapterC.Sp4Four.DistanceReduction.radius_le_B_of_commutator geometry
    (by omega) path.start_color Y inf_le_left h)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
