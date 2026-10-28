module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticBoundaryMovers

/-!
# Strict original movement at the distance-four boundary

An order-four neighboring kernel commutator has an escaping conjugate.
The abelian neighbor comparison makes that conjugate give an actual backward
critical path. Its critical commutator fills the order-four subgroup and lies
in a seed two steps from the endpoint, so it centralizes that endpoint. This
contradicts the chosen escape without assuming that the whole radius is abelian.

The original moving-kernel dichotomy now excludes indices two and four.
The literal second seed on every original critical path has B-index greater
than four, including at distance four. Radius centrality also gives the full
original derived and triple-commutator bounds of source (5.2).

Source: MS93 (5.2), (5.8)--(5.9), pp.914--915,919--922, specialized to the
vanishing original fixed core in Aschbacher--Smith 9.3.10, pp.734--735.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterC.Sp4Four.DistanceReduction.StrictIndex
open ChapterC.Sp4Four.DistanceReduction.LargeDistance
open scoped commutatorElement
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

private theorem neighbor_kernel_commutator_le_seed
    {M : Type*} [Group M] [Finite M] {R : Subgroup M} {a d t : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t) (hdt : Adjacent R d t) :
    ⁅Z R d,Q R a⁆ ≤ Z R d := by
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [ha] at h
    cases he : color R t <;> simp_all
  exact le_normalizer_iff_commutator_le_left.mp
    (((Q_le_adjacent_h R ht hat).trans
      (show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt))).trans
        (Z_normalized R d))

/-- An order-four neighbor commutator supplies an escaping backward critical path at b > 2. -/
theorem original_boundary_small_kernel_backward_path
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      Nat.card (⁅Z R d,Q R a⁆ : Subgroup (FreeAmalgam R)) = 4 →
      ∃ g ∈ stabilizer R a,
        (¬ Z R z ≤ normalizer (⁅Z R (act R g d),Q R a⁆ : Subgroup (FreeAmalgam R))) ∧
        (∃ back : CriticalPath R geometry (act R g d) (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=act R g t ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  intro R geometry hb a z d t path hat hdt hcard
  obtain ⟨g,hg,hbad⟩ := c.original_small_kernel_commutator_escape eK geometry
    (by change 2 < geometry.b R; omega) path hat hdt hcard
  have hga : act R g a = a := hg
  have hatg : Adjacent R a (act R g t) := by
    rw [←hga]
    exact (adjacent_act_iff R g _ _).mpr hat
  have hdtg := (adjacent_act_iff R g _ _).mpr hdt
  let H := ⁅Z R (act R g d),Q R a⁆
  have hmap : (⁅Z R d,Q R a⁆).map (MulAut.conj g⁻¹).toMonoidHom = H := by
    rw [map_commutator,←Z_act,MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a ((stabilizer R a).inv_mem hg))]
  have hHcard : Nat.card H = 4 := by
    rw [←hmap,←hcard]
    exact Nat.card_congr ((⁅Z R d,Q R a⁆).equivMapOfInjective
      (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).toEquiv.symm
  have hHZd : H ≤ Z R (act R g d) :=
    neighbor_kernel_commutator_le_seed path.start_color hatg hdtg
  have hZlocal := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b R)
  have hnot : ¬ Z R (act R g d) ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
    intro hkernel
    apply hbad
    change Z R z ≤ normalizer (H : Set _)
    by_cases hn : Z R z ≤ normalizer ((Z R (act R g d) ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)
    · have hV := ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hatg hdtg
      have hVH : V R a ≤ normalizer (H : Set _) :=
        (geometry.V_le_Q hb a path.start_color).trans (normalizer_commutator_ge_right _ _)
      have hjoin : ⁅Z R (act R g d) ⊔ Z R a,Q R a⁆ = H := le_antisymm
        (commutator_sup_le_of_relative_normal (V R a) (Z R (act R g d)) (Z R a) (Q R a) H
          hVH (le_sup_left.trans hV) (Z_le_VBall R a 2) le_rfl
          ((geometry.centralizes a path.start_color).le.trans bot_le))
        (commutator_mono le_sup_left le_rfl)
      intro x hx
      rw [←hjoin,mem_normalizer_iff_map_conj_eq,map_commutator,
        mem_normalizer_iff_map_conj_eq.mp (hn hx),
        mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a (hZlocal hx))]
    · obtain ⟨heq,hrootcard⟩ := c.original_neighbor_abelian_kernel_commutator eK geometry hb path
        hatg hdtg hkernel hn
      have hrootH : ⁅Z R a,Z R z⁆ ≤ H := heq ▸ commutator_mono le_rfl inf_le_right
      let := finite_Z R (act R g d)
      let : Finite H := Finite.of_injective (inclusion hHZd) (inclusion_injective _)
      have hroot : ⁅Z R a,Z R z⁆ = H := eq_of_le_of_card_ge hrootH
        (by rw [hHcard,←heq,hrootcard])
      rw [←hroot]
      intro x hx
      rw [mem_normalizer_iff_map_conj_eq,map_commutator,
        mem_normalizer_iff_map_conj_eq.mp (Z_normalized R a (hZlocal hx)),
        mem_normalizer_iff_map_conj_eq.mp ((Z R z).le_normalizer hx)]
  exact ⟨g,hg,hbad,ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
    geometry (by omega) path hatg hdtg hnot,
    fun h => hnot ((le_sup_left.trans
      (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hatg hdtg)).trans h)⟩

/-- The full neighboring kernel commutator cannot have order four, including at b = 4. -/
theorem original_boundary_small_kernel_commutator_impossible
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z d t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      Nat.card (⁅Z R d,Q R a⁆ : Subgroup (FreeAmalgam R)) = 4 →
      False := by
  intro R geometry hb a z d t path hat hdt hcard
  obtain ⟨g,hg,hbad,⟨back,_,_⟩,_⟩ :=
    c.original_boundary_small_kernel_backward_path eK geometry hb path hat hdt hcard
  have hga : act R g a = a := hg
  have hatg : Adjacent R a (act R g t) := by
    simpa only [hga] using (adjacent_act_iff R g _ _).mpr hat
  have hdtg := (adjacent_act_iff R g _ _).mpr hdt
  let w := path.walk.getVert (path.walk.length-2)
  let H := ⁅Z R (act R g d),Q R a⁆
  have hmap : (⁅Z R d,Q R a⁆).map (MulAut.conj g⁻¹).toMonoidHom = H := by
    rw [map_commutator,←Z_act,MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a ((stabilizer R a).inv_mem hg))]
  have hHcard : Nat.card H = 4 := by
    rw [←hmap,←hcard]
    exact Nat.card_congr ((⁅Z R d,Q R a⁆).equivMapOfInjective
      (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).toEquiv.symm
  have hHZd : H ≤ Z R (act R g d) :=
    neighbor_kernel_commutator_le_seed path.start_color hatg hdtg
  have hwQ : Z R w ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R w (geometry.exists_critical w back.end_color)
    rw [geometry.distance_constant w back.end_color,SimpleGraph.dist_comm,
      path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hrootH : ⁅Z R (act R g d),Z R w⁆ ≤ H := commutator_mono le_rfl hwQ
  let := finite_Z R (act R g d)
  let : Finite H := Finite.of_injective (inclusion hHZd) (inclusion_injective _)
  have hrootcard : Nat.card (⁅Z R (act R g d),Z R w⁆ : Subgroup (FreeAmalgam R)) = 4 :=
    c.original_critical_commutator_card_four_of_small eK geometry back
      ((Nat.card_le_card_of_injective (inclusion hrootH) (inclusion_injective _)).trans_eq hHcard)
  have hroot : ⁅Z R (act R g d),Z R w⁆ = H :=
    eq_of_le_of_card_ge hrootH (by rw [hHcard,hrootcard])
  have hHZw : H ≤ Z R w := by
    rw [←hroot,commutator_comm]
    exact ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed
      (c.original_critical_reverse eK geometry (by change 0 < geometry.b R; omega) back)
  have hwQz : Z R w ≤ Q R z := by
    apply Z_le_Q_of_dist_lt R w (geometry.exists_critical w back.end_color)
    rw [geometry.distance_constant w back.end_color,path.dist_end,path.length_eq_b]
    change geometry.b R - (geometry.b R - 2) < geometry.b R
    omega
  apply hbad
  exact (le_centralizer_iff.mp
    ((hHZw.trans hwQz).trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color))))).trans
      (Subgroup.centralizer_le_normalizer _)

/-- Every nontrivially moving neighbor has B-index greater than four at b > 2. -/
theorem original_boundary_strict_movement_of_moving_neighbor
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z d t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      1 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) := by
  intro R geometry hb a z d t path hat hdt hmove
  by_contra! hsmall
  have hb2 : 2 < geometry.b R := by omega
  obtain ⟨_,hT⟩ := c.original_moving_neighbor_fixed_intersection eK geometry hb2 path.start_color hat hdt hmove
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [path.start_color] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  have hUdV : U R d ≤ V R a := (U_le_Z d).trans
    (le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt))
  rcases c.original_small_movement_kernel_alternative eK geometry hb2 path.start_color hat hdt hsmall with
    ⟨_,hzero⟩ | ⟨_,hH,_⟩
  · have hcomm : ⁅U R d,Q R a⁆ = ⊥ := by
      simpa only [kernelCommutator,hT] using hzero
    have hUX : U R d ≤ X R a := by
      let := geometry.Z_elementary (by omega : 0 < geometry.b R) d hd
      intro x hx
      exact mem_omegaCenter_iff.mpr ⟨(hUdV.trans (geometry.V_le_Q hb2 a path.start_color)) hx,
        elemPow_eq_one_of_isElementaryAbelian x ((U_le_Z d) hx),
        (commutator_eq_bot_iff_le_centralizer.mp hcomm) hx⟩
    have hUB := ChapterC.Sp4Four.DistanceReduction.radius_le_B_of_commutator geometry hb2
      path.start_color (U R d) hUdV
      ((commutator_mono hUX le_rfl).trans_eq (c.original_X_residual_commutator eK path.start_color))
    have hone := relIndex_eq_one.mpr hUB
    omega
  · have hcard : Nat.card (⁅Z R d,Q R a⁆ : Subgroup (FreeAmalgam R)) = 4 := by
      simpa only [kernelCommutator,hT,←c.original_Z_eq_U d hd] using hH
    exact c.original_boundary_small_kernel_commutator_impossible eK geometry hb path hat hdt hcard

/-- The actual second seed of every original critical path has B-index greater than four. -/
theorem original_boundary_critical_strict_movement
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex
        (U R (path.walk.getVert 2)) := by
  intro R geometry hb a z path
  let d := path.walk.getVert 2
  let t := path.walk.getVert 1
  have hlen : 2 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a t := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R d t := adjacent_symm R ((cosetGraph_adj R _ _).mp
    (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hd : color R d = false := (path.vertex_color (by omega : 2 ≤ path.walk.length)).mpr (by decide)
  apply c.original_boundary_strict_movement_of_moving_neighbor eK geometry hb path hat hdt
  by_contra! hsmall
  change (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) ≤ 1 at hsmall
  let := finite_Z R d
  let : Finite (U R d) := Finite.of_injective (inclusion (U_le_Z d)) (inclusion_injective _)
  have hpos : (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) ≠ 0 :=
    index_ne_zero_of_finite
  have hone : (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) = 1 := by omega
  have hB : Z R d ≤ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a) := by
    rw [c.original_Z_eq_U d hd]
    exact relIndex_eq_one.mp hone
  have hcomm := c.original_nonmoving_neighbor_commutator_eq_bot eK geometry
    (by change 2 < geometry.b R; omega) path.start_color hat hdt hB
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [path.start_color] at h
    cases he : color R t <;> simp_all
  have hQQ : Q R a ≤ Q R d := by
    rw [←C_eq_Q R hodd.isPGroup hodd.twoCore_le hfaith d hd]
    exact le_inf ((Q_le_adjacent_h R ht hat).trans
      (fun _ hx => hx.2 d (adjacent_symm R hdt)))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm))
  let := finite_stabilizer R d
  let : Finite (Q R d) := Finite.of_injective
    (inclusion (show Q R d ≤ stabilizer R d from fun _ hx => hx.1)) (inclusion_injective _)
  have hQeq : Q R a = Q R d := eq_of_le_of_card_ge hQQ
    (by rw [c.original_kernel_card_eq path.start_color,c.original_kernel_card_eq hd])
  have hZQ : Z R z ≤ Q R d := by
    apply Z_le_Q_of_dist_lt R z (geometry.exists_critical z path.end_color)
    rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,path.dist_end,path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  exact (c.original_critical_reverse eK geometry (by change 0 < geometry.b R; omega) path).critical.2
    (hZQ.trans_eq hQeq.symm)

/-- The unconditional original source (5.2) bounds, with the complete X-layer
and the actual endpoint triple commutator. -/
theorem original_radius_centrality_bounds
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (_geometry : Geometry R) (a : Vertex R), color R a = false → ∀ d w : Vertex R,
      ⁅V R a,V R a⁆ ≤ X R a ∧
      ⁅⁅X R d ⊓ Q R a,V R a ⊓ Q R w⁆,V R a ⊓ Q R w⁆ = ⊥ := by
  intro R geometry a ha d w
  have hc := c.original_radius_commutator_central eK geometry a ha
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  exact ⟨SectionFive.radius_derived_le_X R geometry hb ha hc,
    SectionFive.critical_radius_triple_commutator R hc⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
