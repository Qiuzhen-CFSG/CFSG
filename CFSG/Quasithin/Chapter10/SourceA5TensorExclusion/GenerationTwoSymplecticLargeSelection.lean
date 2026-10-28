module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticFullSeedControl

/-!
# Original large-image selection with equal full movers

The neighbor-kernel commutator lies in the sixteen-element common fixed
plane. Strict movement makes it nonzero, and the original residual cannot
normalize such a small subgroup. The original edge-conjugate generation
therefore selects a conjugate whose commutator is not normalized by the
critical endpoint. Large starting image forces this conjugate to extend
the literal path backwards. A large backward image would make its root
fill the whole commutator and centralize the endpoint, a contradiction.
Thus the selected backward image has order four.

This actual selection proves X=Z at every original-color vertex whenever
the first movers agree, by transporting the small backward path's layer
identity. It does not assume away X ≠ Z: that alternative has unequal
movers and order-sixteen images on every critical path. Its large-image
selection, both terminal distance exclusions, distance four and the final
marked-plane recognition remain open.

Source: MS93 (2.1)(vii), (5.3), (5.7)--(5.11), printed pp.856,915,919--924;
Aschbacher--Smith 9.3.10, printed pp.734--735.
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


/-- The full edge-mover fixed plane has exactly sixteen elements. -/
theorem original_edge_mover_fixed_card
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a t : Vertex R}, color R a = false → Adjacent R a t →
      Nat.card (Z R a ⊓ centralizer (LocalPackage.J R a t : Set (FreeAmalgam R)) :
        Subgroup (FreeAmalgam R)) = 16 := by
  intro R a t ha hat
  let := finite_Z R a
  let : Finite (Z R a ⊓ centralizer (LocalPackage.J R a t : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R)) := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hi : (centralizer (LocalPackage.J R a t : Set (FreeAmalgam R))).relIndex (Z R a) = 16 := by
    rw [c.original_Z_eq_U a ha]
    exact (c.original_small_mover_join_indices eK ha hat).2.2
  have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (Z R a ⊓ centralizer (LocalPackage.J R a t : Set (FreeAmalgam R))) (Z R a) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hi,c.original_Z_card eK a ha] at hm
  omega

/-- Equal movers bound the full neighbor-kernel commutator by their fixed
plane. This order bound applies even when the original X-layer is larger. -/
theorem original_equal_mover_neighbor_commutator_bound
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      Nat.card (⁅Z R d,Q R a⁆ : Subgroup (FreeAmalgam R)) ≤ 16 := by
  intro R geometry hb a d t ha hat hdt heq
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [ha] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hQaJ : Q R a ≤ LocalPackage.J R d t := by
    rw [heq]
    exact LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le ha hat
  have hC : ⁅Z R d,Q R a⁆ ≤ centralizer (LocalPackage.J R a t : Set (FreeAmalgam R)) := by
    rw [commutator_comm,←heq]
    exact (commutator_mono hQaJ le_rfl).trans (c.original_edge_mover_quadratic eK hd hdt)
  have hle := le_inf (c.original_equal_mover_displacement_le_Z eK geometry hb ha hat hdt heq) hC
  let := finite_Z R a
  let : Finite (Z R a ⊓ centralizer (LocalPackage.J R a t : Set (FreeAmalgam R)) :
      Subgroup (FreeAmalgam R)) := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hc := Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  rwa [c.original_edge_mover_fixed_card eK ha hat] at hc

/-- A nonzero small neighbor commutator has an actual endpoint conjugate
escaping its normalizer, with the original edge Sylow retained. -/
theorem original_neighbor_commutator_escape
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z d t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      ⁅Z R d,Q R a⁆ ≠ ⊥ →
      Nat.card (⁅Z R d,Q R a⁆ : Subgroup (FreeAmalgam R)) ≤ 128 →
      ∃ g ∈ stabilizer R a,
        ¬ Z R z ≤ normalizer (⁅Z R (act R g d),Q R a⁆ : Subgroup (FreeAmalgam R)) := by
  intro R geometry hb a z d t path hat hdt hneH hcardH
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
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
  have hgen : pResidual 2 c.M ⊔ R = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨k,hk,r,hr,rfl⟩ := c.component_product.2.2.2 x
    exact Subgroup.mul_mem _ (mem_sup_left hk) (mem_sup_right hr)
  let H := ⁅Z R d,Q R a⁆
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [path.start_color] at h
    cases he : color R t <;> simp_all
  have hHQ : H ≤ Q R a := (neighbor_kernel_commutator_le_seed path.start_color hat hdt).trans
    ((le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)).trans
      (geometry.V_le_Q hb a path.start_color))
  have hHS : H ≤ stabilizer R a := hHQ.trans (fun _ hx => hx.1)
  have hHN : Q R t ≤ normalizer (H : Set _) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized R d (hx.2 d (adjacent_symm R hdt))),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a (hx.2 a (adjacent_symm R hat)))]
  have hnot : ¬ (H.subgroupOf (stabilizer R a)).Normal := by
    intro hn
    have hzero := c.original_small_normal_core_eq_bot eK path.start_color H hHQ
      ((Ltilde_le_stabilizer a).trans ((normal_subgroupOf_iff_le_normalizer hHS).mp hn))
      hcardH
    exact hneH hzero
  have hpos : 0 < geometry.b R := by omega
  have hrev := c.original_critical_reverse eK geometry hpos path
  have hegen := edge_conjugate_generation_of_centric_component R hodd.isPGroup hodd.twoCore_le
    hgen q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hBC
    path.start_color hat (Z R z) (path.endpoint_Z_le_start_stabilizer (by omega)) hrev.critical.2
  obtain ⟨g,hg,hbad,_⟩ := source_2_1_vii R a z t path.start_color hat H H
    (hHQ.trans (Q_le_adjacent_h R ht hat)) (hHQ.trans (Q_le_adjacent_h R ht hat))
    (normal_subgroupOf_of_le_normalizer hHN) (normal_subgroupOf_of_le_normalizer hHN)
    hnot hnot hegen
  refine ⟨g,hg,?_⟩
  have hQmap := mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a ((stabilizer R a).inv_mem hg))
  change ¬ Z R z ≤ normalizer ((⁅Z R d,Q R a⁆).map (MulAut.conj g⁻¹).toMonoidHom) at hbad
  rw [map_commutator,←Z_act,MulEquiv.toMonoidHom_eq_coe,hQmap] at hbad
  exact hbad


/-- A large original critical image with equal first movers admits a literal
backward path with small image. Selection preserves the original conjugator
and the endpoint's failure to normalize the whole neighbor commutator. -/
theorem original_large_equal_mover_backward_small_image
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      4 < (Q R z).relIndex (Z R a) →
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      ∃ g ∈ stabilizer R a,
        ∃ back : CriticalPath R geometry (act R g (path.walk.getVert 2))
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = act R g (path.walk.getVert 1) ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        (Q R (path.walk.getVert (path.walk.length-2))).relIndex
          (Z R (act R g (path.walk.getVert 2))) = 4 ∧
        ¬ Z R z ≤ normalizer (⁅Z R (act R g (path.walk.getVert 2)),Q R a⁆ :
          Subgroup (FreeAmalgam R)) := by
  intro R geometry hb a z path hlarge heq
  let d := path.walk.getVert 2
  let t := path.walk.getVert 1
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a t := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R d t := adjacent_symm R ((cosetGraph_adj R _ _).mp
    (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hd : color R d = false := (path.vertex_color (by omega)).mpr (by decide)
  have hmove := c.original_critical_strict_movement eK geometry hb path
  have hne : ⁅Z R d,Q R a⁆ ≠ ⊥ := by
    intro hz
    have hc := commutator_eq_bot_iff_le_centralizer.mp hz
    have hB := c.original_neighbor_core_fixed_eq_B eK geometry (by change 2 < geometry.b R; omega) path.start_color hat hdt
      (lt_trans (by decide : 1 < 4) hmove)
    have hle : Z R d ≤ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a) :=
      (le_inf le_rfl hc).trans (hB.le.trans inf_le_right)
    rw [c.original_Z_eq_U d hd] at hle
    rw [relIndex_eq_one.mpr hle] at hmove
    omega
  have hbound := c.original_equal_mover_neighbor_commutator_bound eK geometry (by change 2 < geometry.b R; omega)
    path.start_color hat hdt heq
  obtain ⟨g,hg,hbad⟩ := c.original_neighbor_commutator_escape eK geometry (by change 2 < geometry.b R; omega)
    path hat hdt hne (hbound.trans (by decide))
  have hga : act R g a = a := hg
  have hatg : Adjacent R a (act R g t) := by
    simpa only [hga] using (adjacent_act_iff R g _ _).mpr hat
  have hdtg := (adjacent_act_iff R g _ _).mpr hdt
  have heqg : LocalPackage.J R (act R g d) (act R g t) = LocalPackage.J R a (act R g t) := by
    rw [smallMoverJoin_act,heq,←smallMoverJoin_act,hga]
  let H := ⁅Z R (act R g d),Q R a⁆
  change ¬ Z R z ≤ normalizer (H : Set (FreeAmalgam R)) at hbad
  have hZlocal := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b R)
  have hnot : ¬ Z R (act R g d) ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
    intro hkernel
    have hn := c.original_critical_kernel_endpoint_normalized_of_large eK geometry hb
      path hatg hdtg hlarge
    rw [inf_eq_left.mpr hkernel] at hn
    apply hbad
    have hV := ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hatg hdtg
    have hHZd : H ≤ Z R (act R g d) := neighbor_kernel_commutator_le_seed path.start_color hatg hdtg
    have hVH : V R a ≤ normalizer (H : Set _) :=
      ((le_centralizer_iff_isMulCommutative.mpr (V_abelian_of_four_lt R path.start_color hb)).trans
        (centralizer_le (hHZd.trans (le_sup_left.trans hV)))).trans (Subgroup.centralizer_le_normalizer _)
    have hjoin : ⁅Z R (act R g d) ⊔ Z R a,Q R a⁆ = H := le_antisymm
      (commutator_sup_le_of_relative_normal (V R a) (Z R (act R g d)) (Z R a) (Q R a) H
        hVH (le_sup_left.trans hV) (Z_le_VBall R a 2) le_rfl
        ((geometry.centralizes a path.start_color).le.trans bot_le))
      (commutator_mono le_sup_left le_rfl)
    intro x hx
    rw [←hjoin,mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hn hx),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a (hZlocal hx))]
  obtain ⟨back,hbt,hover⟩ := ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
    geometry (by omega) path hatg hdtg hnot
  refine ⟨g,hg,back,hbt,hover,?_,hbad⟩
  rcases c.original_critical_indices_four_or_sixteen eK geometry back with hsmall | hbig
  · exact hsmall.1
  have hr := c.original_large_critical_root_eq_kernels eK geometry back (by rw [hbig.1]; decide)
  have hwQ : Z R (path.walk.getVert (path.walk.length-2)) ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ back.end_color)
    rw [geometry.distance_constant _ back.end_color,SimpleGraph.dist_comm,
      path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hrootH : ⁅Z R (act R g d),Z R (path.walk.getVert (path.walk.length-2))⁆ ≤ H :=
    commutator_mono le_rfl hwQ
  have hHbound := c.original_equal_mover_neighbor_commutator_bound eK geometry (by change 2 < geometry.b R; omega)
    path.start_color hatg hdtg heqg
  let := finite_Z R (act R g d)
  let : Finite H := Finite.of_injective
    (inclusion (neighbor_kernel_commutator_le_seed path.start_color hatg hdtg)) (inclusion_injective _)
  have he : ⁅Z R (act R g d),Z R (path.walk.getVert (path.walk.length-2))⁆ = H :=
    eq_of_le_of_card_ge hrootH (by rw [hr.2.2.2]; exact hHbound)
  apply (hbad ?_).elim
  rw [←he]
  have hwQz : Z R (path.walk.getVert (path.walk.length-2)) ≤ Q R z := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ back.end_color)
    rw [geometry.distance_constant _ back.end_color,path.dist_end,path.length_eq_b]
    change geometry.b R-(geometry.b R-2) < geometry.b R
    omega
  exact (le_centralizer_iff.mp
    ((ChapterC.Sp4Four.DistanceReduction.LargeDistance.critical_commutator_le_endpoint
      ⟨_,_,back⟩).trans (hwQz.trans (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color)))))).trans
          (Subgroup.centralizer_le_normalizer _)

/-- Equal first movers force the original X-layer to equal its natural seed.
For a large starting image the actual backward selector supplies the small
critical path from which this identity transports. -/
theorem original_equal_mover_critical_X_eq_Z
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      ∀ v : Vertex R, color R v = false → X R v = Z R v := by
  intro R geometry hb a z path heq v hv
  rcases c.original_critical_indices_four_or_sixteen eK geometry path with hsmall | hlarge
  · exact c.original_X_eq_Z_at_of_eq path.start_color hv
      (c.original_small_critical_data eK geometry path (by rw [hsmall.1]; decide)).2.2
  · obtain ⟨g,hg,back,hbt,hover,hi,hbad⟩ :=
      c.original_large_equal_mover_backward_small_image eK geometry hb path
        (by rw [hlarge.1]; decide) heq
    exact c.original_X_eq_Z_at_of_eq back.start_color hv
      (c.original_small_critical_data eK geometry back (by rw [hi]; decide)).2.2

/-- The remaining X ≠ Z branch has unequal full movers and only order-sixteen
critical images. The whole-layer alternative is preserved explicitly. -/
theorem original_critical_movers_unequal_of_X_ne_Z
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {v : Vertex R}, color R v = false → X R v ≠ Z R v →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) ≠
        LocalPackage.J R a (path.walk.getVert 1) ∧
      (Q R z).relIndex (Z R a) = 16 ∧ (Q R a).relIndex (Z R z) = 16 := by
  intro R geometry hb v hv hX a z path
  have hne := fun heq => hX (c.original_equal_mover_critical_X_eq_Z eK geometry hb path heq v hv)
  refine ⟨hne,?_⟩
  rcases c.original_critical_indices_four_or_sixteen eK geometry path with hsmall | hlarge
  · exact (hne (c.original_small_critical_first_movers_eq eK geometry hb path
      (by rw [hsmall.1]; decide))).elim
  · exact hlarge

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
