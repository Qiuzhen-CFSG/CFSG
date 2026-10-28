module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticFixedIntersection
public import Theory.GroupTheory.Commutator.NilpotentSaturation

/-!
# Strict movement on the full original tensor geometry

An order-four neighboring commutator cannot be locally normal. Source
2.1(vii) therefore selects a conjugate not normalized by the critical endpoint.
If the seed stays in the truncated kernel, the original root comparison
forces normalization. Otherwise its overlapping backward critical commutator
fills that same order-four subgroup and centralizes the endpoint. Both
alternatives contradict the selection, excluding the small nonzero action.

For index one, the neighboring join is locally normal. Its kernel commutator
is proper in the order-256 seed by nilpotent saturation, and the original
order-seventeen action bound makes it trivial. The full neighboring kernels
then agree, contradicting the reversed critical pair. Thus the B-index is
strictly greater than four at the literal second vertex of every original
critical path with b>4. This supplies unconditional overlapping backward
paths, without assuming the small-root branch or a strict-index callback.

Source: MS93 (2.1)(vii), (5.7)--(5.9), pp.856,919--922, specialized to the
center-free original tensor case of Aschbacher--Smith 9.3.10, pp.734--735.
The large-distance and distance-four exclusions and SymplecticPlaneRecognition
remain open.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterC.Sp4Four.DistanceReduction.StrictIndex
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

/-- The full edge kernel normalizes the nonzero small commutator. Its failure
of local normality gives an actual escaping endpoint conjugate by source2.1(vii). -/
theorem original_small_kernel_commutator_escape
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z d t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      Nat.card (⁅Z R d,Q R a⁆ : Subgroup (FreeAmalgam R)) = 4 →
      ∃ g ∈ stabilizer R a,
        ¬ Z R z ≤ normalizer (⁅Z R (act R g d),Q R a⁆ : Subgroup (FreeAmalgam R)) := by
  intro R geometry hb a z d t path hat hdt hcardH
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
      (by change Nat.card H ≤ 128; change Nat.card H = 4 at hcardH; omega)
    change Nat.card H = 4 at hcardH
    rw [hzero,card_bot] at hcardH
    omega
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

/-- An escaping small commutator supplies the original backward critical path.
The same conjugator and its failure of normalization are retained. -/
theorem original_backward_path_of_small_kernel_commutator
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
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
    · obtain ⟨heq,hrootcard⟩ := c.original_neighbor_kernel_commutator eK geometry hb path
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

/-- A nontrivial critical action with commutator order at most four has order
exactly four on the full original natural layer. -/
theorem original_critical_commutator_card_four_of_small
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (_path : CriticalPath R geometry a z),
      Nat.card (⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) ≤ 4 →
      Nat.card (⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) = 4 := by
  intro R geometry a z path hsmall
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hcard,hsq,hQne⟩ :=
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
  have hself : centralizer (pCore 2 c.M : Set c.M) ≤ pCore 2 c.M := by
    simpa only [c.fitting_center.1] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := c.M))
  have hne : R ≠ ⊥ := fun hr => hQne (le_bot_iff.mp (hr ▸ hodd.twoCore_le))
  have hpos : 0 < geometry.b R := lt_of_lt_of_le (by decide : 0 < 4)
    (c.original_geometry_four_le eK geometry)
  let := geometry.Z_elementary hpos a path.start_color
  have hfixed : U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    rw [←c.original_fixedCore_eq_bot z path.end_color]
    exact le_inf (inf_le_left.trans ((U_le_Z z).trans
      ((geometry.omega_bound z path.end_color
        (by rwa [geometry.distance_constant z path.end_color])).trans (omegaCenter_le _)))) inf_le_right
  have hlocal : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  rw [c.original_Z_eq_U z path.end_color] at hsmall ⊢
  have hi := original_small_commutator_centralizer_index R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path.end_color hfixed (Z R a) hlocal hsmall
  obtain ⟨F,hF,f,hf,j,hj,hjr,hact,hdim,himage,hH,hquad⟩ :=
    original_small_actor_marking R hms hodd.isPGroup hne hodd.twoCore_le hself hfaith
      q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      hcard hBC hsq path.end_color hfixed (Z R a) hlocal hi
  apply hH.resolve_left
  intro hzero
  have hcomm := commutator_eq_bot_iff_le_centralizer.mp (card_eq_one.mp hzero)
  apply path.critical.2
  rw [←C_eq_Q R hodd.isPGroup hodd.twoCore_le hfaith z path.end_color]
  exact le_inf hlocal (by rwa [c.original_Z_eq_U z path.end_color])

/-- The newly constructed backward critical commutator fills the small kernel
commutator and centralizes the original endpoint, contradicting its selection. -/
theorem original_small_kernel_commutator_impossible
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      Nat.card (⁅Z R d,Q R a⁆ : Subgroup (FreeAmalgam R)) = 4 →
      False := by
  intro R geometry hb a z d t path hat hdt hcard
  obtain ⟨g,hg,hbad,⟨back,_,_⟩,_⟩ :=
    c.original_backward_path_of_small_kernel_commutator eK geometry hb path hat hdt hcard
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
  have hwVz : Z R w ≤ V R z := by
    have hd : (cosetGraph R).dist w z ≤ 2 := by
      change (cosetGraph R).dist (path.walk.getVert (path.walk.length-2)) z ≤ 2
      rw [path.dist_end]
      omega
    exact le_iSup_of_le w (le_iSup_of_le hd le_rfl)
  apply hbad
  exact (le_centralizer_iff.mp
    ((hHZw.trans hwVz).trans
      ((le_centralizer_iff_isMulCommutative.mpr (V_abelian_of_four_lt R path.end_color hb)).trans
        (centralizer_le (Z_le_VBall R z 2))))).trans (Subgroup.centralizer_le_normalizer _)

/-- The entire original central omega layer has residual commutator Z,
without an assumption X=Z or a critical-distance restriction. -/
theorem original_X_residual_commutator
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a : Vertex R}, color R a = false → ⁅X R a,Ltilde R a⁆ = Z R a := by
  intro R a ha
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hinit := source_tensor_sp4_initialCore D m.sylow_not_normalizes_component c.M
    (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
    c.outside c.sylow (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq
    eK c.fitting_center.1 c.component_product.2.2.2
  obtain ⟨i,hi,_,hiL,hiU,hiQ⟩ := vertex_coordinates_with_kernel R hodd.isPGroup hodd.twoCore_le ha
  have hXmap : (omegaCenterIn (pCore 2 c.M)).map i = X R a := by
    change (omegaCenter (pCore 2 c.M)).map i = omegaCenter (Q R a)
    rw [←hiQ,omegaCenter_map _ _ hi]
  rw [←hXmap,←hiL,←map_commutator,←hinit,hiU,←c.original_Z_eq_U a ha]

/-- Every genuinely moving neighbor has B-index greater than four when b>4.
Both the trivial-action and order-four-action alternatives are excluded. -/
theorem original_strict_movement_of_moving_neighbor
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
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
    exact c.original_small_kernel_commutator_impossible eK geometry hb path hat hdt hcard

/-- A neighboring seed contained in B centralizes the full starting kernel.
Nilpotent saturation removes the order-256 case before the small normal-core bound. -/
theorem original_nonmoving_neighbor_commutator_eq_bot
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      Z R d ≤ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a) →
      ⁅Z R d,Q R a⁆ = ⊥ := by
  intro R geometry hb a d t ha hat hdt hB
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [ha] at h
    cases he : color R t <;> simp_all
  have hd : color R d = false := by
    have h := adjacent_color_ne R hdt
    rw [ht] at h
    cases he : color R d <;> simp_all
  let W := Z R d ⊔ Z R a
  let N := ⁅W,Q R a⁆
  have hgen : pResidual 2 c.M ⊔ R = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨k,hk,r,hr,rfl⟩ := c.component_product.2.2.2 x
    exact Subgroup.mul_mem _ (mem_sup_left hk) (mem_sup_right hr)
  have hNW : stabilizer R a ≤ normalizer (W : Set _) :=
    neighbor_join_normalized_of_le_B geometry hb hgen ha hat hdt hB
  have hWQ : W ≤ Q R a :=
    (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt).trans
      (geometry.V_le_Q hb a ha)
  have hNZ : N ≤ Z R d :=
    commutator_sup_le_of_relative_normal (Q R a) (Z R d) (Z R a) (Q R a) (Z R d)
      (((Q_le_adjacent_h R ht hat).trans
        (show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt))).trans
          (Z_normalized R d))
      (le_sup_left.trans hWQ) (le_sup_right.trans hWQ)
      (neighbor_kernel_commutator_le_seed ha hat hdt)
      ((geometry.centralizes a ha).le.trans bot_le)
  have hNN : stabilizer R a ≤ normalizer (N : Set _) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hNW hx),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a hx)]
  let := finite_Z R d
  let : Finite N := Finite.of_injective (inclusion hNZ) (inclusion_injective _)
  have hZd : Nat.card (Z R d) = 256 := c.original_Z_card eK d hd
  have hNc : Nat.card N ≤ 256 :=
    (Nat.card_le_card_of_injective (inclusion hNZ) (inclusion_injective _)).trans_eq hZd
  have hNzero : N = ⊥ := by
    by_cases hfull : Nat.card N = 256
    · have hNZeq : N = Z R d := eq_of_le_of_card_ge hNZ (by rw [hZd,hfull])
      let := finite_stabilizer R a
      let : Finite (Q R a) := Finite.of_injective
        (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)) (inclusion_injective _)
      have hnil := (Q_isPGroup R hodd.isPGroup hodd.twoCore_le a ha).isNilpotent
      have hWZ : W ≤ Z R a := le_of_le_sup_commutator_of_isNilpotent
        (Q R a) W (Z R a) (Q R a) hnil hWQ (le_sup_right.trans hWQ) le_rfl
        ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Z_normalized R a))
        (by change Z R d ⊔ Z R a ≤ Z R a ⊔ N; rw [hNZeq,sup_comm])
      exact le_bot_iff.mp ((commutator_mono hWZ le_rfl).trans (geometry.centralizes a ha).le)
    · have hmul := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R)) N (Z R d) bot_le hNZ
      rw [relIndex_bot_left,relIndex_bot_left,hZd] at hmul
      have hindex : 2 ≤ N.relIndex (Z R d) := by
        by_contra! hh
        interval_cases he : N.relIndex (Z R d) <;> simp_all
      have hsmall : Nat.card N ≤ 128 := by nlinarith
      exact c.original_small_normal_core_eq_bot eK ha N (hNZ.trans (le_sup_left.trans hWQ))
        ((Ltilde_le_stabilizer a).trans hNN) hsmall
  exact le_bot_iff.mp ((commutator_mono le_sup_left le_rfl).trans_eq hNzero)

/-- Original source5.9 at the literal second vertex of the critical path.
The full-kernel comparison excludes index one, so no movement premise remains. -/
theorem original_critical_strict_movement
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex
        (U R (path.walk.getVert 2)) := by
  intro R geometry hb a z path
  let d := path.walk.getVert 2
  let t := path.walk.getVert 1
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a t := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R d t := adjacent_symm R ((cosetGraph_adj R _ _).mp
    (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hd : color R d = false := (path.vertex_color (by omega : 2 ≤ path.walk.length)).mpr (by decide)
  apply c.original_strict_movement_of_moving_neighbor eK geometry hb path hat hdt
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

/-- Unconditional original backward existence for b>4, retaining the common
edge, every overlapping vertex, and escape of the full radius. -/
theorem original_backward_path
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      ∃ d t, Adjacent R a t ∧ Adjacent R d t ∧
        (∃ back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=t ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  intro R geometry hb a z path
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  exact c.original_backward_path_of_strict_mover eK geometry hb path hat hdt
    (c.original_critical_strict_movement eK geometry hb path)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
