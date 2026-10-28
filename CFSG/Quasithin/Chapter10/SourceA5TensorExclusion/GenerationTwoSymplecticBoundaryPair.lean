module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticBoundaryLarge

/-!
# The original paired kernels at the distance-four boundary

The selected critical kernel is not contained in the original B-layer:
its index is four whereas the full neighboring seed has strictly larger
B-index. Thus its join with the starting seed is not normalized by the
whole residual. If a selected mate were contained in the penultimate
kernel, the two endpoint displacement bounds and the canonical mover
would make all three residual generators normalize that join. Both
selected members therefore give actual backward critical paths.

The two separated mover-fixed planes also force the selected seeds to
commute, despite noncommutativity of the full radius. Their disjoint
displacements on the penultimate seed identify the complete pair kernel
and give the product of the two literal image orders. Both images have
order four, so the paired image has order sixteen. The final consumer
retains both conjugators, both paths, every overlap vertex, the three
generators, full kernels and endpoint displacements on one actual choice.

This is a strengthened original configuration for the remaining small-image
contradiction of MS93 (5.12); it does not prove that contradiction or the
full original marked-plane recognition.
Source: MS93 (3.3)(ii), (5.6)--(5.7), (5.12)(1)--(3), printed pp.866--867,
917--919,924--927; Aschbacher--Smith 9.3.10, printed pp.734--735.
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

private theorem boundary_neighbor_section_le_B
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      ∀ H : Subgroup (FreeAmalgam R), H ≤ Z R d ⊔ Z R a →
      Ltilde R a ≤ normalizer (H : Set _) →
      H ≤ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a) := by
  intro R geometry hb a d t ha hat hdt H hH hn
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
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
  obtain ⟨π,hπ,hπker⟩ := local_residual_projection R hodd.isPGroup hodd.twoCore_le
    q (QuotientGroup.ker_mk' _) ha
  have hHV : H ≤ V R a := hH.trans
    (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)
  have hHQ := hHV.trans (geometry.V_le_Q hb a ha)
  have hHG : H ≤ stabilizer R a := hHQ.trans (fun _ hx => hx.1)
  let := finite_stabilizer R a
  let : Finite (Ltilde R a) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer a)) (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion hHG) (inclusion_injective _)
  have hcomm : ⁅H,Ltilde R a⁆ ≤ Z R a :=
    commutator_le_of_twoPerfect_simple_seventeen_section_le_128
      (Ltilde R a) H (Z R a) (isPPerfect_embedded_pResidual_of_finite 2 _) π hπ hπker
      (by rw [hcard]; decide)
      ((Q_isPGroup R hodd.isPGroup hodd.twoCore_le a ha).to_le hHQ) hn
      ((Ltilde_le_stabilizer a).trans (Z_normalized R a))
      (normal_subgroupOf_of_le_normalizer (hHG.trans (Z_normalized R a)))
      (by
        let : Finite (Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) :=
          Finite.of_injective (inclusion
            ((ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt).trans
              ((geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)))) (inclusion_injective _)
        exact (relIndex_le_of_le_right hH index_ne_zero_of_finite).trans
          (c.original_neighbor_join_index_le_128 eK geometry
            (by change 0 < geometry.b R; omega) ha hat hdt))
  exact ChapterC.Sp4Four.DistanceReduction.radius_le_B_of_commutator geometry hb ha H hHV hcomm


/-- The selected small kernel escapes the neighboring B-layer. Its join
with the neighboring seed is normalized by the canonical mover, but not by
the entire neighboring residual. -/
private theorem boundary_small_kernel_obstruction
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z d t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t → (cosetGraph R).dist z t < geometry.b R →
      (Q R z).relIndex (Z R a) ≤ 4 →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R d (geometry.Z_normal d)).relIndex (U R a) →
      let K := Z R a ⊓ Q R z
      let H := K ⊔ Z R d
      LocalPackage.J R a t ≤ normalizer (H : Set _) ∧
        (¬ K ≤ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R d (geometry.Z_normal d)) ∧
        (¬ Ltilde R d ≤ normalizer (H : Set _)) := by
  intro R geometry hb a z d t path hat hdt hdist hsmall hmove K H
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [path.start_color] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  have hK := c.original_critical_small_kernel_normalized eK geometry path hat hdist hsmall
  have hZd : LocalPackage.J R a t ≤ normalizer (Z R d : Set (FreeAmalgam R)) :=
    (LocalPackage.J_le_radical R a t).trans
      ((show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt)).trans
        (Z_normalized R d))
  have hnot : ¬ K ≤ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R d (geometry.Z_normal d) :=
    selected_kernel_not_le_B geometry hsmall hmove
  refine ⟨(le_inf hK hZd).trans (normalizer_inf_normalizer_le_normalizer_sup _ _),hnot,?_⟩
  intro hn
  exact hnot (le_sup_left.trans (c.boundary_neighbor_section_le_B eK geometry
    (by change 2 < geometry.b R; omega) hd hdt hat H (sup_le_sup inf_le_left le_rfl) hn))

private theorem boundary_small_critical_mate_impossible
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z)
        (back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2))),
      Adjacent R a t → Adjacent R d t → back.walk.getVert 1=t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      ∀ x ∈ Ltilde R a,
      Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      (Q R (path.walk.getVert (path.walk.length-2))).relIndex (Z R d) ≤ 4 →
      Z R (act R x d) ≤ Q R (path.walk.getVert (path.walk.length-2)) → False := by
  intro R geometry hb a z d t path back hat hdt hbt heq x hx hgen hmove hsmall hmate
  let K := Z R d ⊓ Q R (path.walk.getVert (path.walk.length-2))
  let Y := K ⊔ Z R a
  have hdist : (cosetGraph R).dist (path.walk.getVert (path.walk.length-2)) t < geometry.b R := by
    rw [←hbt,SimpleGraph.dist_comm,back.dist_end,back.length_eq_b]
    omega
  obtain ⟨hJ,_,hnot⟩ := c.boundary_small_kernel_obstruction eK geometry hb back
    hdt hat hdist hsmall hmove
  obtain ⟨hd₁,hd₂⟩ := c.original_boundary_generated_pair_displacement eK geometry hb path
    hat hdt heq x hx hgen
  rw [inf_eq_left.mpr hmate] at hd₂
  have hxS : x ∈ stabilizer R a := Ltilde_le_stabilizer a hx
  have hZaMap : (Z R a).map (MulAut.conj x).toMonoidHom = Z R a :=
    mem_normalizer_iff_map_conj_eq.mp ((Z_normalized R a) hxS)
  have hdMap : (Z R (act R x d)).map (MulAut.conj x).toMonoidHom = Z R d := by
    have hh := Z_act R x⁻¹ (act R x d)
    rw [←act_mul,mul_inv_cancel,act_one] at hh
    simpa only [inv_inv] using hh.symm
  have heMap : (Z R z).map (MulAut.conj x).toMonoidHom = Z R (act R x⁻¹ z) := by
    simpa only [inv_inv] using (Z_act R x⁻¹ z).symm
  have hthird := map_mono (f := (MulAut.conj x).toMonoidHom) hd₂
  rw [map_commutator,Subgroup.map_sup,hZaMap,hdMap,heMap] at hthird
  have hN₁ : Z R z ≤ normalizer (Y : Set (FreeAmalgam R)) :=
    le_normalizer_iff_commutator_le_left.mpr (hd₁.trans le_sup_right)
  have hN₂ : Z R (act R x⁻¹ z) ≤ normalizer (Y : Set (FreeAmalgam R)) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono (sup_le_sup inf_le_left le_rfl) le_rfl).trans hthird).trans le_sup_right)
  exact hnot (hgen.trans (sup_le (sup_le hJ hN₁) hN₂))

private theorem boundary_conjugate_three_generators
    {R : Subgroup c.M} {a z d t : Vertex R} {x : FreeAmalgam R}
    (hx : x ∈ Ltilde R a)
    (hgen : Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z)) :
    Ltilde R a ≤ (LocalPackage.J R (act R x d) (act R x t) ⊔ Z R z) ⊔
      Z R (act R x z) := by
  have h := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hgen
  have hL : (Ltilde R a).map (MulAut.conj x⁻¹).toMonoidHom = Ltilde R a :=
    mem_normalizer_iff_map_conj_eq.mp
    ((Ltilde R a).le_normalizer ((Ltilde R a).inv_mem hx))
  rw [hL,Subgroup.map_sup,Subgroup.map_sup,←smallMoverJoin_act,←Z_act,←Z_act,
    ←act_mul,inv_mul_cancel,act_one] at h
  simpa only [sup_assoc,sup_comm,sup_left_comm] using h


private theorem boundary_pair_both_backward
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      ∀ x ∈ Ltilde R a,
      Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      let w := path.walk.getVert (path.walk.length-2)
      ((∃ back : CriticalPath R geometry d w, back.walk.getVert 1=t) ∨
        (∃ back : CriticalPath R geometry (act R x d) w, back.walk.getVert 1=act R x t)) →
      (∃ back : CriticalPath R geometry d w, back.walk.getVert 1=t ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
      (∃ back : CriticalPath R geometry (act R x d) w, back.walk.getVert 1=act R x t ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) := by
  intro R geometry a z d t path hat hdt heq x hx hgen hmove w hback
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  have hxS : x ∈ stabilizer R a := Ltilde_le_stabilizer a hx
  have hfix : act R x a = a := hxS
  have hat₂ : Adjacent R a (act R x t) := by
    simpa only [hfix] using (adjacent_act_iff R x _ _).mpr hat
  have hdt₂ := (adjacent_act_iff R x _ _).mpr hdt
  have heq₂ : LocalPackage.J R (act R x d) (act R x t) = LocalPackage.J R a (act R x t) := by
    rw [←hfix,smallMoverJoin_act,smallMoverJoin_act,heq]
  have hmove₂ : 4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
      (geometry.Z_normal a)).relIndex (U R (act R x d)) := by
    rw [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega)
      path.start_color x hxS]
    exact hmove
  have hn : ¬ Z R d ≤ Q R w ∧ ¬ Z R (act R x d) ≤ Q R w := by
    rcases hback with ⟨back,hbt⟩ | ⟨back,hbt⟩
    · refine ⟨back.critical.2,?_⟩
      exact c.boundary_small_critical_mate_impossible eK geometry hb path back hat hdt hbt
        heq x hx hgen hmove (c.original_critical_images_four eK geometry back).1.le
    · refine ⟨?_,back.critical.2⟩
      intro hk
      have hgen₂ : Ltilde R a ≤ (LocalPackage.J R (act R x d) (act R x t) ⊔ Z R z) ⊔
          Z R (act R (x⁻¹)⁻¹ z) := by
        rw [inv_inv]
        exact c.boundary_conjugate_three_generators hx hgen
      exact c.boundary_small_critical_mate_impossible eK geometry hb path back hat₂ hdt₂ hbt
        heq₂ x⁻¹ ((Ltilde R a).inv_mem hx) hgen₂ hmove₂
        (c.original_critical_images_four eK geometry back).1.le
        (by
          change Z R (act R x⁻¹ (act R x d)) ≤ Q R w
          simpa only [←act_mul,mul_inv_cancel,act_one] using hk)
  exact ⟨ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
      geometry hb.le path hat hdt hn.1,
    ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
      geometry hb.le path hat₂ hdt₂ hn.2⟩

private theorem boundary_neighbor_displacement_fixed
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (_geometry : Geometry R) {a d t : Vertex R}, color R a = false →
      Adjacent R a t → Adjacent R d t →
      ∀ W ≤ Q R a,
      ⁅Z R d,W⁆ ≤ Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R)) := by
  intro R geometry a d t ha hat hdt W hW
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  have heq := c.original_neighbor_movers_eq eK geometry ha hat hdt
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [ha] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hWJ : W ≤ LocalPackage.J R d t := hW.trans
    (heq ▸ LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le ha hat)
  refine le_inf ((commutator_mono le_rfl hW).trans
    (c.original_equal_mover_displacement_le_Z eK geometry hb ha hat hdt heq)) ?_
  rw [commutator_comm]
  exact (commutator_mono hWJ le_rfl).trans (c.original_edge_mover_quadratic eK hd hdt)

/-- The two actually separated neighboring seeds commute even though the
full radius is nonabelian at distance four. Their mutual displacement lies
in both disjoint mover-fixed planes of the original starting seed. -/
theorem original_boundary_separated_seeds_commute
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (_geometry : Geometry R) {a d t : Vertex R}, color R a = false →
      Adjacent R a t → Adjacent R d t → ∀ x ∈ stabilizer R a,
      ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
        centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ →
      ⁅Z R d,Z R (act R x d)⁆ = ⊥ := by
  intro R geometry a d t ha hat hdt x hx hsep
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  have hfix : act R x a = a := hx
  have hat₂ : Adjacent R a (act R x t) := by
    simpa only [hfix] using (adjacent_act_iff R x _ _).mpr hat
  have hdt₂ := (adjacent_act_iff R x _ _).mpr hdt
  have hpairQ := (ChapterC.Sp4Four.DistanceReduction.paired_seed_le_radius hat hdt x hx).trans
    (geometry.V_le_Q hb a ha)
  have h₁ := c.boundary_neighbor_displacement_fixed eK geometry ha hat hdt
    (Z R (act R x d)) (le_sup_right.trans hpairQ)
  have h₂ := c.boundary_neighbor_displacement_fixed eK geometry ha hat₂ hdt₂
    (Z R d) (le_sup_left.trans hpairQ)
  rw [commutator_comm] at h₂
  exact le_bot_iff.mp ((le_inf h₁ (h₂.trans inf_le_right)).trans_eq hsep)

/-- Separation gives independent displacement subgroups on every subgroup
of the original full starting kernel, also at distance four. -/
theorem original_boundary_separated_displacements
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (_geometry : Geometry R) {a d t : Vertex R}, color R a = false →
      Adjacent R a t → Adjacent R d t → ∀ x ∈ stabilizer R a,
      ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
        centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ →
      ∀ W ≤ Q R a, Disjoint ⁅Z R d,W⁆ ⁅Z R (act R x d),W⁆ := by
  intro R geometry a d t ha hat hdt x hx hsep W hW
  have hfix : act R x a = a := hx
  have hat₂ : Adjacent R a (act R x t) := by
    simpa only [hfix] using (adjacent_act_iff R x _ _).mpr hat
  have hdt₂ := (adjacent_act_iff R x _ _).mpr hdt
  have h₁ := c.boundary_neighbor_displacement_fixed eK geometry ha hat hdt W hW
  have h₂ := c.boundary_neighbor_displacement_fixed eK geometry ha hat₂ hdt₂ W hW
  apply disjoint_iff.mpr
  exact le_bot_iff.mp
    ((le_inf (inf_le_left.trans h₁) (inf_le_right.trans (h₂.trans inf_le_right))).trans_eq hsep)

/-- The full kernel of the separated pair splits into its two complete
seed kernels, and its quotient image order is their product. -/
theorem original_boundary_separated_pair_kernel_image
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a d t w : Vertex R}, color R a = false → color R w = false →
      Adjacent R a t → Adjacent R d t →
      (cosetGraph R).dist a w + 2 ≤ geometry.b R →
      ∀ x ∈ stabilizer R a,
      ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
        centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ →
      ((Z R d ⊔ Z R (act R x d)) ⊓ Q R w =
        (Z R d ⊓ Q R w) ⊔ (Z R (act R x d) ⊓ Q R w)) ∧
      (Q R w).relIndex (Z R d ⊔ Z R (act R x d)) =
        (Q R w).relIndex (Z R d) * (Q R w).relIndex (Z R (act R x d)) := by
  intro R geometry a d t w ha hw hat hdt hd x hx hsep
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  have hpairV := ChapterC.Sp4Four.DistanceReduction.paired_seed_le_radius hat hdt x hx
  have hVS := radius_le_stabilizer_of_distance R geometry ha hd
  have hAS := (le_sup_left.trans hpairV).trans hVS
  have hBS := (le_sup_right.trans hpairV).trans hVS
  have hW : Z R w ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R w (geometry.exists_critical w hw)
    rw [geometry.distance_constant w hw,SimpleGraph.dist_comm]
    change (cosetGraph R).dist a w < geometry.b R
    omega
  have hdis := c.original_boundary_separated_displacements eK geometry ha hat hdt x hx hsep
    (Z R w) hW
  have hBA : Z R (act R x d) ≤ normalizer (Z R d : Set (FreeAmalgam R)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (c.original_boundary_separated_seeds_commute eK geometry ha hat hdt x hx hsep))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hprod := centralizer_relIndex_sup_of_disjoint_commutators
    (Z R d) (Z R (act R x d)) (Z R w)
    (hAS.trans (Z_normalized R w)) (hBS.trans (Z_normalized R w)) hBA hdis
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hC := C_eq_Q R hodd.isPGroup hodd.twoCore_le hfaith w hw
  have hker (Y : Subgroup (FreeAmalgam R)) (hYS : Y ≤ stabilizer R w) :
      Y ⊓ Q R w = Y ⊓ centralizer (Z R w : Set (FreeAmalgam R)) := by
    rw [←hC]
    change Y ⊓ (stabilizer R w ⊓ centralizer (Z R w : Set _)) = _
    rw [←inf_assoc,inf_eq_left.mpr hYS]
  have hind (Y : Subgroup (FreeAmalgam R)) (hYS : Y ≤ stabilizer R w) :
      (Q R w).relIndex Y = (centralizer (Z R w : Set (FreeAmalgam R))).relIndex Y := by
    rw [←inf_relIndex_left,←hC]
    change (Y ⊓ (stabilizer R w ⊓ centralizer (Z R w : Set _))).relIndex Y = _
    rw [←inf_assoc,inf_eq_left.mpr hYS,inf_relIndex_left]
  constructor
  · rw [hker _ (sup_le hAS hBS),hker _ hAS,hker _ hBS]
    exact centralizer_inf_sup_of_disjoint_commutators
      (Z R d) (Z R (act R x d)) (Z R w)
      (hAS.trans (Z_normalized R w)) (hBS.trans (Z_normalized R w)) hBA hdis
  · rw [hind _ (sup_le hAS hBS),hind _ hAS,hind _ hBS]
    exact hprod


/-- Every original critical path supplies two commuting, separated backward
critical seeds. Both literal images have order four, their joint image has
order sixteen, and the complete kernels retain endpoint displacement into
the starting seed. No small-image, mover or distance assumption is added. -/
theorem original_boundary_pair_configuration
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (path : CriticalPath R geometry a z),
      ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
        let d := act R g⁻¹ (path.walk.getVert 2)
        let t := act R g⁻¹ (path.walk.getVert 1)
        let w := path.walk.getVert (path.walk.length-2)
        let K₁ := Z R d ⊓ Q R w
        let K₂ := Z R (act R x d) ⊓ Q R w
        Adjacent R a t ∧ Adjacent R d t ∧
        LocalPackage.J R d t = LocalPackage.J R a t ∧
        Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) ∧
        ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
          centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ ∧
        4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) ∧
        (∃ back : CriticalPath R geometry d w, back.walk.getVert 1=t ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        (∃ back : CriticalPath R geometry (act R x d) w, back.walk.getVert 1=act R x t ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ⁅Z R d,Z R (act R x d)⁆ = ⊥ ∧
        ((Z R d ⊔ Z R (act R x d)) ⊓ Q R w = K₁ ⊔ K₂) ∧
        (Q R w).relIndex (Z R d) = 4 ∧
        (Q R w).relIndex (Z R (act R x d)) = 4 ∧
        (Q R w).relIndex (Z R d ⊔ Z R (act R x d)) = 16 ∧
        ⁅K₁ ⊔ Z R a,Z R z⁆ ≤ Z R a ∧ ⁅K₂ ⊔ Z R a,Z R z⁆ ≤ Z R a := by
  intro R geometry a z path
  have hs : (Q R z).relIndex (Z R a) < 16 := by
    rw [(c.original_critical_images_four eK geometry path).1]; decide
  obtain ⟨g,hg,x,hx,hat,hdt,heq,hgen,hsep,hmove,hback,hdisp⟩ :=
    c.original_boundary_small_critical_kernel_selection eK geometry path hs
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  have hlen : 2 < path.walk.length := by rwa [path.length_eq_b]
  have hbacks := c.boundary_pair_both_backward eK geometry path hat hdt heq x hx hgen hmove
    (hback.imp (fun ⟨p,ht,_⟩ => ⟨p,ht⟩) (fun ⟨p,ht,_⟩ => ⟨p,ht⟩))
  obtain ⟨back₁,ht₁,ho₁⟩ := hbacks.1
  obtain ⟨back₂,ht₂,ho₂⟩ := hbacks.2
  have hi₁ := (c.original_critical_images_four eK geometry back₁).1
  have hi₂ := (c.original_critical_images_four eK geometry back₂).1
  have hxS := Ltilde_le_stabilizer a hx
  have hdist : (cosetGraph R).dist a (path.walk.getVert (path.walk.length-2))+2 ≤ geometry.b R := by
    rw [path.dist_start (Nat.sub_le _ _),Nat.sub_add_cancel (by omega : 2 ≤ path.walk.length)]
    exact path.length_eq_b.le
  obtain ⟨hker,hprod⟩ := c.original_boundary_separated_pair_kernel_image eK geometry
    path.start_color back₁.end_color hat hdt hdist x hxS hsep
  have hpair : (Q R (path.walk.getVert (path.walk.length-2))).relIndex
      (Z R (act R g⁻¹ (path.walk.getVert 2)) ⊔
        Z R (act R x (act R g⁻¹ (path.walk.getVert 2)))) = 16 := by
    rw [hprod,hi₁,hi₂]
  exact ⟨g,hg,x,hx,hat,hdt,heq,hgen,hsep,hmove,
    ⟨back₁,ht₁,ho₁⟩,⟨back₂,ht₂,ho₂⟩,
    c.original_boundary_separated_seeds_commute eK geometry path.start_color hat hdt x hxS hsep,
    hker,hi₁,hi₂,hpair,hdisp⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
