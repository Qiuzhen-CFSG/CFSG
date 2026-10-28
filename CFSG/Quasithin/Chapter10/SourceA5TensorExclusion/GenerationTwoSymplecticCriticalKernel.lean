module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticOrbitPaths

/-!
# Full selected critical kernels in the original tensor geometry

The seed centralizer equality identifies the literal critical intersection
Z_a intersect Q_z with the full fixed subgroup of Z_z on Z_a. If its index
is at most four, the canonical small mover at the first edge normalizes
this entire kernel. The argument uses the original natural marking and
retains the whole neighborhood kernel.

Strict movement shows that this kernel escapes the B-layer of the adjacent
M-vertex. Its join with that vertex's seed has section order at most 128,
so the order-seventeen action bound prevents the full residual from
normalizing it. The final application carries these facts along the actual
backward critical paths, with all conjugators, overlaps and paired
commutator centrality on the same sequence.

This supplies the small-mover normalization and nonnormality needed in
MS93 (5.10)--(5.11), pp.922--924. Normalization by the other selected
generators, the stronger radius bound and the two distance exclusions
remain to be proved. It does not assert SymplecticPlaneRecognition.
The original tensor application is Aschbacher--Smith 9.3.10, pp.734--735.
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

/-- The full critical kernel is the fixed subgroup of the opposite seed,
using the exact original centralizer equality. -/
theorem original_critical_seed_kernel_eq_centralizer
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (_path : CriticalPath R geometry a z),
      Z R a ⊓ Q R z = Z R a ⊓ centralizer (Z R z : Set (FreeAmalgam R)) := by
  intro R geometry a z path
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hC := C_eq_Q R hodd.isPGroup hodd.twoCore_le hfaith z path.end_color
  have hlocal : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  rw [←hC]
  change Z R a ⊓ (stabilizer R z ⊓ centralizer (Z R z : Set _)) = _
  rw [←inf_assoc,inf_eq_left.mpr hlocal]

/-- The canonical mover normalizes the complete critical kernel when its
index is at most four. The common edge and the endpoint placement are literal. -/
theorem original_critical_small_kernel_normalized
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → (cosetGraph R).dist z t < geometry.b R →
      (Q R z).relIndex (Z R a) ≤ 4 →
      LocalPackage.J R a t ≤ normalizer ((Z R a ⊓ Q R z : Subgroup (FreeAmalgam R)) : Set _) := by
  intro R geometry a z t path hat hdist hsmall
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
  have hb : 0 < geometry.b R := lt_of_lt_of_le (by decide : 0 < 4)
    (c.original_geometry_four_le eK geometry)
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [path.start_color] at h
    cases he : color R t <;> simp_all
  have hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hcore : x ∈ fixedCore R a := ⟨
      ((U_le_Z a).trans (geometry.omega_bound a path.start_color
        (by rwa [geometry.distance_constant a path.start_color])) |>.trans (omegaCenter_le _)) hx.1,hx.2⟩
    rwa [c.original_fixedCore_eq_bot a path.start_color] at hcore
  have hcentral : (centralizer (Z R z : Set (FreeAmalgam R))).relIndex (U R a) ≤ 4 := by
    rw [←c.original_Z_eq_U a path.start_color,←inf_relIndex_left,
      ←c.original_critical_seed_kernel_eq_centralizer eK geometry path,inf_relIndex_left]
    exact hsmall
  obtain ⟨i,_,_,hiT,_,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le
    path.start_color hat
  have hQt : IsPGroup 2 (Q R t) := hiT ▸ hodd.isPGroup.map i
  have hzT : Z R z ≤ Q R t := Z_le_Q_of_dist_lt R z
    (geometry.exists_critical z path.end_color)
    (by rwa [geometry.distance_constant z path.end_color])
  have hn := original_small_mover_join_normalizes_kernel R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path.start_color hfixed (Q R t) (Z R z) hQt
    (fun _ hx => hx.2 a (adjacent_symm R hat)) (Q_le_adjacent_h R ht hat) hzT hcentral
  change LocalPackage.J R a t ≤ normalizer
    ((U R a ⊓ centralizer (Z R z : Set _) : Subgroup (FreeAmalgam R)) : Set _) at hn
  rwa [←c.original_Z_eq_U a path.start_color,
    ←c.original_critical_seed_kernel_eq_centralizer eK geometry path] at hn

private theorem original_neighbor_section_le_B
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
theorem original_critical_small_kernel_obstruction
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
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
  exact hnot (le_sup_left.trans (c.original_neighbor_section_le_B eK geometry
    (by change 2 < geometry.b R; omega) hd hdt hat H (sup_le_sup inf_le_left le_rfl) hn))

/-- Apply the kernel calculation to the actual backward path, preserving
the prescribed conjugator, the first edge and every overlap vertex. -/
theorem original_backward_small_kernel_configuration
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      ∃ g ∈ stabilizer R a,
        ∃ back : CriticalPath R geometry (act R g (path.walk.getVert 2))
            (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1 = act R g (path.walk.getVert 1) ∧
          (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
          ((Q R (path.walk.getVert (path.walk.length-2))).relIndex
              (Z R (act R g (path.walk.getVert 2))) ≤ 4 →
            let K := Z R (act R g (path.walk.getVert 2)) ⊓
              Q R (path.walk.getVert (path.walk.length-2))
            let H := K ⊔ Z R a
            LocalPackage.J R (act R g (path.walk.getVert 2)) (back.walk.getVert 1) ≤
                normalizer (H : Set _) ∧
              (¬ K ≤ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)) ∧
              (¬ Ltilde R a ≤ normalizer (H : Set _))) := by
  intro R geometry hb a z path
  obtain ⟨g,hg,back,hbt,hover⟩ := c.original_backward_path_with_conjugator eK geometry hb path
  refine ⟨g,hg,back,hbt,hover,?_⟩
  intro hsmall
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hblen : 4 < back.walk.length := by rwa [back.length_eq_b]
  have hdt : Adjacent R (act R g (path.walk.getVert 2)) (back.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (back.walk.adj_getVert_succ (by omega : 0 < back.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hat : Adjacent R a (back.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simp only [SimpleGraph.Walk.getVert_zero] at h
    have hga : act R g a = a := hg
    rw [hbt]
    simpa only [hga] using (adjacent_act_iff R g _ _).mpr h
  have hdist : (cosetGraph R).dist (path.walk.getVert (path.walk.length-2))
      (back.walk.getVert 1) < geometry.b R := by
    rw [SimpleGraph.dist_comm,back.dist_end,back.length_eq_b]
    change geometry.b R-1 < geometry.b R
    omega
  apply c.original_critical_small_kernel_obstruction eK geometry hb back hdt hat hdist hsmall
  rw [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega)
    path.start_color g hg]
  exact c.original_critical_strict_movement eK geometry hb path

/-- On the same original overlapping sequence, every small critical kernel
has the source mover normalization and residual nonnormality. The orbit and
paired commutator conditions are retained on this very sequence. -/
theorem original_overlapping_small_kernel_sequence
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R → ∀ p : CriticalSegment geometry,
      ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
        (∀ n, BackwardLink geometry
          (fun q d t => ∃ g ∈ stabilizer R q.first,
            d=act R g (q.path.walk.getVert 2) ∧ t=act R g (q.path.walk.getVert 1))
          (s n) (s (n+1))) ∧
        (∀ n k i, i+2*k ≤ geometry.b R →
          (s (n+k)).path.walk.getVert (i+2*k) = (s n).path.walk.getVert i) ∧
        (∀ n, ∃ g ∈ stabilizer R (s (n+1)).first,
          act R g (s n).first=(s (n+2)).first) ∧
        ⁅⁅Z R (s 2).first,Z R (s 2).last⁆ ⊔
          ⁅Z R (s 3).first,Z R (s 3).last⁆,V R (s 2).last⁆ = ⊥ ∧
        (∀ n, (Q R (s (n+1)).last).relIndex (Z R (s (n+1)).first) ≤ 4 →
          let K := Z R (s (n+1)).first ⊓ Q R (s (n+1)).last
          let H := K ⊔ Z R (s n).first
          LocalPackage.J R (s (n+1)).first ((s (n+1)).path.walk.getVert 1) ≤
              normalizer (H : Set _) ∧
            (¬ K ≤ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R (s n).first
              (geometry.Z_normal (s n).first)) ∧
            (¬ Ltilde R (s n).first ≤ normalizer (H : Set _))) := by
  intro R geometry hb p
  obtain ⟨s,hs0,hs,hover,horbit,hcent⟩ :=
    c.original_overlapping_sequence_with_conjugators eK geometry hb p
  refine ⟨s,hs0,hs,hover,horbit,hcent,?_⟩
  intro n hsmall
  obtain ⟨t,⟨g,hg,hd,ht⟩,hat,hdt,hbt⟩ := (hs n).choice
  have hdist : (cosetGraph R).dist (s (n+1)).last t < geometry.b R := by
    rw [←hbt,SimpleGraph.dist_comm,(s (n+1)).path.dist_end,(s (n+1)).path.length_eq_b]
    change geometry.b R-1 < geometry.b R
    omega
  rw [hbt]
  apply c.original_critical_small_kernel_obstruction eK geometry hb
    (s (n+1)).path hdt hat hdist hsmall
  rw [hd,ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega)
    (s n).path.start_color g hg]
  exact c.original_critical_strict_movement eK geometry hb (s n).path

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup

