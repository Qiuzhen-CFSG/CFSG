module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticRadiusFixedPlanes
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalMovingPlane

/-!
# Full intermediate seeds in the original symplectic argument

The full neighboring kernel fixes exactly the B-intersection of a moving
seed. In the small-critical-image branch, the proved identity X = Z
transports to every original-group vertex. Strict movement and the natural
quadratic action then identify the entire intersection of neighboring seeds
with the canonical mover's fixed plane.

The existing separated selector consequently has a trivial intersection of
its three full seeds. Its backward critical root belongs to the intermediate
seed and escapes the mate seed. On the literal original overlapping paths,
the two radius-index alternatives insert the required critical root into
the second or fourth seed, without an assumed X = Z or seed containment.

The equal-mover conditions and the remaining positioning on repeated paths
are still explicit. These results do not prove the large-distance or
distance-four contradiction or the marked plane recognition theorem.

Source: MS93 (5.6), (5.9)--(5.11), printed pp.917--924;
Aschbacher--Smith 9.3.10 and the final paragraph of 9.3, pp.734--735.
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

/-- A subactor moving more than four cosets of the original natural seed
fixes exactly the same subgroup as the canonical mover. -/
theorem original_moving_edge_subactor_fixed_eq
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a t : Vertex R}, color R a = false → Adjacent R a t →
      ∀ A : Subgroup (FreeAmalgam R), A ≤ LocalPackage.J R a t →
      4 < (centralizer (A : Set (FreeAmalgam R))).relIndex (Z R a) →
      Z R a ⊓ centralizer (A : Set (FreeAmalgam R)) =
        Z R a ⊓ centralizer (LocalPackage.J R a t : Set (FreeAmalgam R)) := by
  intro R a t ha hat A hAJ hlarge
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
  obtain ⟨geometry,hpos,_⟩ := c.exists_positive_even_geometry eK
  have hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hcore : x ∈ fixedCore R a := ⟨
      ((U_le_Z a).trans (geometry.omega_bound a ha
        (by
          rw [geometry.distance_constant a ha]
          change 0 < geometry.b R
          exact hpos)) |>.trans (omegaCenter_le _)) hx.1,hx.2⟩
    rwa [c.original_fixedCore_eq_bot a ha] at hcore
  have hquad := c.original_edge_mover_quadratic eK ha hat
  rw [c.original_Z_eq_U a ha] at hquad hlarge ⊢
  apply original_moving_quadratic_subactor_fixed_eq R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq ha hfixed A (LocalPackage.J R a t) hAJ
    ((LocalPackage.J_le_radical R a t).trans (fun _ hx => hx.2 a (adjacent_symm R hat)))
    (by rw [(c.original_small_mover_join_indices eK ha hat).2.1]; decide) hlarge hquad


/-- A layer identity at one original-group vertex transports to every
vertex of the same color, by the original conjugation maps. -/
theorem original_X_eq_Z_at_of_eq :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a d : Vertex R}, color R a = false → color R d = false →
      X R a = Z R a → X R d = Z R d := by
  intro R a d ha hd heq
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color R ha
  obtain ⟨h,rfl⟩ := exists_mVertex_of_color R hd
  have hga : act R g (alpha R) = mVertex R g := by simp [alpha,act_mVertex]
  have hha : act R h (alpha R) = mVertex R h := by simp [alpha,act_mVertex]
  rw [←hga,X_act,Z_act] at heq
  have hbase := Subgroup.map_injective (MulAut.conj g⁻¹).injective heq
  rw [←hha,X_act,Z_act,hbase]

/-- The full neighboring kernel fixes exactly the B-intersection of a
moving seed. The reverse containment uses the original X-commutator identity. -/
theorem original_neighbor_core_fixed_eq_B
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      1 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      Z R d ⊓ centralizer (Q R a : Set (FreeAmalgam R)) =
        Z R d ⊓ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a) := by
  intro R geometry hb a d t ha hat hdt hmove
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [ha] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  let C₀ := Z R d ⊓ centralizer (Q R a : Set (FreeAmalgam R))
  have hDV : Z R d ≤ V R a := le_sup_left.trans
    (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)
  have hCX : C₀ ≤ X R a := by
    let := geometry.Z_elementary (by omega) d hd
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨(hDV.trans (geometry.V_le_Q hb a ha)) hx.1,
      elemPow_eq_one_of_isElementaryAbelian x hx.1,hx.2⟩
  have hCB := ChapterC.Sp4Four.DistanceReduction.radius_le_B_of_commutator
    geometry hb ha C₀ (inf_le_left.trans hDV)
    ((commutator_mono hCX le_rfl).trans_eq (c.original_X_residual_commutator eK ha))
  apply le_antisymm (le_inf inf_le_left hCB)
  have hBX := (c.original_moving_neighbor_fixed_intersection eK geometry hb ha hat hdt hmove).1
  rw [←c.original_Z_eq_U d hd] at hBX
  exact le_inf inf_le_left (hBX.trans (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2))

/-- Strict movement identifies the whole intersection of two equal-mover
seeds with the canonical fixed plane. Both original cores are retained. -/
theorem original_equal_mover_seed_intersection_fixed_plane
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t → X R a = Z R a →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      Z R a ⊓ Z R d = Z R a ⊓ centralizer (LocalPackage.J R a t : Set (FreeAmalgam R)) := by
  intro R geometry hb a d t ha hat hdt heq hXa hmove
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [ha] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  have hXd := c.original_X_eq_Z_at_of_eq ha hd hXa
  have hZaQd : Z R a ≤ Q R d :=
    (le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hdt hat)).trans
      (geometry.V_le_Q hb d hd)
  have hZdQa : Z R d ≤ Q R a :=
    (le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)).trans
      (geometry.V_le_Q hb a ha)
  have fixed_seed {u v : Vertex R} (hu : color R u = false)
      (hUV : Z R u ≤ Q R v) (hX : X R v = Z R v) :
      Z R u ⊓ centralizer (Q R v : Set (FreeAmalgam R)) = Z R u ⊓ Z R v := by
    apply le_antisymm
    · let := geometry.Z_elementary (by omega) u hu
      intro x hx
      refine ⟨hx.1,?_⟩
      rw [←hX]
      exact mem_omegaCenter_iff.mpr ⟨hUV hx.1,
        elemPow_eq_one_of_isElementaryAbelian x hx.1,hx.2⟩
    · exact inf_le_inf_left _ (hX ▸ (fun _ hx => (mem_omegaCenter_iff.mp hx).2.2))
  have hCd := fixed_seed hd hZdQa hXa
  have hCa := fixed_seed ha hZaQd hXd
  have hB := c.original_neighbor_core_fixed_eq_B eK geometry hb ha hat hdt
    (lt_trans (by decide : 1 < 4) hmove)
  rw [hCd] at hB
  have hmove' : 4 < (Z R a).relIndex (Z R d) := by
    rw [←c.original_Z_eq_U d hd,←inf_relIndex_left,←hB,inf_relIndex_left] at hmove
    exact hmove
  let := finite_Z R a
  let := finite_Z R d
  let : Finite (Z R a ⊓ Z R d : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hm1 := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (Z R a ⊓ Z R d) (Z R a) bot_le inf_le_left
  have hm2 := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (Z R a ⊓ Z R d) (Z R d) bot_le inf_le_right
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,c.original_Z_card eK a ha] at hm1
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,c.original_Z_card eK d hd] at hm2
  have he : (Z R d).relIndex (Z R a) = (Z R a).relIndex (Z R d) := by
    have hp : 0 < Nat.card (Z R a ⊓ Z R d : Subgroup (FreeAmalgam R)) := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hp
    exact hm1.trans hm2.symm
  have hlarge : 4 < (centralizer (Q R d : Set (FreeAmalgam R))).relIndex (Z R a) := by
    rw [←inf_relIndex_left,hCa,inf_relIndex_left,he]
    exact hmove'
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hQdJ : Q R d ≤ LocalPackage.J R a t := heq ▸
    LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le hd hdt
  rw [←hCa]
  exact c.original_moving_edge_subactor_fixed_eq eK ha hat (Q R d) hQdJ hlarge

/-- The actual paired selector has disjoint full neighboring seed
intersections, not only disjoint displacements. -/
theorem original_equal_mover_selected_seed_intersection_eq_bot
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t → X R a = Z R a →
      ∀ x ∈ stabilizer R a,
      ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
        centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      Z R a ⊓ Z R d ⊓ Z R (act R x d) = ⊥ := by
  intro R geometry hb a d t ha hat hdt heq hXa x hx hsep hmove
  have hfix : act R x a = a := hx
  have hatx : Adjacent R a (act R x t) := by
    simpa only [hfix] using (adjacent_act_iff R x _ _).mpr hat
  have hdtx := (adjacent_act_iff R x _ _).mpr hdt
  have heqx : LocalPackage.J R (act R x d) (act R x t) = LocalPackage.J R a (act R x t) := by
    rw [←hfix,smallMoverJoin_act,smallMoverJoin_act,heq]
  have hmovex : 4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
      (geometry.Z_normal a)).relIndex (U R (act R x d)) := by
    rw [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega) ha x hx]
    exact hmove
  have h1 := c.original_equal_mover_seed_intersection_fixed_plane eK geometry
    (by change 2 < geometry.b R; omega) ha hat hdt heq hXa hmove
  have h2 := c.original_equal_mover_seed_intersection_fixed_plane eK geometry
    (by change 2 < geometry.b R; omega) ha hatx hdtx heqx hXa hmovex
  apply le_bot_iff.mp
  rw [←hsep]
  intro y hy
  have hy1 : y ∈ Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R)) := by
    rw [heq,←h1]
    exact hy.1
  have hy2 : y ∈ Z R a ⊓ centralizer
      (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R)) := by
    rw [heqx,←h2]
    exact ⟨hy.1.1,hy.2⟩
  exact ⟨hy1,hy2.2⟩


/-- In the small-image branch the full backward critical commutator
belongs to the original intermediate seed. No seed-containment premise is used. -/
theorem original_equal_mover_backward_root_le_intermediate_seed
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z)
        (_back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2))),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t → X R a = Z R a →
      ⁅Z R d,Z R (path.walk.getVert (path.walk.length-2))⁆ ≤ Z R a := by
  intro R geometry hb a z d t path back hat hdt heq hXa
  have hwQ : Z R (path.walk.getVert (path.walk.length-2)) ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ back.end_color)
    rw [geometry.distance_constant _ back.end_color,SimpleGraph.dist_comm,
      path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  exact ((commutator_mono le_rfl hwQ).trans
    (c.original_equal_mover_displacement_le_X eK geometry
      (by change 2 < geometry.b R; omega) path.start_color hat hdt heq)).trans_eq hXa

/-- Once the original equal-mover selector gives a backward path, its
critical root escapes the entire mate seed, using strict movement and the
literal paired fixed-plane separation. -/
theorem original_equal_mover_selected_backward_root_escapes_mate
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z)
        (_back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2))),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t → X R a = Z R a →
      ∀ x ∈ stabilizer R a,
      ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
        centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      ¬ ⁅Z R d,Z R (path.walk.getVert (path.walk.length-2))⁆ ≤ Z R (act R x d) := by
  intro R geometry hb a z d t path back hat hdt heq hXa x hx hsep hmove hmate
  have hroot := c.original_equal_mover_backward_root_le_intermediate_seed
    eK geometry hb path back hat hdt heq hXa
  have hzero := c.original_equal_mover_selected_seed_intersection_eq_bot
    eK geometry hb path.start_color hat hdt heq hXa x hx hsep hmove
  have hbot : ⁅Z R d,Z R (path.walk.getVert (path.walk.length-2))⁆ ≤ ⊥ := by
    rw [←hzero]
    exact le_inf (le_inf hroot
      (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed back)) hmate
  exact c.original_critical_commutator_not_le_vertex_center eK geometry back path.start_color
    (hbot.trans bot_le)

/-- Apply the new full-seed separation to the actual source selector on a
small critical path. Strict movement, the layer identity and both mate
movements are all discharged on this choice. -/
theorem original_small_critical_paired_seed_separation
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) < 16 →
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
        let d₁ := act R g⁻¹ (path.walk.getVert 2)
        let t₁ := act R g⁻¹ (path.walk.getVert 1)
        let d₂ := act R x d₁
        let t₂ := act R x t₁
        let w := path.walk.getVert (path.walk.length-2)
        Adjacent R a t₁ ∧ Adjacent R d₁ t₁ ∧
        LocalPackage.J R d₁ t₁ = LocalPackage.J R a t₁ ∧
        Ltilde R a ≤ (LocalPackage.J R d₁ t₁ ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) ∧
        Z R a ⊓ Z R d₁ ⊓ Z R d₂ = ⊥ ∧
        ((∃ back : CriticalPath R geometry d₁ w,
          back.walk.getVert 1=t₁ ∧
          (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
          ⁅Z R d₁,Z R w⁆ ≤ Z R a ∧ ¬ ⁅Z R d₁,Z R w⁆ ≤ Z R d₂) ∨
        (∃ back : CriticalPath R geometry d₂ w,
          back.walk.getVert 1=t₂ ∧
          (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
          ⁅Z R d₂,Z R w⁆ ≤ Z R a ∧ ¬ ⁅Z R d₂,Z R w⁆ ≤ Z R d₁)) := by
  intro R geometry hb a z path hsmall heq
  obtain ⟨g,hg,x,hx,hat,hdt,heq',hgen,hsep,hmove,hback,_⟩ :=
    c.original_small_critical_paired_selection eK geometry hb path hsmall heq
  have hXa := (c.original_small_critical_data eK geometry path hsmall).2.2
  have hxS := Ltilde_le_stabilizer a hx
  have hzero := c.original_equal_mover_selected_seed_intersection_eq_bot
    eK geometry hb path.start_color hat hdt heq' hXa x hxS hsep hmove
  refine ⟨g,hg,x,hx,hat,hdt,heq',hgen,hzero,?_⟩
  rcases hback with ⟨back,hbt,hover⟩ | ⟨back,hbt,hover⟩
  · exact Or.inl ⟨back,hbt,hover,
      c.original_equal_mover_backward_root_le_intermediate_seed eK geometry hb path back hat hdt heq' hXa,
      c.original_equal_mover_selected_backward_root_escapes_mate eK geometry hb path back
        hat hdt heq' hXa x hxS hsep hmove⟩
  · have hfix : act R x a = a := hxS
    have hatx : Adjacent R a (act R x (act R g⁻¹ (path.walk.getVert 1))) := by
      simpa only [hfix] using (adjacent_act_iff R x _ _).mpr hat
    have hdtx := (adjacent_act_iff R x _ _).mpr hdt
    have heqx : LocalPackage.J R (act R x (act R g⁻¹ (path.walk.getVert 2)))
        (act R x (act R g⁻¹ (path.walk.getVert 1))) =
        LocalPackage.J R a (act R x (act R g⁻¹ (path.walk.getVert 1))) := by
      rw [smallMoverJoin_act,heq']
      have hh := smallMoverJoin_act R x a (act R g⁻¹ (path.walk.getVert 1))
      simpa only [hfix] using hh.symm
    have hroot := c.original_equal_mover_backward_root_le_intermediate_seed
      eK geometry hb path back hatx hdtx heqx hXa
    refine Or.inr ⟨back,hbt,hover,hroot,?_⟩
    intro hmate
    have hbot : ⁅Z R (act R x (act R g⁻¹ (path.walk.getVert 2))),
        Z R (path.walk.getVert (path.walk.length-2))⁆ ≤ ⊥ := by
      rw [←hzero]
      exact le_inf (le_inf hroot hmate)
        (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed back)
    exact c.original_critical_commutator_not_le_vertex_center eK geometry back path.start_color
      (hbot.trans bot_le)


/-- The small critical root lies in the literal second seed once the
first mover pair agrees. The proof transports the established X=Z identity. -/
theorem original_small_critical_root_le_second_seed
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) < 16 →
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      ⁅Z R a,Z R z⁆ ≤ Z R (path.walk.getVert 2) := by
  intro R geometry hb a z path hsmall heq
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hd : color R (path.walk.getVert 2) = false :=
    (path.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hX := c.original_X_eq_Z_at_of_eq path.start_color hd
    (c.original_small_critical_data eK geometry path hsmall).2.2
  have hzQ : Z R z ≤ Q R (path.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt R z (geometry.exists_critical z path.end_color)
    rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,path.dist_end,path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  exact ((commutator_mono le_rfl hzQ).trans
    (c.original_equal_mover_displacement_le_X eK geometry
      (by change 2 < geometry.b R; omega) hd hdt hat heq.symm)).trans_eq hX

/-- Both radius-index alternatives now insert their critical commutator
into the required intermediate full seed on the original overlapping paths.
The equal-mover hypotheses remain explicit; there is no assumed X=Z identity,
strict-movement bound or intermediate-seed containment. -/
theorem original_small_critical_radius_root_containment
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z)
        (_back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2))),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      (Q R z).relIndex (Z R a) < 16 →
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      LocalPackage.J R (path.walk.getVert 4) (path.walk.getVert 3) =
        LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 3) →
      (⁅Z R a,Z R z⁆ ≤ Z R (path.walk.getVert 4)) ∨
        (⁅Z R d,Z R (path.walk.getVert (path.walk.length-2))⁆ ≤ Z R (path.walk.getVert 2)) := by
  intro R geometry hb a z d t path back hat hdt heqback hsmall heq2 heq4
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have htwo : color R (path.walk.getVert 2) = false :=
    (path.vertex_color (by omega)).mpr (by decide)
  have hfour : color R (path.walk.getVert 4) = false :=
    (path.vertex_color (by omega)).mpr (by decide)
  have hXa := (c.original_small_critical_data eK geometry path hsmall).2.2
  have hXtwo := c.original_X_eq_Z_at_of_eq path.start_color htwo hXa
  have hXfour := c.original_X_eq_Z_at_of_eq path.start_color hfour hXa
  have hroot2 := c.original_small_critical_root_le_second_seed eK geometry hb path hsmall heq2
  have hrootV : ⁅Z R a,Z R z⁆ ≤ centralizer (V R z : Set (FreeAmalgam R)) :=
    (ChapterC.Sp4Four.DistanceReduction.LargeDistance.critical_commutator_le_endpoint ⟨a,z,path⟩).trans
      (ChapterC.Sp4Four.DistanceReduction.LargeDistance.seed_centralizes_radius_of_distance geometry
        path.end_color path.end_color (by simp; omega))
  have hbackA := c.original_equal_mover_backward_root_le_intermediate_seed
    eK geometry hb path back hat hdt heqback hXa
  have hbackV : ⁅Z R d,Z R (path.walk.getVert (path.walk.length-2))⁆ ≤
      centralizer (V R z : Set (FreeAmalgam R)) := by
    apply (ChapterC.Sp4Four.DistanceReduction.LargeDistance.critical_commutator_le_endpoint
      ⟨d,_,back⟩).trans
    apply ChapterC.Sp4Four.DistanceReduction.LargeDistance.seed_centralizes_radius_of_distance
      geometry back.end_color path.end_color
    rw [path.dist_end,path.length_eq_b]
    omega
  rcases c.original_critical_radius_fixed_plane_alternative eK geometry hb path heq4 heq2 with h | h
  · exact Or.inl (((le_inf hroot2 hrootV).trans h).trans_eq hXfour)
  · exact Or.inr (((le_inf hbackA
      (hbackV.trans (centralizer_le (show V R z ⊓ Q R (path.walk.getVert 2) ≤ V R z from inf_le_left)))).trans h).trans_eq hXtwo)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
