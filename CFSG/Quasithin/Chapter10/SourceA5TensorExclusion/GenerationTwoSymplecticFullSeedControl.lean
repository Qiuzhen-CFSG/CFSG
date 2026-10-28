module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticLargeCritical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalQuadraticXFixed

/-!
# Whole-seed control across equal original movers

The full-X fixed-subgroup theorem gives MS93 (5.3) for the actual canonical
edge mover. Quadratic displacement across equal movers therefore lies in
Z, even when X is strictly larger. Their fixed planes agree, and strict
movement identifies the whole intersection of the two original seeds.

This puts every equal-mover critical root into the literal second seed and
every backward root into the intervening seed. Applied to the proved
radius-index alternatives, it discharges both intermediate-seed containments
for all critical image sizes. The full kernels, original vertices and maps
are retained; no X=Z identity is asserted.

Source: MS93 (5.3), (5.10)--(5.11), printed pp.915,922--924; the original
tensor setting of Aschbacher--Smith 9.3.10, printed pp.734--735.
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

/-- MS93 (5.3) for the whole original X-layer, with its full kernel. -/
theorem original_edge_mover_X_fixed_le_Z
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a t : Vertex R}, color R a = false → Adjacent R a t →
      X R a ⊓ centralizer (LocalPackage.J R a t : Set (FreeAmalgam R)) ≤ Z R a := by
  intro R a t ha hat
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
  have hquad := c.original_edge_mover_quadratic eK ha hat
  rw [c.original_Z_eq_U a ha] at hquad ⊢
  exact original_large_quadratic_X_fixed_le_U R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq ha (c.graph_X_fixed_eq_bot a ha) (LocalPackage.J R a t)
    ((LocalPackage.J_le_radical R a t).trans (fun _ hx => hx.2 a (adjacent_symm R hat)))
    (by rw [(c.original_small_mover_join_indices eK ha hat).2.1]; decide) hquad

/-- Across equal full movers, the kernel displacement belongs to the actual
neighboring seed even when X is larger than Z. -/
theorem original_equal_mover_displacement_le_Z
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false →
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t → ⁅Z R d,Q R a⁆ ≤ Z R a := by
  intro R geometry hb a d t ha hat hdt heq
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [ha] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hQaJ : Q R a ≤ LocalPackage.J R d t := heq ▸
    LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le ha hat
  apply (le_inf (c.original_equal_mover_displacement_le_X eK geometry hb ha hat hdt heq) ?_).trans
    (c.original_edge_mover_X_fixed_le_Z eK ha hat)
  rw [commutator_comm,←heq]
  exact (commutator_mono hQaJ le_rfl).trans (c.original_edge_mover_quadratic eK hd hdt)

/-- A common full mover has the same fixed plane in the two original seeds.
No equality of either whole central omega layer with its seed is required. -/
theorem original_equal_mover_fixed_planes_eq
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false →
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      Z R a ⊓ centralizer (LocalPackage.J R a t : Set (FreeAmalgam R)) =
        Z R d ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R)) := by
  intro R geometry hb a d t ha hat hdt heq
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [ha] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  have step {u v : Vertex R} (hu : color R u = false) (hv : color R v = false)
      (hut : Adjacent R u t) (hvt : Adjacent R v t)
      (heq : LocalPackage.J R v t = LocalPackage.J R u t) :
      Z R u ⊓ centralizer (LocalPackage.J R u t : Set (FreeAmalgam R)) ≤
        Z R v ⊓ centralizer (LocalPackage.J R v t : Set (FreeAmalgam R)) := by
    have hX := c.original_equal_mover_large_subactor_fixed_le_X eK geometry hb hu hut hvt heq
      (LocalPackage.J R u t) le_rfl
      (by rw [(c.original_small_mover_join_indices eK hu hut).2.1]; decide)
    have hC : Z R u ⊓ centralizer (LocalPackage.J R u t : Set (FreeAmalgam R)) ≤
        centralizer (LocalPackage.J R v t : Set (FreeAmalgam R)) := by rw [heq]; exact inf_le_right
    exact le_inf ((le_inf hX hC).trans (c.original_edge_mover_X_fixed_le_Z eK hv hvt)) hC
  exact le_antisymm (step ha hd hat hdt heq) (step hd ha hdt hat heq.symm)

/-- The entire critical commutator belongs to the literal second seed
whenever the first movers agree, for both possible critical image sizes. -/
theorem original_equal_mover_critical_root_le_second_seed
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      ⁅Z R a,Z R z⁆ ≤ Z R (path.walk.getVert 2) := by
  intro R geometry hb a z path heq
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
  have hzQ : Z R z ≤ Q R (path.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt R z (geometry.exists_critical z path.end_color)
    rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,path.dist_end,path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  exact (commutator_mono le_rfl hzQ).trans
    (c.original_equal_mover_displacement_le_Z eK geometry
      (by change 2 < geometry.b R; omega) hd hdt hat heq.symm)

/-- The actual backward critical root lies in the intervening original seed,
including the previously unresolved X ≠ Z branch. -/
theorem original_equal_mover_backward_root_le_seed
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z)
        (_back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2))),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      ⁅Z R d,Z R (path.walk.getVert (path.walk.length-2))⁆ ≤ Z R a := by
  intro R geometry hb a z d t path back hat hdt heq
  have hwQ : Z R (path.walk.getVert (path.walk.length-2)) ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ back.end_color)
    rw [geometry.distance_constant _ back.end_color,SimpleGraph.dist_comm,
      path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  exact (commutator_mono le_rfl hwQ).trans
    (c.original_equal_mover_displacement_le_Z eK geometry
      (by change 2 < geometry.b R; omega) path.start_color hat hdt heq)

/-- Large subactors of a common mover fix only the neighboring full seed,
without the former global X=Z hypothesis. -/
theorem original_equal_mover_large_subactor_fixed_le_Z
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false →
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      ∀ A : Subgroup (FreeAmalgam R), A ≤ LocalPackage.J R a t →
      4 < (Q R a).relIndex A →
      Z R a ⊓ centralizer (A : Set (FreeAmalgam R)) ≤ Z R d := by
  intro R geometry hb a d t ha hat hdt heq A hAJ hlarge
  rw [c.original_large_edge_subactor_fixed_eq eK ha hat A hAJ hlarge,
    c.original_equal_mover_fixed_planes_eq eK geometry hb ha hat hdt heq]
  exact inf_le_left

/-- Strict movement identifies the entire intersection of two original
seeds with their common mover-fixed plane, also in the large-image branch. -/
theorem original_equal_mover_seed_intersection
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      Z R a ⊓ Z R d = Z R a ⊓ centralizer (LocalPackage.J R a t : Set (FreeAmalgam R)) := by
  intro R geometry hb a d t ha hat hdt heq hmove
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [ha] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hB := c.original_neighbor_core_fixed_eq_B eK geometry hb ha hat hdt
    (lt_trans (by decide : 1 < 4) hmove)
  have hm : 4 < (centralizer (Q R a : Set (FreeAmalgam R))).relIndex (Z R d) := by
    rw [←inf_relIndex_left,hB,inf_relIndex_left,c.original_Z_eq_U d hd]
    exact hmove
  have hQaJ : Q R a ≤ LocalPackage.J R d t := by
    rw [heq]
    exact LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le ha hat
  have hfix := c.original_moving_edge_subactor_fixed_eq eK hd hdt (Q R a) hQaJ hm
  have hplanes := c.original_equal_mover_fixed_planes_eq eK geometry hb ha hat hdt heq
  apply le_antisymm
  · apply (le_inf inf_le_right (inf_le_left.trans ?_)).trans (hfix.trans hplanes.symm).le
    exact commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha)
  · rw [hplanes]
    exact le_inf (hplanes.symm.le.trans inf_le_left) inf_le_left

/-- The first numerical branch on the literal original path fixes the
canonical plane at vertex two and therefore lies in the seed at vertex four,
when the two movers across vertex three agree. -/
theorem original_critical_radius_first_seed
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 4) (path.walk.getVert 3) =
        LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 3) →
      4 < (Q R (path.walk.getVert 2)).relIndex (V R z) →
      Z R (path.walk.getVert 2) ⊓ centralizer (V R z : Set (FreeAmalgam R)) ≤
        Z R (path.walk.getVert 4) := by
  intro R geometry hb a z path heq hlarge
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have htwo : color R (path.walk.getVert 2) = false :=
    (path.vertex_color (by omega)).mpr (by decide)
  have hfour : color R (path.walk.getVert 4) = false :=
    (path.vertex_color (by omega)).mpr (by decide)
  have h23 : Adjacent R (path.walk.getVert 2) (path.walk.getVert 3) :=
    (cosetGraph_adj R _ _).mp (path.walk.adj_getVert_succ (by omega : 2 < path.walk.length))
  have h43 : Adjacent R (path.walk.getVert 4) (path.walk.getVert 3) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 3 < path.walk.length)))
  have hVQ : V R z ≤ Q R (path.walk.getVert 4) := by
    apply (V_le_iff R path.end_color _).mpr
    intro d hd hdz
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    change (cosetGraph R).dist d (path.walk.getVert 4) < geometry.b R
    have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := z)
      (w := path.walk.getVert 4)
    have he := path.dist_end 4
    rw [SimpleGraph.dist_comm] at he
    rw [he,path.length_eq_b] at ht
    omega
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hVJ := hVQ.trans (LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le hfour h43)
  rw [heq] at hVJ
  exact c.original_equal_mover_large_subactor_fixed_le_Z eK geometry
    (by change 2 < geometry.b R; omega)
    htwo h23 h43 heq (V R z) hVJ hlarge

/-- The second numerical branch uses the entire radius kernel at the
literal second vertex, not a truncated subgroup. -/
theorem original_critical_radius_second_seed
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      4 < (Q R a).relIndex (V R z ⊓ Q R (path.walk.getVert 2)) →
      Z R a ⊓ centralizer ((V R z ⊓ Q R (path.walk.getVert 2) :
        Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) ≤ Z R (path.walk.getVert 2) := by
  intro R geometry hb a z path heq hlarge
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have htwo : color R (path.walk.getVert 2) = false :=
    (path.vertex_color (by omega)).mpr (by decide)
  have h01 : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have h21 : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hKJ : V R z ⊓ Q R (path.walk.getVert 2) ≤ LocalPackage.J R a (path.walk.getVert 1) := by
    rw [←heq]
    exact inf_le_right.trans (LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le htwo h21)
  exact c.original_equal_mover_large_subactor_fixed_le_Z eK geometry
    (by change 2 < geometry.b R; omega)
    path.start_color h01 h21 heq _ hKJ hlarge


/-- Both actual radius alternatives now give the required intermediate full
seed containment for every critical image size along equal movers. -/
theorem original_equal_mover_radius_root_containment
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z)
        (_back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2))),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      LocalPackage.J R (path.walk.getVert 4) (path.walk.getVert 3) =
        LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 3) →
      (⁅Z R a,Z R z⁆ ≤ Z R (path.walk.getVert 4)) ∨
        (⁅Z R d,Z R (path.walk.getVert (path.walk.length-2))⁆ ≤ Z R (path.walk.getVert 2)) := by
  intro R geometry hb a z d t path back hat hdt heqback heq2 heq4
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have htwo : color R (path.walk.getVert 2) = false :=
    (path.vertex_color (by omega)).mpr (by decide)
  have hfour : color R (path.walk.getVert 4) = false :=
    (path.vertex_color (by omega)).mpr (by decide)
  have hroot2 := c.original_equal_mover_critical_root_le_second_seed eK geometry hb path heq2
  have hrootV : ⁅Z R a,Z R z⁆ ≤ centralizer (V R z : Set (FreeAmalgam R)) :=
    (ChapterC.Sp4Four.DistanceReduction.LargeDistance.critical_commutator_le_endpoint ⟨a,z,path⟩).trans
      (ChapterC.Sp4Four.DistanceReduction.LargeDistance.seed_centralizes_radius_of_distance geometry
        path.end_color path.end_color (by simp; omega))
  have hbackA := c.original_equal_mover_backward_root_le_seed
    eK geometry hb path back hat hdt heqback
  have hbackV : ⁅Z R d,Z R (path.walk.getVert (path.walk.length-2))⁆ ≤
      centralizer (V R z : Set (FreeAmalgam R)) := by
    apply (ChapterC.Sp4Four.DistanceReduction.LargeDistance.critical_commutator_le_endpoint
      ⟨d,_,back⟩).trans
    apply ChapterC.Sp4Four.DistanceReduction.LargeDistance.seed_centralizes_radius_of_distance
      geometry back.end_color path.end_color
    rw [path.dist_end,path.length_eq_b]
    omega
  rcases c.original_critical_radius_index_split eK geometry hb path with h | h
  · exact Or.inl ((le_inf hroot2 hrootV).trans
      (c.original_critical_radius_first_seed eK geometry hb path heq4 h))
  · exact Or.inr ((le_inf hbackA
      (hbackV.trans (centralizer_le (show V R z ⊓ Q R (path.walk.getVert 2) ≤ V R z from inf_le_left)))).trans
        (c.original_critical_radius_second_seed eK geometry hb path heq2 h))

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
