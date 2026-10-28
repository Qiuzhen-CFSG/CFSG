module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticRadiusKernelAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalAbelianKernelDisplacement

/-!
# Original critical movers and radius centrality at distance four

A neighboring seed whose mover generates the full residual with the critical
endpoint must lie in the penultimate kernel: either possible image of a
backward critical path gives a nontrivial subgroup of the original fixed core.
The join of two seeds on one edge is abelian already for b > 2. The original
hyperplane calculation therefore identifies its critical-root commutator at
b = 4 as well. The natural marking bounds the centralizer index and makes the
selected mover centralize that root.

For a small critical image, unequal movers would now centralize a nontrivial
critical root inside the zero fixed core. Thus all neighboring movers agree.
Their displacement bound excludes the actual mixed triple commutator selected
by a failure of radius centrality. This proves [V_a,Q_a] ≤ C(V_a) on every
original radius, with the full kernels and possible outer action retained.

The terminal distance-four contradiction and the full original marked plane
recognition remain separate obligations.

Source: MS93 (3.3)(ii), (5.2)(ii), (5.5)--(5.7), printed pp.866--867,
914--919; Aschbacher--Smith 9.3.10, pp.734--735.
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

private theorem generated_backward_small_impossible_at_four
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z)
        (back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2))),
      Adjacent R a t → Adjacent R d t → back.walk.getVert 1 = t →
      Ltilde R a ≤ LocalPackage.J R d t ⊔ Z R z →
      (Q R (path.walk.getVert (path.walk.length-2))).relIndex (Z R d) ≤ 4 → False := by
  intro R geometry hb a z d t path back hat hdt hbt hsmallgen hsmall
  let w := path.walk.getVert (path.walk.length-2)
  let H := ⁅Z R d,Z R w⁆
  have hdist : (cosetGraph R).dist w t < geometry.b R := by
    rw [←hbt,SimpleGraph.dist_comm,back.dist_end,back.length_eq_b]
    omega
  have hJ : H ≤ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R)) :=
    c.original_critical_small_commutator_centralizes_mover eK geometry back hdt hdist hsmall
  have hwQ : Z R w ≤ Q R z := by
    apply Z_le_Q_of_dist_lt R w (geometry.exists_critical w back.end_color)
    rw [geometry.distance_constant w back.end_color,path.dist_end,path.length_eq_b]
    change geometry.b R-(geometry.b R-2) < geometry.b R
    omega
  have hHw : H ≤ Z R w := critical_commutator_le_endpoint ⟨d,w,back⟩
  have hZ : H ≤ centralizer (Z R z : Set (FreeAmalgam R)) :=
    hHw.trans (hwQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color))))
  have hL : H ≤ centralizer (Ltilde R a : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (hsmallgen.trans
      (sup_le (le_centralizer_iff.mp hJ) (le_centralizer_iff.mp hZ)))
  have hHQ : H ≤ Q R a :=
    (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed back).trans
      ((le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)).trans
        (geometry.V_le_Q (by omega) a path.start_color))
  have hzero : H ≤ fixedCore R a := le_inf hHQ hL
  rw [c.original_fixedCore_eq_bot a path.start_color] at hzero
  exact c.original_critical_commutator_not_le_vertex_center eK geometry back path.start_color
    (hzero.trans bot_le)

private theorem generated_backward_large_impossible_at_four
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z)
        (back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2))),
      Adjacent R a t → Adjacent R d t → back.walk.getVert 1 = t →
      Ltilde R a ≤ LocalPackage.J R d t ⊔ Z R z →
      4 < (Q R (path.walk.getVert (path.walk.length-2))).relIndex (Z R d) → False := by
  intro R geometry hb a z d t path back hat hdt hbt hgen hlarge
  let w := path.walk.getVert (path.walk.length-2)
  let H := Z R d ⊓ centralizer (Q R t : Set (FreeAmalgam R))
  have hpos : 0 < geometry.b R := by omega
  have rev := c.original_critical_reverse eK geometry hpos back
  have hlarge' : 4 < (Q R d).relIndex (Z R w) := by
    by_contra! hsmall
    have hdata := c.original_small_critical_data eK geometry rev (lt_of_le_of_lt hsmall (by decide : 4 < 16))
    rw [hdata.2.1] at hlarge
    omega
  have hwQt : Z R w ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R w (geometry.exists_critical w back.end_color)
    rw [geometry.distance_constant w back.end_color,←hbt,SimpleGraph.dist_comm,back.dist_end,back.length_eq_b]
    change geometry.b R - 1 < geometry.b R
    omega
  have hHroot : H ≤ ⁅Z R d,Z R w⁆ :=
    (inf_le_inf_left _ (centralizer_le hwQt)).trans
      (c.original_large_critical_fixed_le_root eK geometry back hlarge')
  have hwQz : Z R w ≤ Q R z := by
    apply Z_le_Q_of_dist_lt R w (geometry.exists_critical w back.end_color)
    rw [geometry.distance_constant w back.end_color,path.dist_end,path.length_eq_b]
    change geometry.b R - (geometry.b R - 2) < geometry.b R
    omega
  have hHZ : H ≤ centralizer (Z R z : Set (FreeAmalgam R)) :=
    (hHroot.trans (ChapterC.Sp4Four.DistanceReduction.LargeDistance.critical_commutator_le_endpoint
      ⟨d,w,back⟩)).trans (hwQz.trans (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color))))
  have hHJ : H ≤ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R)) :=
    inf_le_right.trans (centralizer_le (LocalPackage.J_le_radical R d t))
  have hHL : H ≤ centralizer (Ltilde R a : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (hgen.trans
      (sup_le (le_centralizer_iff.mp hHJ) (le_centralizer_iff.mp hHZ)))
  have hHQ : H ≤ Q R a := inf_le_left.trans
    ((le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)).trans
      (geometry.V_le_Q (by omega) a path.start_color))
  have hHbot : H = ⊥ := by
    apply le_bot_iff.mp
    rw [←c.original_fixedCore_eq_bot a path.start_color]
    exact le_inf hHQ hHL
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨i,_,_,hiT,_,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le
    back.start_color hdt
  have hpT : IsPGroup 2 (Q R t) := hiT ▸ hodd.isPGroup.map i
  have ht : color R t = true := by
    have h := adjacent_color_ne R hdt
    rw [back.start_color] at h
    cases he : color R t <;> simp_all
  have hZdT : Z R d ≤ Q R t :=
    ((geometry.omega_bound d back.start_color
      (by rw [geometry.distance_constant d back.start_color]; exact hpos)).trans (omegaCenter_le _)).trans
        (Q_le_adjacent_h R ht hdt)
  have hn : Q R t ≤ normalizer (Z R d : Set (FreeAmalgam R)) :=
    (show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt)).trans
      (Z_normalized R d)
  have hne : Z R d ≠ ⊥ := by
    intro heq
    have hc := c.original_Z_card eK d back.start_color
    rw [heq,card_bot] at hc
    omega
  let := finite_stabilizer R t
  let : Finite (Q R t) := Finite.of_injective
    (inclusion (show Q R t ≤ stabilizer R t from fun _ hx => hx.1)) (inclusion_injective _)
  let N := (Z R d).subgroupOf (Q R t)
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Nontrivial (Z R d) := (nontrivial_iff_ne_bot _).mpr hne
  let : Nontrivial N := (subgroupOfEquivOfLe hZdT).toEquiv.nontrivial
  let : Fact (IsPGroup 2 (Q R t)) := ⟨hpT⟩
  obtain ⟨x,hxne,hxc⟩ := exists_nontrivial_center_mem_normal N (p := 2)
  have hxH : ((x : Q R t) : FreeAmalgam R) ∈ H := by
    refine ⟨x.property,?_⟩
    intro y hy
    exact congrArg Subtype.val ((mem_center_iff.mp hxc) ⟨y,hy⟩)
  rw [hHbot] at hxH
  exact hxne (Subtype.ext (Subtype.ext (mem_bot.mp hxH)))

/-- The actual generated neighbor seed belongs to the full penultimate kernel,
including at the distance-four boundary. -/
theorem original_generated_neighbor_seed_le_penultimate_kernel
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      Ltilde R a ≤ LocalPackage.J R d t ⊔ Z R z →
      Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  intro R geometry a z d t path hat hdt hgen
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  by_contra hn
  obtain ⟨back,hbt,_⟩ := ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
    geometry (by omega) path hat hdt hn
  by_cases hs : (Q R (path.walk.getVert (path.walk.length-2))).relIndex (Z R d) ≤ 4
  · exact generated_backward_small_impossible_at_four c eK geometry hb path back hat hdt hbt hgen hs
  · exact generated_backward_large_impossible_at_four c eK geometry hb path back hat hdt hbt hgen
      (Nat.lt_of_not_ge hs)

/-- If a neighboring seed join is locally normal, its kernel commutator is
an invariant subgroup of order at most 128 and vanishes. With X=Z, the full
neighboring seeds and then their maximum movers coincide. -/
theorem original_normal_neighbor_join_movers_eq
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (_geometry : Geometry R) {a d t : Vertex R}, color R a = false →
      Adjacent R a t → Adjacent R d t → X R a = Z R a →
      stabilizer R a ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      Z R d = Z R a ∧ LocalPackage.J R d t = LocalPackage.J R a t := by
  intro R geometry a d t ha hat hdt hX hn
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  have ht : color R t = true := by
    have hh := adjacent_color_ne R hat
    rw [ha] at hh
    cases he : color R t <;> simp_all
  have hd : color R d = false := by
    have hh := adjacent_color_ne R hdt
    rw [ht] at hh
    cases he : color R d <;> simp_all
  have hQN : Q R a ≤ normalizer (Z R d : Set (FreeAmalgam R)) :=
    ((Q_le_adjacent_h R ht hat).trans
      (show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt))).trans
      (Z_normalized R d)
  have hZdQ : Z R d ≤ Q R a :=
    (le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)).trans
      (geometry.V_le_Q hb a ha)
  have hZaQ : Z R a ≤ Q R a := (Z_le_VBall R a 2).trans (geometry.V_le_Q hb a ha)
  let N := ⁅Z R d,Q R a⁆
  have hNZ : N ≤ Z R d := le_normalizer_iff_commutator_le_left.mp hQN
  have heq : ⁅Z R d ⊔ Z R a,Q R a⁆ = N := by
    apply le_antisymm
    · exact commutator_sup_le_of_relative_normal (Q R a) (Z R d) (Z R a) (Q R a) N
        (normalizer_commutator_ge_right _ _) hZdQ hZaQ le_rfl
        ((geometry.centralizes a ha).le.trans bot_le)
    · exact commutator_mono le_sup_left le_rfl
  have hnN : stabilizer R a ≤ normalizer (N : Set (FreeAmalgam R)) := by
    intro g hg
    rw [←heq,mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hn hg),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a hg)]
  have hzero : N = ⊥ := c.original_small_normal_core_eq_bot eK ha N (hNZ.trans hZdQ)
    ((Ltilde_le_stabilizer a).trans hnN)
    (c.original_neighbor_commutator_card_le_128 eK geometry hb ha hat hdt)
  have hZa : Z R d ≤ Z R a := by
    rw [←hX]
    let := geometry.Z_elementary (by omega) d hd
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hZdQ hx,elemPow_eq_one_of_isElementaryAbelian x hx,
      (commutator_eq_bot_iff_le_centralizer.mp hzero) hx⟩
  let := finite_Z R a
  have hseeds : Z R d = Z R a := eq_of_le_of_card_ge hZa (by
    rw [c.original_Z_card eK d hd,c.original_Z_card eK a ha])
  refine ⟨hseeds,?_⟩
  apply (c.original_neighbor_mover_eq_iff_quadratic eK ha hat hdt).mpr
  rw [←hseeds]
  exact c.original_edge_mover_quadratic eK hd hdt

/-- The original unequal-mover selector at distance four retains full
residual generation, puts the entire selected seed in the penultimate kernel,
and forces failure of endpoint normalization of its join with the starting seed. -/
theorem original_small_unequal_four_selection
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t ≠ LocalPackage.J R a t →
      (Q R z).relIndex (Z R a) < 16 →
      ∃ g ∈ Ltilde R a,
        let d' := act R g⁻¹ d
        let t' := act R g⁻¹ t
        Adjacent R a t' ∧ Adjacent R d' t' ∧
        LocalPackage.J R d' t' ≠ LocalPackage.J R a t' ∧
        Ltilde R a ≤ LocalPackage.J R d' t' ⊔ Z R z ∧
        Z R d' ≤ Q R (path.walk.getVert (path.walk.length-2)) ∧
        ¬ Z R z ≤ normalizer ((Z R d' ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
  intro R geometry a z d t path hat hdt hne hs
  obtain ⟨ha4,hz4,hX⟩ := c.original_small_critical_data eK geometry path hs
  obtain ⟨g,hg,hgen⟩ := c.original_unequal_mover_generator eK geometry path hat hdt hne hz4 ha4
  have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  have hfix : act R g⁻¹ a = a := hgS
  have hat' : Adjacent R a (act R g⁻¹ t) := by
    simpa only [hfix] using (adjacent_act_iff R g⁻¹ _ _).mpr hat
  have hdt' := (adjacent_act_iff R g⁻¹ _ _).mpr hdt
  have hgen' : Ltilde R a ≤ LocalPackage.J R (act R g⁻¹ d) (act R g⁻¹ t) ⊔ Z R z := by
    rw [smallMoverJoin_act,inv_inv]
    exact hgen
  have hne' : LocalPackage.J R (act R g⁻¹ d) (act R g⁻¹ t) ≠
      LocalPackage.J R a (act R g⁻¹ t) := by
    intro he
    apply hne
    rw [←hfix,smallMoverJoin_act,smallMoverJoin_act] at he
    exact Subgroup.map_injective (MulAut.conj (g⁻¹)⁻¹).injective he
  refine ⟨g,hg,hat',hdt',hne',hgen',
    c.original_generated_neighbor_seed_le_penultimate_kernel eK geometry path hat' hdt' hgen',?_⟩
  intro hnorm
  have hJ : LocalPackage.J R (act R g⁻¹ d) (act R g⁻¹ t) ≤
      normalizer ((Z R (act R g⁻¹ d) ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) :=
    (LocalPackage.J_le_radical R _ _).trans
      (ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat' hdt')
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hcover : pResidual 2 c.M ⊔ R = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨k,hk,r,hr,rfl⟩ := c.component_product.2.2.2 x
    exact Subgroup.mul_mem _ (mem_sup_left hk) (mem_sup_right hr)
  have hSn : stabilizer R a ≤
      normalizer ((Z R (act R g⁻¹ d) ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
    rw [←ChapterC.RankTwo.Sp4Four.local_residual_edge_generation R hcover path.start_color hat']
    exact sup_le (hgen'.trans (sup_le hJ hnorm))
      (ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat' hdt')
  exact hne' (c.original_normal_neighbor_join_movers_eq eK geometry path.start_color hat' hdt' hX hSn).2


/-- The full neighboring seed has the exact critical-root commutator at b > 2. -/
theorem original_neighbor_abelian_kernel_commutator
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) →
      ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      ⁅Z R d,Z R z ⊓ Q R a⁆ = ⁅Z R a,Z R z⁆ ∧
        Nat.card (⁅Z R d,Z R z ⊓ Q R a⁆ : Subgroup (FreeAmalgam R)) = 4 := by
  intro R geometry hb a z d t path hat hdt hcontained hbad
  let Y := Z R d ⊔ Z R a
  let Y₀ := V R a ⊓ Q R (path.walk.getVert (path.walk.length-2))
  have hZa₀ : Z R a ≤ Y₀ := by
    apply le_inf (Z_le_VBall R a 2)
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a path.start_color)
    rw [geometry.distance_constant a path.start_color,path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hYV : Y ≤ V R a := ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt
  have hY₀ : Y ≤ Y₀ := le_inf hYV (sup_le hcontained (hZa₀.trans inf_le_right))
  have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hYZ := hY₀.trans (truncated_radius_le_endpoint_stabilizer path (by omega))
  have hn : ¬ ⁅Y₀,Z R z⁆ ≤ Z R a := by
    intro h
    apply hbad
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono hY₀ le_rfl).trans h).trans le_sup_right
  obtain h | ⟨ha4,hz4,_,_⟩ := c.original_radius_displacement_or_root eK geometry path
  · exact (hn h).elim
  obtain ⟨F,hF,f,hf,hr,π,hπ⟩ := c.original_truncated_radius_root_action eK geometry path ha4 hz4
  let fY := f.comp (inclusion hY₀)
  have hfY : fY.ker = (Q R z).subgroupOf Y := by
    ext y
    change f (inclusion hY₀ y) = 1 ↔ y.val ∈ Q R z
    change inclusion hY₀ y ∈ f.ker ↔ _
    rw [hf]
    rfl
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hCa : C R a = Q R a := C_eq_Q R hodd.isPGroup hodd.twoCore_le hfaith a path.start_color
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [path.start_color] at h
    cases he : color R t <;> simp_all
  have hAn : Z R z ⊓ Q R a ≤ normalizer (Y : Set (FreeAmalgam R)) :=
    (inf_le_right.trans (Q_le_adjacent_h R ht hat)).trans
      (ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat hdt)
  have hYt : Y ≤ V R t := by
    apply sup_le
    · exact le_iSup_of_le d (le_iSup_of_le
        (show (cosetGraph R).dist d t ≤ 2 from
          (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdt)).le.trans (by decide)) le_rfl)
    · exact le_iSup_of_le a (le_iSup_of_le
        (show (cosetGraph R).dist a t ≤ 2 from
          (SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)).le.trans (by decide)) le_rfl)
  have habel : IsMulCommutative Y := le_centralizer_iff_isMulCommutative.mp
    ((hYt.trans (le_centralizer_iff_isMulCommutative.mpr
      (NaturalStructure.Exclusion.edge_radius_commutative geometry hb a t path.start_color hat))).trans
      (centralizer_le hYt))
  have hh := critical_root_abelian_kernel_commutator path (by omega) hCa (c.original_Z_eq_U z path.end_color)
    Y hYQ le_sup_right hYZ habel fY hfY (fun y hy => hr (inclusion hY₀ y) hy)
    π (fun y u => hπ (inclusion hY₀ y) u) hAn hbad
  rw [F.card_eq,hF] at hh
  let A := Z R z ⊓ Q R a
  have hAnD : A ≤ normalizer (Z R d : Set (FreeAmalgam R)) :=
    ((inf_le_right.trans (Q_le_adjacent_h R ht hat)).trans
      (show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt))).trans
        (Z_normalized R d)
  have hcommV : ⁅Z R d,A⁆ ≤ Y :=
    (le_normalizer_iff_commutator_le_left.mp hAnD).trans le_sup_left
  have hnorm : Y ≤ normalizer ((⁅Z R d,A⁆ : Subgroup (FreeAmalgam R)) : Set _) :=
    ((le_centralizer_iff_isMulCommutative.mpr habel).trans
      (centralizer_le hcommV)).trans (Subgroup.centralizer_le_normalizer _)
  have hZaA : ⁅Z R a,A⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono le_rfl inf_le_right).trans (geometry.centralizes a path.start_color).le)
  have hjoin : ⁅Y,A⁆ = ⁅Z R d,A⁆ := le_antisymm
    (commutator_sup_le_of_relative_normal Y (Z R d) (Z R a) A ⁅Z R d,A⁆
      hnorm le_sup_left le_sup_right le_rfl (hZaA ▸ bot_le))
    (commutator_mono le_sup_left le_rfl)
  have hseed : ⁅Z R d,A⁆ = ⁅Z R a,Z R z⁆ := hjoin.symm.trans hh.1
  refine ⟨hseed,?_⟩
  rw [hseed]
  exact hh.2

/-- The full neighboring seed has critical-hyperplane centralizer index at most four. -/
theorem original_neighbor_abelian_kernel_centralizer_index
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) →
      ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      (centralizer ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _)).relIndex (Z R d) ≤ 4 := by
  intro R geometry hb a z d t path hat hdt hcontained hbad
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
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [path.start_color] at h
    cases he : color R t <;> simp_all
  have hd : color R d = false := by
    have h := adjacent_color_ne R hdt
    rw [ht] at h
    cases he : color R d <;> simp_all
  let A := Z R z ⊓ Q R a
  let := geometry.Z_elementary (by omega) z path.end_color
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le inf_le_left
  have hAD : A ≤ stabilizer R d :=
    (inf_le_right.trans (Q_le_adjacent_h R ht hat)).trans
      (fun _ hx => hx.2 d (adjacent_symm R hdt))
  have hfixed : U R d ⊓ centralizer (Ltilde R d : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hcore : x ∈ fixedCore R d := ⟨
      ((U_le_Z d).trans (geometry.omega_bound d hd
        (by
          rw [geometry.distance_constant d hd]
          change 0 < geometry.b R
          omega)) |>.trans (omegaCenter_le _)) hx.1,hx.2⟩
    rwa [c.original_fixedCore_eq_bot d hd] at hcore
  have hsmall : Nat.card (⁅A,U R d⁆ : Subgroup (FreeAmalgam R)) ≤ 4 := by
    rw [←c.original_Z_eq_U d hd,commutator_comm]
    exact (c.original_neighbor_abelian_kernel_commutator eK geometry hb path hat hdt hcontained hbad).2.le
  rw [c.original_Z_eq_U d hd]
  exact original_small_commutator_centralizer_index R hms hodd.isPGroup hne hodd.twoCore_le
    hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq hd hfixed A hAD hsmall

/-- The neighboring mover centralizes the actual critical root, including at b = 4. -/
theorem original_neighbor_abelian_movers_centralize_root
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) →
      ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      ⁅Z R a,Z R z⁆ ≤ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R)) := by
  intro R geometry hb a z d t path hat hdt hcontained hbad
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
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [path.start_color] at h
    cases he : color R t <;> simp_all
  have hd : color R d = false := by
    have h := adjacent_color_ne R hdt
    rw [ht] at h
    cases he : color R d <;> simp_all
  let A := Z R z ⊓ Q R a
  have hfixed : U R d ⊓ centralizer (Ltilde R d : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hcore : x ∈ fixedCore R d := ⟨
      ((U_le_Z d).trans (geometry.omega_bound d hd
        (by
          rw [geometry.distance_constant d hd]
          change 0 < geometry.b R
          omega)) |>.trans (omegaCenter_le _)) hx.1,hx.2⟩
    rwa [c.original_fixedCore_eq_bot d hd] at hcore
  have hsmall : (centralizer (A : Set (FreeAmalgam R))).relIndex (U R d) ≤ 4 := by
    rw [←c.original_Z_eq_U d hd]
    exact c.original_neighbor_abelian_kernel_centralizer_index eK geometry hb path hat hdt hcontained hbad
  have hQt : IsPGroup 2 (Q R t) := by
    obtain ⟨i,_,_,hiT,_,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le hd hdt
    rw [←hiT]
    exact hodd.isPGroup.map i
  have hindices := (c.original_small_mover_join_indices eK hd hdt).2
  have hJ := original_large_small_mover_centralizes_commutator R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq hd hfixed (Q R t) (LocalPackage.J R d t) A hQt
    (fun _ hx => hx.2 d (adjacent_symm R hdt)) (LocalPackage.J_le_radical R d t)
    (inf_le_right.trans (Q_le_adjacent_h R ht hat)) hindices.1 hindices.2.le (Or.inl hsmall)
  rw [←c.original_Z_eq_U d hd,commutator_comm] at hJ
  rw [(c.original_neighbor_abelian_kernel_commutator eK geometry hb path hat hdt hcontained hbad).1] at hJ
  exact hJ

/-- Every neighboring mover agrees with the starting mover when the original
critical image is small, including at distance four. -/
theorem original_small_critical_neighbor_movers_eq
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z d t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      (Q R z).relIndex (Z R a) < 16 →
      LocalPackage.J R d t = LocalPackage.J R a t := by
  intro R geometry a z d t path hat hdt hsmall
  by_contra hne
  obtain ⟨g,_hg,hat',hdt',_hne',hgen,hcontained,hbad⟩ :=
    c.original_small_unequal_four_selection eK geometry path hat hdt hne hsmall
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  let H := ⁅Z R a,Z R z⁆
  have hHJ : H ≤ centralizer (LocalPackage.J R (act R g⁻¹ d) (act R g⁻¹ t) : Set (FreeAmalgam R)) :=
    c.original_neighbor_abelian_movers_centralize_root eK geometry hb path hat' hdt' hcontained hbad
  have hHZ : H ≤ centralizer (Z R z : Set (FreeAmalgam R)) := by
    let := geometry.Z_elementary (by omega) z path.end_color
    exact (critical_commutator_le_endpoint ⟨a,z,path⟩).trans
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hHL : H ≤ centralizer (Ltilde R a : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (hgen.trans
      (sup_le (le_centralizer_iff.mp hHJ) (le_centralizer_iff.mp hHZ)))
  have hHQ : H ≤ Q R a :=
    (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path).trans
      ((Z_le_VBall R a 2).trans (geometry.V_le_Q hb a path.start_color))
  have hzero : H = ⊥ := by
    apply le_bot_iff.mp
    rw [←c.original_fixedCore_eq_bot a path.start_color]
    exact le_inf hHQ hHL
  exact (c.original_midpoint_radius_nonabelian eK geometry path).1 hzero

/-- The first kernel commutator centralizes every original radius, including
small critical images and outer ambient actions. -/
theorem original_radius_commutator_central
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (_geometry : Geometry R) (a : Vertex R), color R a = false →
      ⁅V R a,Q R a⁆ ≤ centralizer (V R a : Set (FreeAmalgam R)) := by
  intro R geometry a ha
  by_contra hn
  obtain ⟨u,z,hua,hza,htrip,path,hsmall,_⟩ :=
    c.original_noncentral_radius_root_pair eK geometry ha hn
  obtain ⟨t,hut,hat⟩ := exists_common_neighbor_of_dist_two R u a hua
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  have heq := c.original_small_critical_neighbor_movers_eq eK geometry path hut hat
    (by change (Q R z).relIndex (Z R u) < 16; rw [hsmall]; decide)
  have hcomm : ⁅Z R u,Q R a⁆ ≤ Z R a :=
    c.original_equal_mover_displacement_le_Z eK geometry hb ha hat hut heq.symm
  have hzQ : Z R z ≤ Q R a :=
    (show Z R z ≤ V R a from le_iSup_of_le z (le_iSup_of_le hza.le le_rfl)).trans
      (geometry.V_le_Q hb a ha)
  exact htrip (le_bot_iff.mp ((commutator_mono hcomm hzQ).trans
    (geometry.centralizes a ha).le))

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
