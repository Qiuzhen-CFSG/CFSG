module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticCriticalKernel

/-!
# Endpoint action on the full original critical kernel

For the original overlapping paths (a,z) and (d,w), with w two steps before
z, retain the complete kernel K = Z_d intersect Q_w. The critical hyperplane
Z_z intersect Q_a normalizes K joined with Z_a. If Z_z fails to normalize
that join, the natural marking identifies [K, Z_z intersect Q_a] with the
original critical root [Z_a,Z_z], of order four, inside K. Thus a critical
image larger than four supplies endpoint normalization.

In the unequal-mover root branch, the selected backward path now retains
its full residual-generation equality as well as its conjugator, every
overlap vertex, and the mover inequality. Combining these actual generators
with canonical-mover normalization and residual nonnormality applies the
root obstruction to the same full backward kernel. The small-root exclusion,
stronger radius bound, both distance exclusions and final marked plane
recognition remain to be proved.

Source: MS93 (3.3)(ii), (5.5)--(5.7), (5.10), pp.867,915--919,922--923;
Aschbacher--Smith 9.3.10 and its final paragraph, pp.734--735.
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

/-- The source hyperplane calculation applies to the full truncated section,
not only to an entire neighboring seed. -/
theorem original_truncated_section_root_commutator
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z)
        (Y : Subgroup (FreeAmalgam R)),
      Z R a ≤ Y → Y ≤ V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)) →
      Z R z ⊓ Q R a ≤ normalizer (Y : Set _) →
      ¬ Z R z ≤ normalizer (Y : Set _) →
      (Q R z).relIndex (Z R a) = 4 ∧ (Q R a).relIndex (Z R z) = 4 ∧
        X R a = Z R a ∧ X R z = Z R z ∧
        ⁅Y,Z R z ⊓ Q R a⁆ = ⁅Z R a,Z R z⁆ ∧
        Nat.card (⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) = 4 := by
  intro R geometry hb a z path Y hZa hY hAn hbad
  let Y₀ := V R a ⊓ Q R (path.walk.getVert (path.walk.length-2))
  have hn : ¬ ⁅Y₀,Z R z⁆ ≤ Z R a := by
    intro h
    apply hbad
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono hY le_rfl).trans h).trans hZa
  obtain h | ⟨ha4,hz4,hXa,hXz⟩ := c.original_radius_displacement_or_root eK geometry path
  · exact (hn h).elim
  obtain ⟨F,hF,f,hf,hr,π,hπ⟩ := c.original_truncated_radius_root_action eK geometry path ha4 hz4
  let fY := f.comp (inclusion hY)
  have hfY : fY.ker = (Q R z).subgroupOf Y := by
    ext y
    change f (inclusion hY y) = 1 ↔ y.val ∈ Q R z
    change inclusion hY y ∈ f.ker ↔ _
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
  have hYV := hY.trans inf_le_left
  have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hYZ := hY.trans (truncated_radius_le_endpoint_stabilizer path (by omega))
  have hh := critical_root_kernel_commutator path hb hCa (c.original_Z_eq_U z path.end_color)
    Y hYQ hZa hYZ hYV fY hfY (fun y hy => hr (inclusion hY y) hy)
    π (fun y u => hπ (inclusion hY y) u) hAn hbad
  rw [F.card_eq,hF] at hh
  exact ⟨ha4,hz4,hXa,hXz,hh⟩

/-- On the original overlap, failure of endpoint normalization has one
specific nontrivial commutator, inside the entire backward critical kernel. -/
theorem original_critical_kernel_endpoint_alternative
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      let K := Z R d ⊓ Q R (path.walk.getVert (path.walk.length-2))
      Z R z ≤ normalizer ((K ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) ∨
        ((Q R z).relIndex (Z R a) = 4 ∧ (Q R a).relIndex (Z R z) = 4 ∧
          X R a = Z R a ∧ X R z = Z R z ∧
          ⁅K,Z R z ⊓ Q R a⁆ = ⁅Z R a,Z R z⁆ ∧
          Nat.card (⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) = 4 ∧
          ⁅Z R a,Z R z⁆ ≤ K) := by
  intro R geometry hb a z d t path hat hdt K
  classical
  by_cases hn : Z R z ≤ normalizer ((K ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)
  · exact Or.inl hn
  apply Or.inr
  let w := path.walk.getVert (path.walk.length-2)
  let A := Z R z ⊓ Q R a
  let H := K ⊔ Z R a
  have hZaQ : Z R a ≤ Q R w := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a path.start_color)
    rw [geometry.distance_constant a path.start_color,path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hzQ : Z R z ≤ Q R w := by
    apply Z_le_Q_of_dist_lt R z (geometry.exists_critical z path.end_color)
    rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,path.dist_end,path.length_eq_b]
    change geometry.b R-(geometry.b R-2) < geometry.b R
    omega
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [path.start_color] at h
    cases he : color R t <;> simp_all
  have hAD : A ≤ normalizer (Z R d : Set (FreeAmalgam R)) :=
    ((inf_le_right.trans (Q_le_adjacent_h R ht hat)).trans
      (show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt))).trans
        (Z_normalized R d)
  have hAQ : A ≤ normalizer (Q R w : Set (FreeAmalgam R)) :=
    (inf_le_left.trans hzQ).trans le_normalizer
  have hAK : A ≤ normalizer (K : Set (FreeAmalgam R)) :=
    (le_inf hAD hAQ).trans inf_normalizer_le_normalizer_inf
  have hAZ : A ≤ normalizer (Z R a : Set (FreeAmalgam R)) :=
    (inf_le_right.trans (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)).trans (Z_normalized R a)
  have hAH : A ≤ normalizer (H : Set (FreeAmalgam R)) :=
    (le_inf hAK hAZ).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hHV : H ≤ V R a := (sup_le_sup inf_le_left le_rfl).trans
    (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)
  have hHY : H ≤ V R a ⊓ Q R w := le_inf hHV (sup_le inf_le_right hZaQ)
  obtain ⟨ha4,hz4,hXa,hXz,hroot,hcard⟩ :=
    c.original_truncated_section_root_commutator eK geometry hb path H le_sup_right hHY hAH hn
  have hKA : ⁅K,A⁆ ≤ K := le_normalizer_iff_commutator_le_left.mp hAK
  have hcommV : ⁅K,A⁆ ≤ V R a := hKA.trans (le_sup_left.trans hHV)
  have hnorm : V R a ≤ normalizer ((⁅K,A⁆ : Subgroup (FreeAmalgam R)) : Set _) :=
    ((le_centralizer_iff_isMulCommutative.mpr (V_abelian_of_four_lt R path.start_color hb)).trans
      (centralizer_le hcommV)).trans (Subgroup.centralizer_le_normalizer _)
  have hZaA : ⁅Z R a,A⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono le_rfl inf_le_right).trans (geometry.centralizes a path.start_color).le)
  have hjoin : ⁅H,A⁆ = ⁅K,A⁆ := le_antisymm
    (commutator_sup_le_of_relative_normal (V R a) K (Z R a) A ⁅K,A⁆
      hnorm (le_sup_left.trans hHV) (Z_le_VBall R a 2) le_rfl (hZaA ▸ bot_le))
    (commutator_mono le_sup_left le_rfl)
  have heq : ⁅K,A⁆ = ⁅Z R a,Z R z⁆ := hjoin.symm.trans hroot
  exact ⟨ha4,hz4,hXa,hXz,heq,hcard,heq ▸ hKA⟩

/-- Unequal movers select a backward critical path with its actual full
residual generation, not just a conjugator and an overlapping walk. -/
theorem original_unequal_root_backward_generators
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) ≠
        LocalPackage.J R a (path.walk.getVert 1) →
      (Q R a).relIndex (Z R z) = 4 → (Q R z).relIndex (Z R a) = 4 →
      ∃ g ∈ stabilizer R a,
        ∃ back : CriticalPath R geometry (act R g (path.walk.getVert 2))
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = act R g (path.walk.getVert 1) ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        Ltilde R a ≤ LocalPackage.J R (act R g (path.walk.getVert 2))
          (back.walk.getVert 1) ⊔ Z R z ∧
        LocalPackage.J R (act R g (path.walk.getVert 2)) (back.walk.getVert 1) ≠
          LocalPackage.J R a (back.walk.getVert 1) := by
  intro R geometry hb a z path hne hza haz
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  obtain ⟨g,hg,hgen⟩ := c.original_unequal_mover_generator eK geometry path hat hdt hne hza haz
  have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  have hga : act R g⁻¹ a = a := hgS
  have hatg : Adjacent R a (act R g⁻¹ (path.walk.getVert 1)) := by
    simpa only [hga] using (adjacent_act_iff R g⁻¹ _ _).mpr hat
  have hdtg := (adjacent_act_iff R g⁻¹ _ _).mpr hdt
  have hgen' : Ltilde R a ≤ LocalPackage.J R (act R g⁻¹ (path.walk.getVert 2))
      (act R g⁻¹ (path.walk.getVert 1)) ⊔ Z R z := by
    rwa [smallMoverJoin_act,inv_inv]
  have hmove : 4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
      (geometry.Z_normal a)).relIndex (U R (act R g⁻¹ (path.walk.getVert 2))) := by
    rw [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega)
      path.start_color g⁻¹ hgS]
    exact c.original_critical_strict_movement eK geometry hb path
  have hbad : ¬ Z R z ≤ normalizer ((Z R (act R g⁻¹ (path.walk.getVert 2)) ⊔ Z R a :
      Subgroup (FreeAmalgam R)) : Set _) := by
    intro hn
    have hJ := (LocalPackage.J_le_radical R (act R g⁻¹ (path.walk.getVert 2))
      (act R g⁻¹ (path.walk.getVert 1))).trans
      (ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hatg hdtg)
    have hi := c.original_normal_neighbor_join_moving_index_eq_one eK geometry
      (by change 2 < geometry.b R; omega) path.start_color hatg hdtg
      (hgen'.trans (sup_le hJ hn))
    change (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
      (geometry.Z_normal a)).relIndex (U R (act R g⁻¹ (path.walk.getVert 2)))=1 at hi
    omega
  obtain ⟨⟨back,hbt,hover⟩,_⟩ := c.original_small_movers_backward_path eK geometry hb path
    hatg hdtg hbad hgen' hmove
  refine ⟨g⁻¹,hgS,back,hbt,hover,?_,?_⟩
  · rwa [hbt]
  · rw [hbt]
    intro heq
    have hJa := smallMoverJoin_act R g⁻¹ a (path.walk.getVert 1)
    rw [hga,inv_inv] at hJa
    rw [smallMoverJoin_act,inv_inv,hJa] at heq
    exact hne (Subgroup.map_injective (MulAut.conj g).injective heq)

/-- A small backward critical kernel with the actual two residual generators
forces the precise root obstruction of MS93 (5.10). -/
theorem original_generated_small_kernel_root
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z)
        (back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2))),
      Adjacent R a t → Adjacent R d t → back.walk.getVert 1 = t →
      Ltilde R a ≤ LocalPackage.J R d t ⊔ Z R z →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      (Q R (path.walk.getVert (path.walk.length-2))).relIndex (Z R d) ≤ 4 →
      let K := Z R d ⊓ Q R (path.walk.getVert (path.walk.length-2))
      (¬ Z R z ≤ normalizer ((K ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)) ∧
        (Q R z).relIndex (Z R a) = 4 ∧ (Q R a).relIndex (Z R z) = 4 ∧
        X R a = Z R a ∧ X R z = Z R z ∧
        ⁅K,Z R z ⊓ Q R a⁆ = ⁅Z R a,Z R z⁆ ∧
        Nat.card (⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) = 4 ∧
        ⁅Z R a,Z R z⁆ ≤ K := by
  intro R geometry hb a z d t path back hat hdt hbt hgen hmove hsmall K
  have hdist : (cosetGraph R).dist (path.walk.getVert (path.walk.length-2)) t < geometry.b R := by
    rw [←hbt,SimpleGraph.dist_comm,back.dist_end,back.length_eq_b]
    omega
  obtain ⟨hJ,_,hnot⟩ := c.original_critical_small_kernel_obstruction eK geometry hb back
    hdt hat hdist hsmall hmove
  have hn : ¬ Z R z ≤ normalizer ((K ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
    intro hZ
    exact hnot (hgen.trans (sup_le hJ hZ))
  refine ⟨hn,?_⟩
  rcases c.original_critical_kernel_endpoint_alternative eK geometry hb path hat hdt with h | h
  · exact (hn h).elim
  · exact h

/-- The unequal-mover source branch now retains the generated backward path
and its exact full-kernel obstruction on that very path. -/
theorem original_unequal_root_backward_kernel_configuration
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) ≠
        LocalPackage.J R a (path.walk.getVert 1) →
      (Q R a).relIndex (Z R z) = 4 → (Q R z).relIndex (Z R a) = 4 →
      ∃ g ∈ stabilizer R a,
        ∃ back : CriticalPath R geometry (act R g (path.walk.getVert 2))
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = act R g (path.walk.getVert 1) ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        Ltilde R a ≤ LocalPackage.J R (act R g (path.walk.getVert 2))
          (back.walk.getVert 1) ⊔ Z R z ∧
        LocalPackage.J R (act R g (path.walk.getVert 2)) (back.walk.getVert 1) ≠
          LocalPackage.J R a (back.walk.getVert 1) ∧
        ((Q R (path.walk.getVert (path.walk.length-2))).relIndex
          (Z R (act R g (path.walk.getVert 2))) ≤ 4 →
          let K := Z R (act R g (path.walk.getVert 2)) ⊓
            Q R (path.walk.getVert (path.walk.length-2))
          ⁅K,Z R z ⊓ Q R a⁆ = ⁅Z R a,Z R z⁆ ∧
            Nat.card (⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) = 4 ∧
            ⁅Z R a,Z R z⁆ ≤ K) := by
  intro R geometry hb a z path hne hza haz
  obtain ⟨g,hg,back,hbt,hover,hgen,hne'⟩ :=
    c.original_unequal_root_backward_generators eK geometry hb path hne hza haz
  refine ⟨g,hg,back,hbt,hover,hgen,hne',?_⟩
  intro hsmall
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hga : act R g a = a := hg
  have hatg : Adjacent R a (back.walk.getVert 1) := by
    rw [hbt]
    simpa only [hga] using (adjacent_act_iff R g _ _).mpr hat
  have hdtg : Adjacent R (act R g (path.walk.getVert 2)) (back.walk.getVert 1) := by
    rw [hbt]
    exact (adjacent_act_iff R g _ _).mpr hdt
  have hmove : 4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
      (geometry.Z_normal a)).relIndex (U R (act R g (path.walk.getVert 2))) := by
    rw [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega) path.start_color g hg]
    exact c.original_critical_strict_movement eK geometry hb path
  exact (c.original_generated_small_kernel_root eK geometry hb path back hatg hdtg rfl
    hgen hmove hsmall).2.2.2.2.2

/-- The endpoint normalizes the complete backward critical-kernel join
outside the order-four critical-image branch. -/
theorem original_critical_kernel_endpoint_normalized_of_large
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t → 4 < (Q R z).relIndex (Z R a) →
      Z R z ≤ normalizer (((Z R d ⊓ Q R (path.walk.getVert (path.walk.length-2))) ⊔
        Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
  intro R geometry hb a z d t path hat hdt hlarge
  rcases c.original_critical_kernel_endpoint_alternative eK geometry hb path hat hdt with h | h
  · exact h
  · change 4 < (Q R z).relIndex (Z R a) at hlarge
    rw [h.1] at hlarge
    omega

/-- For actual two-generator overlaps, a larger starting critical image
forces a larger backward critical image as well. -/
theorem original_generated_backward_critical_index_gt_four
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z)
        (back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2))),
      Adjacent R a t → Adjacent R d t → back.walk.getVert 1 = t →
      Ltilde R a ≤ LocalPackage.J R d t ⊔ Z R z →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      4 < (Q R z).relIndex (Z R a) →
      4 < (Q R (path.walk.getVert (path.walk.length-2))).relIndex (Z R d) := by
  intro R geometry hb a z d t path back hat hdt hbt hgen hmove hlarge
  by_contra! hsmall
  have hroot := c.original_generated_small_kernel_root eK geometry hb path back hat hdt hbt hgen hmove hsmall
  exact hroot.1 (c.original_critical_kernel_endpoint_normalized_of_large eK geometry hb path hat hdt hlarge)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
