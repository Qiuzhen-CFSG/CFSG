module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticPairedImageExclusion
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticGeneratedRootExclusion

/-!
# Radius growth and the original large-distance numerical split

For a critical image below sixteen, the reciprocal indices are four and
X_a is the original seed. The selected equal-mover pair has image at least
sixteen at the vertex two steps before the endpoint, even when the radius
already has the desired displacement. Unequal movers supply the same lower
bound through their generated backward critical path.

In the other branch a backward critical seed contributes at least four
images, while the starting seed contributes at least sixteen inside that
kernel. Exact relative-index multiplication therefore gives at least
sixty-four images of the full radius modulo the intersection of the two
original neighborhood kernels, in every branch.

Reverse the same critical path and use its literal second vertex. This
bound gives the two strict index alternatives in the final paragraph of
MS93 (5.11), without an additional single-kernel radius bound. The original
overlapping-sequence application retains its conjugators, paired commutator
centrality and both noncentrality conclusions. The fixed-space implications
that turn either index alternative into a contradiction, distance four,
and SymplecticPlaneRecognition remain to be proved.

Source: MS93 (5.6)--(5.11), pp.917--924; Aschbacher--Smith 9.3.10,
printed pp.734--735. Every kernel here belongs to the original tensor
geometry; no characteristic replacement or central quotient is substituted.
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

/-- Every small critical image retains both exact field-four indices and
identifies the full starting X-layer with its original seed. -/
theorem original_small_critical_data
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (_path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) < 16 →
      (Q R z).relIndex (Z R a) = 4 ∧ (Q R a).relIndex (Z R z) = 4 ∧ X R a = Z R a := by
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
  have hfour : 4 ≤ geometry.b R := c.original_geometry_four_le eK geometry
  have hi := original_small_critical_indices_eq_four R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path (by omega) hsmall
  have hX := original_small_critical_X_decomposition R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path (by omega) hsmall
  rw [c.graph_X_fixed_eq_bot a path.start_color,sup_bot_eq,
    ←c.original_Z_eq_U a path.start_color] at hX
  exact ⟨hi.1,hi.2,hX⟩

/-- The original paired choice has image at least sixteen whenever the
starting critical image is small. No failure of radius displacement is
assumed; every full kernel and every overlap vertex is retained. -/
theorem original_small_critical_paired_selection
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
        let K₁ := Z R d₁ ⊓ Q R w
        let K₂ := Z R d₂ ⊓ Q R w
        Adjacent R a t₁ ∧ Adjacent R d₁ t₁ ∧
        LocalPackage.J R d₁ t₁ = LocalPackage.J R a t₁ ∧
        Ltilde R a ≤ (LocalPackage.J R d₁ t₁ ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) ∧
        ((Z R a ⊓ centralizer (LocalPackage.J R d₁ t₁ : Set (FreeAmalgam R))) ⊓
          centralizer (LocalPackage.J R d₂ t₂ : Set (FreeAmalgam R))) = ⊥ ∧
        4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d₁) ∧
        ((∃ back : CriticalPath R geometry d₁ w,
          back.walk.getVert 1=t₁ ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∨
        (∃ back : CriticalPath R geometry d₂ w,
          back.walk.getVert 1=t₂ ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i)) ∧
        ((Z R d₁ ⊔ Z R d₂) ⊓ Q R w = K₁ ⊔ K₂) ∧
        (Q R w).relIndex (Z R d₁ ⊔ Z R d₂) =
          (Q R w).relIndex (Z R d₁) * (Q R w).relIndex (Z R d₂) ∧
        16 ≤ (Q R w).relIndex (Z R d₁ ⊔ Z R d₂) ∧
        ⁅K₁ ⊔ Z R a,Z R z⁆ ≤ Z R a ∧ ⁅K₂ ⊔ Z R a,Z R z⁆ ≤ Z R a := by
  intro R geometry hb a z path hsmall heq
  obtain ⟨ha4,hz4,hX⟩ := c.original_small_critical_data eK geometry path hsmall
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  obtain ⟨g,hg,x,hx,hat₁,hdt₁,hgen,hindex,hsep⟩ :=
    c.original_equal_mover_root_separated_selection eK geometry hb path hat hdt heq hz4 ha4
  have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  have hfix : act R g⁻¹ a = a := hgS
  have heq₁ : LocalPackage.J R (act R g⁻¹ (path.walk.getVert 2))
      (act R g⁻¹ (path.walk.getVert 1)) = LocalPackage.J R a (act R g⁻¹ (path.walk.getVert 1)) := by
    rw [smallMoverJoin_act,heq,←smallMoverJoin_act,hfix]
  have hmove : 4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex
      (U R (act R g⁻¹ (path.walk.getVert 2))) := by
    rw [hindex]
    exact c.original_critical_strict_movement eK geometry hb path
  have hxS : x ∈ stabilizer R a := Ltilde_le_stabilizer a hx
  have hback := c.original_equal_mover_pair_backward_path eK geometry hb path
    hat₁ hdt₁ heq₁ hX ha4 hz4 x hx hgen hsep hmove
  have hcritical : ¬ Z R (act R g⁻¹ (path.walk.getVert 2)) ≤ Q R (path.walk.getVert (path.walk.length-2)) ∨
      ¬ Z R (act R x (act R g⁻¹ (path.walk.getVert 2))) ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
    rcases hback with ⟨back,_,_⟩ | ⟨back,_,_⟩
    · exact Or.inl back.critical.2
    · exact Or.inr back.critical.2
  have he : Even path.walk.length := by
    rw [path.shortest,path.critical.1]
    exact geometry.even a path.start_color
  have hw : color R (path.walk.getVert (path.walk.length-2)) = false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    rw [Nat.even_iff] at he ⊢
    omega
  have hdist : (cosetGraph R).dist a (path.walk.getVert (path.walk.length-2))+2 ≤ geometry.b R := by
    rw [path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    omega
  obtain ⟨hker,hprod⟩ := c.original_equal_mover_pair_kernel_image eK geometry hb path.start_color hw
    hat₁ hdt₁ heq₁ hX hdist x hxS hsep
  exact ⟨g,hg,x,hx,hat₁,hdt₁,heq₁,hgen,hsep,hmove,hback,hker,hprod,
    c.original_equal_mover_generated_pair_index_ge_sixteen eK geometry hb path
      hat₁ hdt₁ heq₁ hX x hx hgen hsep hmove hcritical,
    c.original_equal_mover_generated_pair_displacement eK geometry hb path hat₁ hdt₁ heq₁ x hx hgen⟩

/-- Both source choices force at least sixteen images of the full original
radius at the literal vertex two steps before the endpoint. -/
theorem original_small_critical_radius_image_ge_sixteen
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) < 16 →
      16 ≤ (Q R (path.walk.getVert (path.walk.length-2))).relIndex (V R a) := by
  intro R geometry hb a z path hsmall
  let w := path.walk.getVert (path.walk.length-2)
  let := finite_stabilizer R a
  let : Finite (V R a) := Finite.of_injective
    (inclusion ((geometry.V_le_Q (by omega) a path.start_color).trans (fun _ hx => hx.1)))
    (inclusion_injective _)
  by_cases heq : LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
      LocalPackage.J R a (path.walk.getVert 1)
  · obtain ⟨g,hg,x,hx,hat,hdt,_,_,_,_,_,_,_,hi,_,_⟩ :=
      c.original_small_critical_paired_selection eK geometry hb path hsmall heq
    exact hi.trans ((Q R w).relIndex_le_of_le_right
      (ChapterC.Sp4Four.DistanceReduction.paired_seed_le_radius hat hdt x (Ltilde_le_stabilizer a hx))
      index_ne_zero_of_finite)
  · obtain ⟨ha4,hz4,_⟩ := c.original_small_critical_data eK geometry path hsmall
    obtain ⟨g,hg,back,hbt,hover,_,_,hlarge,_⟩ :=
      c.original_unequal_root_backward_large_image eK geometry hb path heq hz4 ha4
    have hi : 16 ≤ (Q R w).relIndex (Z R (act R g (path.walk.getVert 2))) := by
      rcases c.original_critical_image_gap eK geometry back with h | h
      · omega
      · exact h
    have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
    have hdist : (cosetGraph R).dist a (path.walk.getVert 2) ≤ 2 := by
      rw [path.dist_start (by omega)]
    have hZV : Z R (act R g (path.walk.getVert 2)) ≤ V R a := by
      have hfix : act R g a = a := hg
      have hdist' : (cosetGraph R).dist (act R g (path.walk.getVert 2)) a ≤ 2 := by
        have hh := dist_act R g (path.walk.getVert 2) a
        rw [hfix] at hh
        exact hh.trans_le (by rwa [SimpleGraph.dist_comm])
      exact le_iSup_of_le _ (le_iSup_of_le hdist' le_rfl)
    exact hi.trans ((Q R w).relIndex_le_of_le_right hZV index_ne_zero_of_finite)

/-- In the small critical branch, intersecting the two literal endpoint
kernels leaves at least sixty-four images of the original radius. -/
private theorem original_small_critical_two_kernel_index_ge_64
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) < 16 →
      64 ≤ (Q R z ⊓ Q R (path.walk.getVert (path.walk.length-2))).relIndex (V R a) := by
  intro R geometry hb a z path hsmall
  let w := path.walk.getVert (path.walk.length-2)
  let := finite_stabilizer R a
  let : Finite (V R a) := Finite.of_injective
    (inclusion ((geometry.V_le_Q (by omega) a path.start_color).trans (fun _ hx => hx.1)))
    (inclusion_injective _)
  let : Finite (V R a ⊓ Q R w : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  obtain ⟨ha4,_,_⟩ := c.original_small_critical_data eK geometry path hsmall
  have hZaQ : Z R a ≤ Q R w := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a path.start_color)
    rw [geometry.distance_constant a path.start_color,path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hZaK : Z R a ≤ V R a ⊓ Q R w := le_inf (Z_le_VBall R a 2) hZaQ
  have hfour : 4 ≤ (Q R z).relIndex (V R a ⊓ Q R w) := by
    rw [←ha4]
    exact relIndex_le_of_le_right hZaK index_ne_zero_of_finite
  have hsixteen := c.original_small_critical_radius_image_ge_sixteen eK geometry hb path hsmall
  have hm := relIndex_inf_mul_relIndex (Q R z) (Q R w) (V R a)
  rw [inf_comm (Q R w) (V R a)] at hm
  change 16 ≤ (Q R w).relIndex (V R a) at hsixteen
  change 64 ≤ (Q R z ⊓ Q R w).relIndex (V R a)
  rw [←hm]
  exact Nat.mul_le_mul hfour hsixteen


/-- An actual backward critical path forces at least four images at the
truncated endpoint, with no restriction on the original critical image. -/
theorem original_truncated_radius_image_ge_four
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      4 ≤ (Q R (path.walk.getVert (path.walk.length-2))).relIndex (V R a) := by
  intro R geometry hb a z path
  obtain ⟨d,t,hat,hdt,⟨back,_,_⟩,_⟩ := c.original_backward_path eK geometry hb path
  have hi : 4 ≤ (Q R (path.walk.getVert (path.walk.length-2))).relIndex (Z R d) := by
    rcases c.original_critical_image_gap eK geometry back with h | h
    · exact h.ge
    · exact (by decide : 4 ≤ 16).trans h
  let := finite_stabilizer R a
  let : Finite (V R a) := Finite.of_injective
    (inclusion ((geometry.V_le_Q (by omega) a path.start_color).trans (fun _ hx => hx.1)))
    (inclusion_injective _)
  exact hi.trans (relIndex_le_of_le_right
    (le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt))
    index_ne_zero_of_finite)

/-- The original radius has at least sixty-four images modulo the complete
intersection of the critical and truncated endpoint kernels, in both
critical-image branches. -/
theorem original_two_kernel_radius_index_ge_64
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      64 ≤ (Q R z ⊓ Q R (path.walk.getVert (path.walk.length-2))).relIndex (V R a) := by
  intro R geometry hb a z path
  rcases c.original_critical_image_gap eK geometry path with hsmall | hlarge
  · apply c.original_small_critical_two_kernel_index_ge_64 eK geometry hb path
    rw [hsmall]
    decide
  let w := path.walk.getVert (path.walk.length-2)
  let := finite_stabilizer R a
  let : Finite (V R a) := Finite.of_injective
    (inclusion ((geometry.V_le_Q (by omega) a path.start_color).trans (fun _ hx => hx.1)))
    (inclusion_injective _)
  let : Finite (V R a ⊓ Q R w : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hZaQ : Z R a ≤ Q R w := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a path.start_color)
    rw [geometry.distance_constant a path.start_color,path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hsixteen : 16 ≤ (Q R z).relIndex (V R a ⊓ Q R w) :=
    hlarge.trans (relIndex_le_of_le_right (le_inf (Z_le_VBall R a 2) hZaQ)
      index_ne_zero_of_finite)
  have hfour := c.original_truncated_radius_image_ge_four eK geometry hb path
  have hm := relIndex_inf_mul_relIndex (Q R z) (Q R w) (V R a)
  rw [inf_comm (Q R w) (V R a)] at hm
  change 4 ≤ (Q R w).relIndex (V R a) at hfour
  change 64 ≤ (Q R z ⊓ Q R w).relIndex (V R a)
  rw [←hm]
  exact Nat.mul_le_mul hsixteen hfour

/-- If the original endpoint radius image is at most sixteen, its whole
kernel has at least four images at the earlier vertex. All source-image
alternatives have been discharged on this same path. -/
theorem original_small_radius_endpoint_kernel_moves
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      (Q R z).relIndex (V R a) ≤ 16 →
      let w := path.walk.getVert (path.walk.length-2)
      4 ≤ (Q R w).relIndex (V R a ⊓ Q R z) ∧ ¬ V R a ⊓ Q R z ≤ Q R w := by
  intro R geometry hb a z path hradius w
  have hlo := c.original_two_kernel_radius_index_ge_64 eK geometry hb path
  have hm := relIndex_inf_mul_relIndex (Q R w) (Q R z) (V R a)
  rw [inf_comm (Q R z) (V R a),inf_comm (Q R w) (Q R z)] at hm
  change 64 ≤ (Q R z ⊓ Q R w).relIndex (V R a) at hlo
  change (Q R z).relIndex (V R a) ≤ 16 at hradius
  have hfour : 4 ≤ (Q R w).relIndex (V R a ⊓ Q R z) := by
    have hu := Nat.mul_le_mul_left ((Q R w).relIndex (V R a ⊓ Q R z)) hradius
    rw [hm] at hu
    omega
  refine ⟨hfour,?_⟩
  intro h
  rw [relIndex_eq_one.mpr h] at hfour
  omega

/-- Apply the full two-kernel bound to the reversed original path. This
discharges the numerical split used in the final paragraph of source 5.11
without replacing either of its kernels. -/
theorem original_critical_radius_index_split
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      4 < (Q R (path.walk.getVert 2)).relIndex (V R z) ∨
        4 < (Q R a).relIndex (V R z ⊓ Q R (path.walk.getVert 2)) := by
  intro R geometry hb a z path
  let rev : CriticalPath R geometry z a := {
    start_color := path.end_color
    walk := path.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
    critical := (c.original_critical_reverse eK geometry (by change 0 < geometry.b R; omega) path).critical }
  have hlarge := c.original_two_kernel_radius_index_ge_64 eK geometry hb rev
  change 64 ≤ (Q R a ⊓ Q R (path.walk.reverse.getVert (path.walk.reverse.length-2))).relIndex (V R z) at hlarge
  rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse] at hlarge
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  rw [show path.walk.length-(path.walk.length-2)=2 by omega] at hlarge
  have hm := relIndex_inf_mul_relIndex (Q R a) (Q R (path.walk.getVert 2)) (V R z)
  rw [inf_comm (Q R (path.walk.getVert 2)) (V R z)] at hm
  by_contra! h
  have hu := Nat.mul_le_mul h.2 h.1
  rw [hm] at hu
  omega

/-- The original sequence now supplies both the numerical alternative and
the paired commutator centrality in the final source calculation. Its
stabilizer conjugators and every overlapping path vertex are retained. -/
theorem original_large_distance_radius_split
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
        (4 < (Q R (s 1).first).relIndex (V R (s 2).last) ∨
          4 < (Q R (s 2).first).relIndex (V R (s 2).last ⊓ Q R (s 1).first)) ∧
        ⁅⁅Z R (s 2).first,Z R (s 2).last⁆ ⊔
          ⁅Z R (s 3).first,Z R (s 3).last⁆,V R (s 2).last⁆ = ⊥ ∧
        (¬ ⁅Z R (s 2).first,Z R (s 2).last⁆ ≤
          stabilizer R (s 1).first ⊓ centralizer (stabilizer R (s 1).first : Set (FreeAmalgam R))) ∧
        (¬ ⁅Z R (s 3).first,Z R (s 3).last⁆ ≤
          stabilizer R (s 2).first ⊓ centralizer (stabilizer R (s 2).first : Set (FreeAmalgam R))) := by
  intro R geometry hb p
  obtain ⟨s,hs0,hs,hover,horbit,hcent⟩ :=
    c.original_overlapping_sequence_with_conjugators eK geometry hb p
  refine ⟨s,hs0,hs,hover,horbit,?_,hcent,
    c.original_critical_commutator_not_le_vertex_center eK geometry (s 2).path (s 1).path.start_color,
    c.original_critical_commutator_not_le_vertex_center eK geometry (s 3).path (s 2).path.start_color⟩
  have h := c.original_critical_radius_index_split eK geometry hb (s 2).path
  have hv := (hs 1).overlap 0 (by change 0+2 ≤ geometry.b R; omega)
  simp only [zero_add,SimpleGraph.Walk.getVert_zero] at hv
  rwa [hv] at h

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
