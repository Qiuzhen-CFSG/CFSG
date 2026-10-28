module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticPairedCriticalKernel
public import Theory.GroupTheory.DisjointCommutatorImages

/-!
# Independent images and full kernels of the original separated pair

For equal movers, the displacement of each selected seed by a subgroup of
Q_a lies in its mover's fixed part of X_a. In the root branch X_a=Z_a,
and the separated fixed spaces make those two displacements disjoint.
Consequently their conjugation images on every seed Z_w inside Q_a are
independent. When w is in critical range, C_w=Q_w identifies the exact
full-kernel splitting and the product of the two relative indices.

The field-four critical-image gap then shows that a joined image smaller
than sixteen has order four and exactly one backward critical seed; its
whole mate lies in Q_w. The final theorem applies this to the previously
selected original pair, preserving all three residual generators, the
actual conjugators, every path-overlap vertex and the kernel-normalization
alternative. No new local assumption is added to that selection.

This supplies the paired-image and full-kernel comparison needed in MS93
(5.11), printed p.923, specialized to Aschbacher--Smith 9.3.10, p.734.
The order-four paired-image exclusion, stronger radius bound, large-distance
and distance-four exclusions, and SymplecticPlaneRecognition remain open.
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

/-- The separated equal movers give disjoint displacement groups for every
subgroup of the full starting kernel. -/
theorem original_equal_mover_disjoint_displacements
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t → X R a = Z R a →
      ∀ x ∈ stabilizer R a,
      ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
        centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ →
      ∀ W ≤ Q R a, Disjoint ⁅Z R d,W⁆ ⁅Z R (act R x d),W⁆ := by
  intro R geometry hb a d t ha hat hdt heq hX x hx hsep W hW
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hfix : act R x a = a := hx
  have hat₂ : Adjacent R a (act R x t) := by
    rw [←hfix]
    exact (adjacent_act_iff R x _ _).mpr hat
  have hdt₂ := (adjacent_act_iff R x _ _).mpr hdt
  have heq₂ : LocalPackage.J R (act R x d) (act R x t) = LocalPackage.J R a (act R x t) := by
    rw [←hfix,smallMoverJoin_act,smallMoverJoin_act,heq]
  have hbounds {d' t' : Vertex R} (hat' : Adjacent R a t') (hdt' : Adjacent R d' t')
      (heq' : LocalPackage.J R d' t' = LocalPackage.J R a t') :
      ⁅Z R d',W⁆ ≤ Z R a ⊓ centralizer (LocalPackage.J R d' t' : Set (FreeAmalgam R)) := by
    have hd' : color R d' = false := by
      have h := adjacent_color_ne R hat'
      have h' := adjacent_color_ne R hdt'
      rw [ha] at h
      cases he : color R d' <;> cases ht : color R t' <;> simp_all
    have hWJ : W ≤ LocalPackage.J R d' t' := hW.trans
      (heq' ▸ LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le ha hat')
    refine le_inf ((commutator_mono le_rfl hW).trans
      ((c.original_equal_mover_displacement_le_X eK geometry
        (by change 2 < geometry.b R; omega) ha hat' hdt' heq').trans_eq hX)) ?_
    rw [commutator_comm]
    exact (commutator_mono hWJ le_rfl).trans (c.original_edge_mover_quadratic eK hd' hdt')
  have h₁ := hbounds hat hdt heq
  have h₂ := hbounds hat₂ hdt₂ heq₂
  apply disjoint_iff.mpr
  apply le_bot_iff.mp
  exact (le_inf (inf_le_left.trans h₁) (inf_le_right.trans (h₂.trans inf_le_right))).trans_eq hsep

/-- The full pair kernel is the join of the seed kernels, and its image
order is the product of the two seed-image orders. -/
theorem original_equal_mover_pair_kernel_image
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a d t w : Vertex R}, color R a = false → color R w = false →
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t → X R a = Z R a →
      (cosetGraph R).dist a w + 2 ≤ geometry.b R →
      ∀ x ∈ stabilizer R a,
      ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
        centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ →
      ((Z R d ⊔ Z R (act R x d)) ⊓ Q R w =
        (Z R d ⊓ Q R w) ⊔ (Z R (act R x d) ⊓ Q R w)) ∧
      (Q R w).relIndex (Z R d ⊔ Z R (act R x d)) =
        (Q R w).relIndex (Z R d) * (Q R w).relIndex (Z R (act R x d)) := by
  intro R geometry hb a d t w ha hw hat hdt heq hX hd x hx hsep
  have hpairV := ChapterC.Sp4Four.DistanceReduction.paired_seed_le_radius hat hdt x hx
  have hVS := radius_le_stabilizer_of_distance R geometry ha hd
  have hAS := (le_sup_left.trans hpairV).trans hVS
  have hBS := (le_sup_right.trans hpairV).trans hVS
  have hW : Z R w ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R w (geometry.exists_critical w hw)
    rw [geometry.distance_constant w hw,SimpleGraph.dist_comm]
    change (cosetGraph R).dist a w < geometry.b R
    omega
  have hdis := c.original_equal_mover_disjoint_displacements eK geometry hb ha hat hdt heq hX x hx hsep
    (Z R w) hW
  have hBA : Z R (act R x d) ≤ normalizer (Z R d : Set (FreeAmalgam R)) :=
    (((le_sup_right.trans hpairV).trans
      (le_centralizer_iff_isMulCommutative.mpr (V_abelian_of_four_lt R ha hb))).trans
      (centralizer_le (show Z R d ≤ V R a from le_sup_left.trans hpairV))).trans
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

/-- Every critical image in the original field-four geometry has order four
or at least sixteen. This uses the same whole seed at both endpoints. -/
theorem original_critical_image_gap
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (_path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) = 4 ∨ 16 ≤ (Q R z).relIndex (Z R a) := by
  intro R geometry a z path
  by_cases hsmall : (Q R z).relIndex (Z R a) < 16
  · apply Or.inl
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
    exact (original_small_critical_indices_eq_four R hms hodd.isPGroup hne
      hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
      hcard hBC hsq path (by omega) hsmall).1
  · exact Or.inr (Nat.le_of_not_gt hsmall)

/-- If a separated equal-mover pair has image smaller than sixteen, exactly
one of its seeds can be backward critical. Its image has order four and
the whole other seed lies in the original truncated kernel. -/
theorem original_equal_mover_small_pair_unique_backward
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t → X R a = Z R a →
      ∀ x ∈ stabilizer R a,
      ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
        centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ →
      let w := path.walk.getVert (path.walk.length-2)
      (¬ Z R d ≤ Q R w ∨ ¬ Z R (act R x d) ≤ Q R w) →
      (Q R w).relIndex (Z R d ⊔ Z R (act R x d)) < 16 →
      ((∃ back : CriticalPath R geometry d w,
          back.walk.getVert 1=t ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        (Q R w).relIndex (Z R d) = 4 ∧ Z R (act R x d) ≤ Q R w) ∨
      (Z R d ≤ Q R w ∧
        (∃ back : CriticalPath R geometry (act R x d) w,
          back.walk.getVert 1=act R x t ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        (Q R w).relIndex (Z R (act R x d)) = 4) := by
  intro R geometry hb a z d t path hat hdt heq hX x hx hsep w hcritical hsmall
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have he : Even path.walk.length := by
    rw [path.shortest,path.critical.1]
    exact geometry.even a path.start_color
  have hw : color R w = false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    rw [Nat.even_iff] at he ⊢
    omega
  have hdist : (cosetGraph R).dist a w+2 ≤ geometry.b R := by
    rw [path.dist_start (Nat.sub_le _ _),Nat.sub_add_cancel (by omega : 2 ≤ path.walk.length)]
    exact path.length_eq_b.le
  have hprod := (c.original_equal_mover_pair_kernel_image eK geometry hb path.start_color hw
    hat hdt heq hX hdist x hx hsep).2
  change (Q R w).relIndex (Z R d ⊔ Z R (act R x d)) =
    (Q R w).relIndex (Z R d) * (Q R w).relIndex (Z R (act R x d)) at hprod
  let := finite_stabilizer R a
  have hpairS := (ChapterC.Sp4Four.DistanceReduction.paired_seed_le_radius hat hdt x hx).trans
    ((geometry.V_le_Q (by omega) a path.start_color).trans (show Q R a ≤ stabilizer R a from fun _ h => h.1))
  let : Finite (Z R d ⊔ Z R (act R x d) : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hpairS) (inclusion_injective _)
  have hi₁ := (Q R w).relIndex_le_of_le_right
    (show Z R d ≤ Z R d ⊔ Z R (act R x d) from le_sup_left) index_ne_zero_of_finite
  have hi₂ := (Q R w).relIndex_le_of_le_right
    (show Z R (act R x d) ≤ Z R d ⊔ Z R (act R x d) from le_sup_right) index_ne_zero_of_finite
  have hfix : act R x a = a := hx
  have hat₂ : Adjacent R a (act R x t) := by
    rw [←hfix]
    exact (adjacent_act_iff R x _ _).mpr hat
  have hdt₂ := (adjacent_act_iff R x _ _).mpr hdt
  have hfirst (hn : ¬ Z R d ≤ Q R w) :
      (∃ back : CriticalPath R geometry d w,
        back.walk.getVert 1=t ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
      (Q R w).relIndex (Z R d)=4 := by
    obtain ⟨back,ht,ho⟩ := ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
      geometry (by omega) path hat hdt hn
    refine ⟨⟨back,ht,ho⟩,?_⟩
    rcases c.original_critical_image_gap eK geometry back with h | h
    · exact h
    · change 16 ≤ (Q R w).relIndex (Z R d) at h
      omega
  have hsecond (hn : ¬ Z R (act R x d) ≤ Q R w) :
      (∃ back : CriticalPath R geometry (act R x d) w,
        back.walk.getVert 1=act R x t ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
      (Q R w).relIndex (Z R (act R x d))=4 := by
    obtain ⟨back,ht,ho⟩ := ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
      geometry (by omega) path hat₂ hdt₂ hn
    refine ⟨⟨back,ht,ho⟩,?_⟩
    rcases c.original_critical_image_gap eK geometry back with h | h
    · exact h
    · change 16 ≤ (Q R w).relIndex (Z R (act R x d)) at h
      omega
  rcases hcritical with hn | hn
  · obtain ⟨hback,hi⟩ := hfirst hn
    refine Or.inl ⟨hback,hi,?_⟩
    by_contra hn₂
    obtain ⟨_,hi₂'⟩ := hsecond hn₂
    rw [hi,hi₂'] at hprod
    omega
  · obtain ⟨hback,hi⟩ := hsecond hn
    refine Or.inr ⟨?_,hback,hi⟩
    by_contra hn₁
    obtain ⟨_,hi₁'⟩ := hfirst hn₁
    rw [hi₁',hi] at hprod
    omega

/-- Apply the exact kernel splitting and image product to the original source choice.
Every small joined image singles out the actual backward path, with image
four and its entire mate in the kernel. All three residual generators and
the complete path overlap belong to this same pair. -/
theorem original_equal_mover_root_pair_image_configuration
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      ¬ ⁅V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)),Z R z⁆ ≤ Z R a →
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
        (Z R z ≤ normalizer ((K₁ ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) ∨
          Z R z ≤ normalizer ((K₂ ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)) ∧
        ((Z R d₁ ⊔ Z R d₂) ⊓ Q R w = K₁ ⊔ K₂) ∧
        (Q R w).relIndex (Z R d₁ ⊔ Z R d₂) =
          (Q R w).relIndex (Z R d₁) * (Q R w).relIndex (Z R d₂) ∧
        (16 ≤ (Q R w).relIndex (Z R d₁ ⊔ Z R d₂) ∨
          ((Q R w).relIndex (Z R d₁ ⊔ Z R d₂) = 4 ∧
            (((Q R w).relIndex (Z R d₁) = 4 ∧ Z R d₂ ≤ Q R w) ∨
              (Z R d₁ ≤ Q R w ∧ (Q R w).relIndex (Z R d₂) = 4)))) := by
  intro R geometry hb a z path heq hbad
  obtain h | ⟨_,_,hX,_⟩ := c.original_radius_displacement_or_root eK geometry path
  · exact (hbad h).elim
  obtain ⟨g,hg,x,hx,hat,hdt,heq₁,hgen,hsep,hmove,hback,hnorm,_⟩ :=
    c.original_equal_mover_root_kernel_configuration eK geometry hb path heq hbad
  have hxS : x ∈ stabilizer R a := Ltilde_le_stabilizer a hx
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have he : Even path.walk.length := by
    rw [path.shortest,path.critical.1]
    exact geometry.even a path.start_color
  have hw : color R (path.walk.getVert (path.walk.length-2)) = false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    rw [Nat.even_iff] at he ⊢
    omega
  have hdist : (cosetGraph R).dist a (path.walk.getVert (path.walk.length-2))+2 ≤ geometry.b R := by
    rw [path.dist_start (Nat.sub_le _ _),Nat.sub_add_cancel (by omega : 2 ≤ path.walk.length)]
    exact path.length_eq_b.le
  obtain ⟨hker,hprod⟩ := c.original_equal_mover_pair_kernel_image eK geometry hb path.start_color hw
    hat hdt heq₁ hX hdist x hxS hsep
  refine ⟨g,hg,x,hx,hat,hdt,heq₁,hgen,hsep,hmove,hback,hnorm,hker,hprod,?_⟩
  by_cases hlarge : 16 ≤ (Q R (path.walk.getVert (path.walk.length-2))).relIndex
      (Z R (act R g⁻¹ (path.walk.getVert 2)) ⊔ Z R (act R x (act R g⁻¹ (path.walk.getVert 2))))
  · exact Or.inl hlarge
  have hcritical : ¬ Z R (act R g⁻¹ (path.walk.getVert 2)) ≤ Q R (path.walk.getVert (path.walk.length-2)) ∨
      ¬ Z R (act R x (act R g⁻¹ (path.walk.getVert 2))) ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
    rcases hback with ⟨back,_,_⟩ | ⟨back,_,_⟩
    · exact Or.inl back.critical.2
    · exact Or.inr back.critical.2
  have hsmall := c.original_equal_mover_small_pair_unique_backward eK geometry hb path
    hat hdt heq₁ hX x hxS hsep hcritical (Nat.lt_of_not_ge hlarge)
  apply Or.inr
  rcases hsmall with ⟨_,hi,hk⟩ | ⟨hk,_,hi⟩
  · refine ⟨?_,Or.inl ⟨hi,hk⟩⟩
    rw [hprod,hi,relIndex_eq_one.mpr hk,mul_one]
  · refine ⟨?_,Or.inr ⟨hk,hi⟩⟩
    rw [hprod,hi,relIndex_eq_one.mpr hk,one_mul]

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
