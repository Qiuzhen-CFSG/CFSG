module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticGeneratedRootExclusion

/-!
# Equal-mover control of the full original critical kernels

For the selected pair of neighboring seeds, intersect each complete seed
with the same original kernel two steps before the critical endpoint. If
the endpoint fails to normalize one kernel joined with the starting seed,
the exact root comparison and quadratic mover action make that root fixed
by its mover. The selected movers have zero common fixed space, so failure
cannot occur on both sides.

The common-root calculation gives more: the mate fixes the full critical
hyperplane. Its endpoint displacement is in the starting seed, and its
join with that seed has endpoint image of order exactly four. The proof
uses the literal natural marking and the full quotient kernel. Neither
neighboring seed is assumed contained in the truncated kernel.

The final application retains the original equal-mover selection, all three
residual generators, strict movement, and the overlapping backward paths.
The stronger radius bound, complete root exclusion, both original distance
exclusions and SymplecticPlaneRecognition still require their source proofs.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii), (5.6)--(5.7),
(5.10)--(5.11), printed pp.867,917--919,922--924; Aschbacher--Smith
9.3.10 and the terminal paragraph of9.3, printed p.734.
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

/-- In the equal-mover branch, failure of endpoint normalization on the
full critical-kernel join forces its root to be fixed by the common mover. -/
theorem original_equal_mover_kernel_failure_fixes_root
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      ¬ Z R z ≤ normalizer (((Z R d ⊓ Q R (path.walk.getVert (path.walk.length-2))) ⊔
        Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      ⁅Z R a,Z R z⁆ ≤ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R)) := by
  intro R geometry hb a z d t path hat hdt heq hbad
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [path.start_color] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  have hAJ : Z R z ⊓ Q R a ≤ LocalPackage.J R d t := inf_le_right.trans
    (heq ▸ LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le path.start_color hat)
  rcases c.original_critical_kernel_endpoint_alternative eK geometry hb path hat hdt with hn | hroot
  · exact (hbad hn).elim
  rw [←hroot.2.2.2.2.1,commutator_comm]
  exact (commutator_mono hAJ inf_le_left).trans (c.original_edge_mover_quadratic eK hd hdt)

/-- Endpoint normalization cannot fail on both full kernels of a separated
equal-mover pair. The common root is nontrivial on the original path. -/
theorem original_equal_mover_paired_critical_kernel_normalized
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      ∀ x ∈ stabilizer R a,
      ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
        centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ →
      Z R z ≤ normalizer (((Z R d ⊓ Q R (path.walk.getVert (path.walk.length-2))) ⊔
        Z R a : Subgroup (FreeAmalgam R)) : Set _) ∨
      Z R z ≤ normalizer (((Z R (act R x d) ⊓ Q R (path.walk.getVert (path.walk.length-2))) ⊔
        Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
  intro R geometry hb a z d t path hat hdt heq x hx hsep
  by_contra! hn
  have hfix : act R x a = a := hx
  have hat₂ : Adjacent R a (act R x t) := by
    rw [←hfix]
    exact (adjacent_act_iff R x _ _).mpr hat
  have hdt₂ := (adjacent_act_iff R x _ _).mpr hdt
  have heq₂ : LocalPackage.J R (act R x d) (act R x t) = LocalPackage.J R a (act R x t) := by
    rw [←hfix,smallMoverJoin_act,smallMoverJoin_act,heq]
  have h₁ := c.original_equal_mover_kernel_failure_fixes_root eK geometry hb path hat hdt heq hn.1
  have h₂ := c.original_equal_mover_kernel_failure_fixes_root eK geometry hb path hat₂ hdt₂ heq₂ hn.2
  have hzero : ⁅Z R a,Z R z⁆ ≤ (⊥ : Subgroup (FreeAmalgam R)) := hsep ▸
    le_inf (le_inf (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path) h₁) h₂
  exact c.original_critical_commutator_not_le_vertex_center eK geometry path path.start_color
    (hzero.trans bot_le)

private theorem original_truncated_section_common_root
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z)
        (Y : Subgroup (FreeAmalgam R)),
      Z R a ≤ Y → Y ≤ V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)) →
      ⁅Y,Z R z ⊓ Q R a⁆ ≤ Z R a → ¬ ⁅Y,Z R z⁆ ≤ Z R a →
      ∀ W ≤ Y, ⁅W,Z R z ⊓ Q R a⁆ = ⊥ ∨ ⁅W,Z R z ⊓ Q R a⁆ = ⁅Z R a,Z R z⁆ := by
  intro R geometry hb a z path Y hZa hY hbound hbad
  have hn : ¬ ⁅V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)),Z R z⁆ ≤ Z R a :=
    fun h => hbad ((commutator_mono hY le_rfl).trans h)
  obtain h | ⟨ha4,hz4,_,_⟩ := c.original_radius_displacement_or_root eK geometry path
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
  exact (critical_root_kernel_commutator_of_displacement path hb hCa
    (c.original_Z_eq_U z path.end_color) Y
    (hY.trans (inf_le_left.trans (geometry.V_le_Q (by omega) a path.start_color))) hZa
    (hY.trans (truncated_radius_le_endpoint_stabilizer path (by omega)))
    (hY.trans inf_le_left) fY hfY (fun y hy => hr (inclusion hY y) hy)
    π (fun y u => hπ (inclusion hY y) u) hbound hbad).2.2

private theorem original_truncated_section_control_of_central_hyperplane
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z)
        (Y : Subgroup (FreeAmalgam R)),
      Z R a ≤ Y → Y ≤ V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)) →
      (Q R z).relIndex (Z R a) = 4 → (Q R a).relIndex (Z R z) = 4 →
      ⁅Y,Z R z ⊓ Q R a⁆ = ⊥ →
      ⁅Y,Z R z⁆ ≤ Z R a ∧ (Q R z).relIndex Y = 4 := by
  intro R geometry hb a z path Y hZa hY ha4 hz4 hzero
  have hYZ := hY.trans (truncated_radius_le_endpoint_stabilizer path (by omega))
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
  have hcent := critical_root_hyperplane_centralizer path (by omega) hCa
    (c.original_Z_eq_U z path.end_color) Y hZa hYZ fY hfY
    (fun y hy => hr (inclusion hY y) hy) π (fun y u => hπ (inclusion hY y) u)
    (by rw [F.card_eq,hF]; exact ha4)
  have hY' : Y ≤ Z R a ⊔ (Y ⊓ Q R z) :=
    (le_inf le_rfl (commutator_eq_bot_iff_le_centralizer.mp hzero)).trans_eq hcent
  have hQ : Y ≤ Q R a := hY.trans (inf_le_left.trans (geometry.V_le_Q (by omega) a path.start_color))
  have hcomm : ⁅Y ⊓ Q R z,Z R z⁆ = ⊥ := by
    rw [commutator_comm]
    exact le_bot_iff.mp ((commutator_mono le_rfl inf_le_right).trans (geometry.centralizes z path.end_color).le)
  have hdisp : ⁅Y,Z R z⁆ ≤ Z R a := (commutator_mono hY' le_rfl).trans
    (commutator_sup_le_of_relative_normal (Q R a) (Z R a) (Y ⊓ Q R z) (Z R z) (Z R a)
      ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Z_normalized R a))
      (hZa.trans hQ) (inf_le_left.trans hQ)
      (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path) (hcomm ▸ bot_le))
  have hYY : Z R a ⊔ (Y ⊓ Q R z) = Y := le_antisymm (sup_le hZa inf_le_left) hY'
  have hN : (Y ⊓ Q R z).subgroupOf Y = (Q R z).subgroupOf Y := by
    ext y
    change (y.val ∈ Y ∧ y.val ∈ Q R z) ↔ y.val ∈ Q R z
    exact and_iff_right y.property
  have hjoin := congrArg (fun H : Subgroup (FreeAmalgam R) => H.subgroupOf Y) hYY
  rw [subgroupOf_sup hZa inf_le_left,hN,subgroupOf_self] at hjoin
  let : ((Q R z).subgroupOf Y).Normal :=
    normal_subgroupOf_of_le_normalizer (hYZ.trans (Q_normalized R z))
  have hi := relIndex_sup_right ((Z R a).subgroupOf Y) ((Q R z).subgroupOf Y)
  rw [hjoin,relIndex_top_right,relIndex_subgroupOf hZa] at hi
  exact ⟨hdisp,hi.trans ha4⟩

/-- If one full selected kernel fails endpoint normalization, its mate
centralizes the entire critical hyperplane and has endpoint displacement
inside the original starting seed. Its image joined with that seed has
order exactly four at the endpoint. Neither neighboring seed is assumed to
lie in the truncated kernel. -/
theorem original_equal_mover_critical_kernel_mate_displacement
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      ∀ x ∈ stabilizer R a,
      ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
        centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ →
      let K₁ := Z R d ⊓ Q R (path.walk.getVert (path.walk.length-2))
      let K₂ := Z R (act R x d) ⊓ Q R (path.walk.getVert (path.walk.length-2))
      ¬ Z R z ≤ normalizer ((K₁ ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      ⁅K₂,Z R z ⊓ Q R a⁆ = ⊥ ∧ ⁅K₂ ⊔ Z R a,Z R z⁆ ≤ Z R a ∧
        (Q R z).relIndex (K₂ ⊔ Z R a) = 4 := by
  intro R geometry hb a z d t path hat hdt heq x hx hsep K₁ K₂ hbad
  obtain hnorm | ⟨ha4,hz4,hX,_,hroot,_,_⟩ :=
    c.original_critical_kernel_endpoint_alternative eK geometry hb path hat hdt
  · exact (hbad hnorm).elim
  let A := Z R z ⊓ Q R a
  let Y := (K₁ ⊔ K₂) ⊔ Z R a
  have hfix : act R x a = a := hx
  have hat₂ : Adjacent R a (act R x t) := by
    rw [←hfix]
    exact (adjacent_act_iff R x _ _).mpr hat
  have hdt₂ := (adjacent_act_iff R x _ _).mpr hdt
  have heq₂ : LocalPackage.J R (act R x d) (act R x t) = LocalPackage.J R a (act R x t) := by
    rw [←hfix,smallMoverJoin_act,smallMoverJoin_act,heq]
  have hZaQ : Z R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a path.start_color)
    rw [geometry.distance_constant a path.start_color,path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hpairV : K₁ ⊔ K₂ ≤ V R a :=
    (sup_le_sup inf_le_left inf_le_left).trans
      (ChapterC.Sp4Four.DistanceReduction.paired_seed_le_radius hat hdt x hx)
  have hYV : Y ≤ V R a := sup_le hpairV (Z_le_VBall R a 2)
  have hY : Y ≤ V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)) :=
    le_inf hYV (sup_le (sup_le inf_le_right inf_le_right) hZaQ)
  have hpair : ⁅K₁ ⊔ K₂,A⁆ ≤ Z R a :=
    (commutator_mono (sup_le_sup inf_le_left inf_le_left) inf_le_right).trans
      (c.original_equal_mover_pair_displacement eK geometry hb path.start_color hat hdt heq hX x hx)
  have hZaA : ⁅Z R a,A⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono le_rfl inf_le_right).trans (geometry.centralizes a path.start_color).le)
  have hbound : ⁅Y,A⁆ ≤ Z R a :=
    commutator_sup_le_of_relative_normal (V R a) (K₁ ⊔ K₂) (Z R a) A (Z R a)
      ((geometry.V_le_Q (by omega) a path.start_color).trans
        ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Z_normalized R a)))
      hpairV (Z_le_VBall R a 2) hpair (hZaA ▸ bot_le)
  have hn : ¬ ⁅Y,Z R z⁆ ≤ Z R a := by
    intro h
    exact hbad (le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono (sup_le (le_sup_left.trans le_sup_left) le_sup_right) le_rfl).trans h).trans le_sup_right))
  have hzero : ⁅K₂,A⁆ = ⊥ := by
    rcases c.original_truncated_section_common_root eK geometry hb path Y le_sup_right hY hbound hn
      K₂ (le_sup_right.trans le_sup_left) with hzero | hroot₂
    · exact hzero
    have hd₂ : color R (act R x d) = false := by
      have h := adjacent_color_ne R hat₂
      have h' := adjacent_color_ne R hdt₂
      rw [path.start_color] at h
      cases he : color R (act R x d) <;> cases ht : color R (act R x t) <;> simp_all
    obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
      m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
      (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    have hAJ : A ≤ LocalPackage.J R (act R x d) (act R x t) := inf_le_right.trans
      (heq₂ ▸ LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le path.start_color hat₂)
    have hsecond : ⁅Z R a,Z R z⁆ ≤ centralizer
        (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R)) := by
      rw [←hroot₂,commutator_comm]
      exact (commutator_mono hAJ inf_le_left).trans (c.original_edge_mover_quadratic eK hd₂ hdt₂)
    have hfirst := c.original_equal_mover_kernel_failure_fixes_root eK geometry hb path hat hdt heq hbad
    have hzero' : ⁅Z R a,Z R z⁆ ≤ (⊥ : Subgroup (FreeAmalgam R)) := hsep ▸
      le_inf (le_inf (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path) hfirst) hsecond
    exact (c.original_critical_commutator_not_le_vertex_center eK geometry path path.start_color
      (hzero'.trans bot_le)).elim
  refine ⟨hzero,?_⟩
  have hmate : K₂ ⊔ Z R a ≤ Y := sup_le (le_sup_right.trans le_sup_left) le_sup_right
  apply c.original_truncated_section_control_of_central_hyperplane eK geometry hb path
    (K₂ ⊔ Z R a) le_sup_right (hmate.trans hY) ha4 hz4
  apply commutator_eq_bot_iff_le_centralizer.mpr
  exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hzero)
    (commutator_eq_bot_iff_le_centralizer.mp hZaA)

/-- Apply full-kernel control to the actual equal-mover root branch. The
same selected pair retains its three residual generators, strict movement,
separated fixed spaces and original overlapping backward paths. -/
theorem original_equal_mover_root_kernel_configuration
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
        let K₁ := Z R d₁ ⊓ Q R (path.walk.getVert (path.walk.length-2))
        let K₂ := Z R d₂ ⊓ Q R (path.walk.getVert (path.walk.length-2))
        Adjacent R a t₁ ∧ Adjacent R d₁ t₁ ∧
        LocalPackage.J R d₁ t₁ = LocalPackage.J R a t₁ ∧
        Ltilde R a ≤ (LocalPackage.J R d₁ t₁ ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) ∧
        ((Z R a ⊓ centralizer (LocalPackage.J R d₁ t₁ : Set (FreeAmalgam R))) ⊓
          centralizer (LocalPackage.J R d₂ t₂ : Set (FreeAmalgam R))) = ⊥ ∧
        4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d₁) ∧
        ((∃ back : CriticalPath R geometry d₁ (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=t₁ ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∨
        (∃ back : CriticalPath R geometry d₂ (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=t₂ ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i)) ∧
        (Z R z ≤ normalizer ((K₁ ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) ∨
          Z R z ≤ normalizer ((K₂ ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)) ∧
        (¬ Z R z ≤ normalizer ((K₁ ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
          ⁅K₂,Z R z ⊓ Q R a⁆ = ⊥ ∧ ⁅K₂ ⊔ Z R a,Z R z⁆ ≤ Z R a ∧
            (Q R z).relIndex (K₂ ⊔ Z R a) = 4) := by
  intro R geometry hb a z path heq hbad
  obtain h | ⟨ha4,hz4,hX,_⟩ := c.original_radius_displacement_or_root eK geometry path
  · exact (hbad h).elim
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
  exact ⟨g,hg,x,hx,hat₁,hdt₁,heq₁,hgen,hsep,hmove,
    c.original_equal_mover_pair_backward_path eK geometry hb path hat₁ hdt₁ heq₁ hX
      ha4 hz4 x hx hgen hsep hmove,
    c.original_equal_mover_paired_critical_kernel_normalized eK geometry hb path hat₁ hdt₁ heq₁ x hxS hsep,
    c.original_equal_mover_critical_kernel_mate_displacement eK geometry hb path hat₁ hdt₁ heq₁ x hxS hsep⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
