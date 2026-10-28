module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticCriticalMoverControl

/-!
# Exact original large critical images and full kernels

The original critical action is quadratic on the entire natural seed. Its
fixed quotient has order at most sixteen; reversing the literal path gives
the same bound on the opposite image. The existing image gap now leaves
only the reciprocal pairs (4,4) and (16,16).

In the latter case fixed-space saturation identifies the actual critical
commutator with both full endpoint kernels and with the whole intersection
of the seeds. Its order is sixteen. Equal first movers fix the large kernel
pointwise, so the full kernel is normalized in both image-size branches.

Apply this to the actual positioned backward path from a small critical
image: its kernel joins with the old seed to give exactly that seed, which
discharges endpoint normalization. Repeated unequal-mover paths have only
order-sixteen images; repeated paths from a small image have normalized
full kernels at every step. All original kernels and conjugators remain.

Large-image selection, both terminal large-distance contradictions,
distance four and full plane recognition remain to be proved. In
particular none of these results identifies X with Z in the large branch.

Source: MS93 (3.3), (5.5)--(5.11), pp.867,915--924; the center-free natural
specialization of Aschbacher--Smith 9.3.10, printed pp.734--735.
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

/-- The whole original critical image has order at most sixteen. The
opposite seed is quadratic on the full natural seed, and its action image
has at least four elements. The original centralizer identifies the kernel. -/
theorem original_critical_index_le_sixteen
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (_path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) ≤ 16 := by
  intro R geometry a z path
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
  have hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hcore : x ∈ fixedCore R a := ⟨
      ((U_le_Z a).trans (geometry.omega_bound a path.start_color
        (by rwa [geometry.distance_constant a path.start_color])) |>.trans (omegaCenter_le _)) hx.1,hx.2⟩
    rwa [c.original_fixedCore_eq_bot a path.start_color] at hcore
  have rev := c.original_critical_reverse eK geometry hb path
  have hlarge : 2 < (Q R a).relIndex (Z R z) := by
    rcases c.original_critical_image_gap eK geometry rev with h | h
    · rw [h]; decide
    · change 16 ≤ (Q R a).relIndex (Z R z) at h
      omega
  have hZQ : Z R z ≤ Q R z :=
    (geometry.omega_bound z path.end_color
      (by rw [geometry.distance_constant z path.end_color]; exact hb)).trans (omegaCenter_le _)
  have hZZ : Z R z ≤ centralizer (Z R z : Set (FreeAmalgam R)) :=
    hZQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color)))
  have hquad : ⁅Z R z,U R a⁆ ≤ centralizer (Z R z : Set (FreeAmalgam R)) := by
    rw [←c.original_Z_eq_U a path.start_color,commutator_comm]
    exact (critical_commutator_le_endpoint ⟨a,z,path⟩).trans hZZ
  have h := original_quadratic_actor_fixed_index_le_sixteen R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path.start_color hfixed (Z R z)
    (path.endpoint_Z_le_start_stabilizer hb) hlarge hquad
  rw [←c.original_Z_eq_U a path.start_color,←inf_relIndex_left,
    ←c.original_critical_seed_kernel_eq_centralizer eK geometry path,inf_relIndex_left] at h
  exact h

/-- There are exactly two reciprocal image sizes in the original natural
geometry; the formerly unbounded large-image alternative is exactly sixteen. -/
theorem original_critical_indices_four_or_sixteen
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (_path : CriticalPath R geometry a z),
      ((Q R z).relIndex (Z R a) = 4 ∧ (Q R a).relIndex (Z R z) = 4) ∨
      ((Q R z).relIndex (Z R a) = 16 ∧ (Q R a).relIndex (Z R z) = 16) := by
  intro R geometry a z path
  have hb : 0 < geometry.b R := lt_of_lt_of_le (by decide : 0 < 4)
    (c.original_geometry_four_le eK geometry)
  have rev := c.original_critical_reverse eK geometry hb path
  by_cases hsmall : (Q R z).relIndex (Z R a) < 16
  · have h := c.original_small_critical_data eK geometry path hsmall
    exact Or.inl ⟨h.1,h.2.1⟩
  · right
    have haz : (Q R z).relIndex (Z R a) = 16 :=
      Nat.le_antisymm (c.original_critical_index_le_sixteen eK geometry path) (by omega)
    refine ⟨haz,?_⟩
    apply Nat.le_antisymm (c.original_critical_index_le_sixteen eK geometry rev)
    by_contra! hsm
    have h := (c.original_small_critical_data eK geometry rev hsm).2.1
    rw [haz] at h
    omega

/-- In the large-image branch the critical commutator is the entire original
kernel on either side, and is exactly the intersection of the full seeds. -/
theorem original_large_critical_root_eq_kernels
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (_path : CriticalPath R geometry a z),
      4 < (Q R z).relIndex (Z R a) →
      ⁅Z R a,Z R z⁆ = Z R a ⊓ Q R z ∧
      ⁅Z R a,Z R z⁆ = Z R z ⊓ Q R a ∧
      ⁅Z R a,Z R z⁆ = Z R a ⊓ Z R z ∧
      Nat.card (⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) = 16 := by
  intro R geometry a z path hlarge
  have hb : 0 < geometry.b R := lt_of_lt_of_le (by decide : 0 < 4)
    (c.original_geometry_four_le eK geometry)
  have rev := c.original_critical_reverse eK geometry hb path
  have hindices : (Q R z).relIndex (Z R a) = 16 ∧ (Q R a).relIndex (Z R z) = 16 := by
    rcases c.original_critical_indices_four_or_sixteen eK geometry path with h | h
    · rw [h.1] at hlarge; omega
    · exact h
  have hZaQ : Z R a ≤ Q R a :=
    (geometry.omega_bound a path.start_color
      (by rw [geometry.distance_constant a path.start_color]; exact hb)).trans (omegaCenter_le _)
  have hZzQ : Z R z ≤ Q R z :=
    (geometry.omega_bound z path.end_color
      (by rw [geometry.distance_constant z path.end_color]; exact hb)).trans (omegaCenter_le _)
  have hRa := ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path
  have hRz := critical_commutator_le_endpoint ⟨a,z,path⟩
  have ha : ⁅Z R a,Z R z⁆ = Z R a ⊓ Q R z := by
    apply le_antisymm (le_inf hRa (hRz.trans hZzQ))
    rw [c.original_critical_seed_kernel_eq_centralizer eK geometry path]
    exact c.original_large_critical_fixed_le_root eK geometry path (by rw [hindices.2]; decide)
  have hz : ⁅Z R a,Z R z⁆ = Z R z ⊓ Q R a := by
    apply le_antisymm (le_inf hRz (hRa.trans hZaQ))
    rw [c.original_critical_seed_kernel_eq_centralizer eK geometry rev,commutator_comm]
    exact c.original_large_critical_fixed_le_root eK geometry rev hlarge
  have hi : ⁅Z R a,Z R z⁆ = Z R a ⊓ Z R z :=
    le_antisymm (le_inf hRa hRz) ((inf_le_inf_left _ hZzQ).trans_eq ha.symm)
  refine ⟨ha,hz,hi,?_⟩
  let := finite_Z R a
  let : Finite (Z R a ⊓ Q R z : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (Z R a ⊓ Q R z) (Z R a) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hindices.1,
    c.original_Z_card eK a path.start_color] at hmul
  rw [ha]
  omega

/-- If the first full movers agree, the large critical kernel is fixed
pointwise by that common mover. No X=Z identification is needed. -/
theorem original_large_critical_kernel_fixed_by_first_mover
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      4 < (Q R z).relIndex (Z R a) →
      Z R a ⊓ Q R z =
        Z R a ⊓ centralizer (LocalPackage.J R a (path.walk.getVert 1) : Set (FreeAmalgam R)) := by
  intro R geometry hb a z path heq hlarge
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
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hzJ : Z R z ≤ LocalPackage.J R a (path.walk.getVert 1) := by
    rw [←heq]
    exact hzQ.trans (LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le hd hdt)
  have hrev : 4 < (Q R a).relIndex (Z R z) := by
    rcases c.original_critical_indices_four_or_sixteen eK geometry path with h | h
    · rw [h.1] at hlarge; omega
    · rw [h.2]; decide
  rw [c.original_critical_seed_kernel_eq_centralizer eK geometry path]
  exact c.original_large_edge_subactor_fixed_eq eK path.start_color hat (Z R z) hzJ hrev

/-- Equality of the first movers now gives normalization of the whole
critical kernel for both image sizes. The large branch is fixed pointwise. -/
theorem original_equal_mover_critical_kernel_normalized
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      LocalPackage.J R a (path.walk.getVert 1) ≤ normalizer
        ((Z R a ⊓ Q R z : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  intro R geometry hb a z path heq
  by_cases hsmall : (Q R z).relIndex (Z R a) ≤ 4
  · have hat : Adjacent R a (path.walk.getVert 1) := by
      have h := (cosetGraph_adj R _ _).mp
        (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
      simpa only [SimpleGraph.Walk.getVert_zero] using h
    apply c.original_critical_small_kernel_normalized eK geometry path hat _ hsmall
    rw [SimpleGraph.dist_comm,path.dist_end,path.length_eq_b]
    change geometry.b R-1 < geometry.b R
    omega
  · have hfix := c.original_large_critical_kernel_fixed_by_first_mover eK geometry hb path heq
      (Nat.lt_of_not_ge hsmall)
    exact (le_centralizer_iff.mp (hfix.le.trans inf_le_right)).trans (Subgroup.centralizer_le_normalizer _)

/-- The actual positioned backward choice from a small critical path has
an exact order-sixteen kernel and root. The kernel joined with the old seed
is the old seed itself, so the original endpoint normalizes it. -/
theorem original_small_critical_positioned_backward_full_kernel
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) < 16 →
      ∃ g ∈ stabilizer R a,
        ∃ back : CriticalPath R geometry (act R g (path.walk.getVert 2))
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = act R g (path.walk.getVert 1) ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        LocalPackage.J R (act R g (path.walk.getVert 2)) (back.walk.getVert 1) =
          LocalPackage.J R a (back.walk.getVert 1) ∧
        (Q R (path.walk.getVert (path.walk.length-2))).relIndex
          (Z R (act R g (path.walk.getVert 2))) = 16 ∧
        let K := Z R (act R g (path.walk.getVert 2)) ⊓ Q R (path.walk.getVert (path.walk.length-2))
        K = ⁅Z R (act R g (path.walk.getVert 2)),Z R (path.walk.getVert (path.walk.length-2))⁆ ∧
        Nat.card K = 16 ∧ K ⊔ Z R a = Z R a ∧
        K ≤ centralizer (LocalPackage.J R a (back.walk.getVert 1) : Set (FreeAmalgam R)) ∧
        Z R z ≤ normalizer ((K ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) ∧
        ¬ K ≤ Z R (path.walk.getVert 2) := by
  intro R geometry hb a z path hsmall
  obtain ⟨g,hg,back,hbt,hover,heq,hlarge,hescape⟩ :=
    c.original_small_critical_positioned_backward eK geometry hb path hsmall
  have h16 : (Q R (path.walk.getVert (path.walk.length-2))).relIndex
      (Z R (act R g (path.walk.getVert 2))) = 16 :=
    Nat.le_antisymm (c.original_critical_index_le_sixteen eK geometry back) hlarge
  have hroot := c.original_large_critical_root_eq_kernels eK geometry back
    (by
      change 4 < (Q R (path.walk.getVert (path.walk.length-2))).relIndex
        (Z R (act R g (path.walk.getVert 2)))
      rw [h16]
      decide)
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hblen : 4 < back.walk.length := by
    rw [back.length_eq_b]
    change 4 < geometry.b R
    exact hb
  have htwo : back.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
  have hfirst : LocalPackage.J R (back.walk.getVert 2) (back.walk.getVert 1) =
      LocalPackage.J R (act R g (path.walk.getVert 2)) (back.walk.getVert 1) := by
    rw [htwo]; exact heq.symm
  have hfixed := c.original_large_critical_kernel_fixed_by_first_mover eK geometry hb back hfirst
    (by
      change 4 < (Q R (path.walk.getVert (path.walk.length-2))).relIndex
        (Z R (act R g (path.walk.getVert 2)))
      rw [h16]
      decide)
  have hat : Adjacent R a (back.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (back.walk.adj_getVert_succ (by omega : 1 < back.walk.length))
    rw [htwo] at h
    exact adjacent_symm R h
  have hdt : Adjacent R (act R g (path.walk.getVert 2)) (back.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (back.walk.adj_getVert_succ (by omega : 0 < back.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hle := c.original_equal_mover_backward_root_le_intermediate_seed eK geometry hb path back
    hat hdt heq (c.original_small_critical_data eK geometry path hsmall).2.2
  let K := Z R (act R g (path.walk.getVert 2)) ⊓ Q R (path.walk.getVert (path.walk.length-2))
  have hjoin : K ⊔ Z R a = Z R a := sup_eq_right.mpr (hroot.1.symm.le.trans hle)
  refine ⟨g,hg,back,hbt,hover,heq,h16,hroot.1.symm,?_,hjoin,?_,?_,?_⟩
  · rw [←hroot.1]; exact hroot.2.2.2
  · rw [heq] at hfixed
    exact hfixed.le.trans inf_le_right
  · rw [hjoin]
    exact (path.endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized R a)
  · exact fun h => hescape (hroot.1.le.trans h)

/-- On a repeated path with unequal first movers, every image is exactly
sixteen and each critical root is the entire kernel. A shifted small image
would force equality and transport it back to the original path. -/
theorem original_unequal_mover_sequence_exact_kernels
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R → ∀ p : CriticalSegment geometry,
      ¬ MoverAgreement p 0 →
      ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
        (∀ n, BackwardLink geometry OrbitChoice (s n) (s (n+1))) ∧
        (∀ n, (Q R (s n).last).relIndex (Z R (s n).first) = 16 ∧
          (Q R (s n).first).relIndex (Z R (s n).last) = 16 ∧
          ⁅Z R (s n).first,Z R (s n).last⁆ = Z R (s n).first ⊓ Q R (s n).last ∧
          ⁅Z R (s n).first,Z R (s n).last⁆ = Z R (s n).last ⊓ Q R (s n).first ∧
          Nat.card (⁅Z R (s n).first,Z R (s n).last⁆ : Subgroup (FreeAmalgam R)) = 16) := by
  intro R geometry hb p hne
  obtain ⟨s,hs0,hs,_,_,_⟩ := c.original_overlapping_sequence_with_conjugators eK geometry hb p
  refine ⟨s,hs0,hs,?_⟩
  intro n
  have hi : (Q R (s n).last).relIndex (Z R (s n).first) = 16 ∧
      (Q R (s n).first).relIndex (Z R (s n).last) = 16 := by
    rcases c.original_critical_indices_four_or_sixteen eK geometry (s n).path with h | h
    · have heq : MoverAgreement (s n) 0 := by
        simpa only [MoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
          c.original_small_critical_first_movers_eq eK geometry hb (s n).path
            (by rw [h.1]; decide)
      exact (hne (hs0 ▸ (sequence_first_mover_agreement_iff (by change 2 ≤ geometry.b R; omega) s hs n).mp heq)).elim
    · exact h
  have hr := c.original_large_critical_root_eq_kernels eK geometry (s n).path
    (by rw [hi.1]; decide)
  exact ⟨hi.1,hi.2,hr.1,hr.2.1,hr.2.2.2⟩

/-- Starting from an actual small critical path, the image-improving
sequence has normalized full critical kernels at every step, including all
large-image steps. No further image-size or mover-equality premise remains. -/
theorem original_small_critical_sequence_normalized_kernels
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R → ∀ p : CriticalSegment geometry,
      (Q R p.last).relIndex (Z R p.first) < 16 →
      ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
        (∀ n, BackwardLink geometry OrbitChoice (s n) (s (n+1))) ∧
        (∀ n, LocalPackage.J R (s n).first ((s n).path.walk.getVert 1) ≤
          normalizer ((Z R (s n).first ⊓ Q R (s n).last : Subgroup (FreeAmalgam R)) : Set _)) ∧
        (∀ n, (Q R (s n).last).relIndex (Z R (s n).first) < 16 →
          (Q R (s (n+1)).last).relIndex (Z R (s (n+1)).first) = 16) := by
  intro R geometry hb p hsmall
  obtain ⟨s,hs0,hs,hagree,hlarge,_,_,_⟩ :=
    c.original_small_critical_repeated_mover_control eK geometry hb p hsmall
  refine ⟨s,hs0,hs,?_,?_⟩
  · intro n
    apply c.original_equal_mover_critical_kernel_normalized eK geometry hb (s n).path
    simpa only [MoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero,
      Nat.add_zero] using hagree n 0 (by change 2*0+2 ≤ geometry.b R; omega)
  · intro n hn
    exact Nat.le_antisymm (c.original_critical_index_le_sixteen eK geometry (s (n+1)).path)
      (hlarge n hn)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
