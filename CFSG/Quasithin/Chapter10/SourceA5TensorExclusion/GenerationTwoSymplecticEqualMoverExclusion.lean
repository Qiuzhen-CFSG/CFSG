module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticUnequalCriticalSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalLargePlaneGeneration

/-!
# The original equal-mover large-distance branch is impossible

For a large critical image, the original endpoint belongs to the common
plane mover. An invertible shear in its marked image generates Sp₄ with
an opposite plane radical. The conjugator lifts inside the original
residual, and the full kernel restores generation upstairs. Strict movement
and the proved endpoint normalization give the actual backward path.
Both possible backward critical images contradict these generators.

A small starting image already has a positioned large backward image with
the same mover agreement. Applying the large-image exclusion there closes
the entire equal-mover branch, and hence every small critical image at
distance greater than four. GenerationTwoSymplecticDistanceBound uses the full edge Sylow to close
the remaining unequal-mover branch. The distance-four exclusion and the
final original marked-plane recognition remain open.

Source: MS93 (5.5)--(5.11), pp.915--924, specialized to the vanishing
original fixed core in Aschbacher--Smith 9.3.10, pp.734--735.
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

/-- An actual residual conjugate of the common first mover generates with
the large critical endpoint, retaining the entire original action kernel. -/
theorem original_large_equal_mover_residual_generator
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      4 < (Q R z).relIndex (Z R a) →
      ∃ g ∈ Ltilde R a,
        Ltilde R a ≤ ((LocalPackage.J R a (path.walk.getVert 1)).map
          (MulAut.conj g).toMonoidHom) ⊔ Z R z := by
  intro R geometry hb a z path heq hlarge
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hd : color R (path.walk.getVert 2) = false :=
    (path.vertex_color (by omega)).mpr (by decide)
  have hza : 4 < (Q R a).relIndex (Z R z) := by
    rcases c.original_critical_indices_four_or_sixteen eK geometry path with h | h
    · rw [h.1] at hlarge; omega
    · rw [h.2]; decide
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
  have hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hcore : x ∈ fixedCore R a := ⟨
      ((U_le_Z a).trans (geometry.omega_bound a path.start_color
        (by
          rw [geometry.distance_constant a path.start_color]
          change 0 < geometry.b R
          exact (by omega : 0 < geometry.b R))) |>.trans (omegaCenter_le _)) hx.1,hx.2⟩
    rwa [c.original_fixedCore_eq_bot a path.start_color] at hcore
  have ht : color R (path.walk.getVert 1) = true := by
    have h := adjacent_color_ne R hat
    rw [path.start_color] at h
    cases he : color R (path.walk.getVert 1) <;> simp_all
  obtain ⟨i,_,_,hiT,_,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le
    path.start_color hat
  have hQt : IsPGroup 2 (Q R (path.walk.getVert 1)) := hiT ▸ hodd.isPGroup.map i
  have hindices := c.original_small_mover_join_indices eK path.start_color hat
  have hzQd : Z R z ≤ Q R (path.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt R z (geometry.exists_critical z path.end_color)
    rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,path.dist_end,path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hzE : Z R z ≤ LocalPackage.J R a (path.walk.getVert 1) := by
    rw [←heq]
    exact hzQd.trans (LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le hd hdt)
  exact original_small_mover_large_subactor_generator R hms hodd.isPGroup hne hodd.twoCore_le
    hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path (by omega) hza hfixed (LocalPackage.J R a (path.walk.getVert 1))
    ((LocalPackage.J_le_radical R a (path.walk.getVert 1)).trans
      (fun _ hx => hx.2 a (adjacent_symm R hat)))
    (LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le path.start_color hat)
    (hQt.to_le (LocalPackage.J_le_radical R a (path.walk.getVert 1))) hindices.2.1 hindices.2.2.le hzE

/-- The large critical image is incompatible with equal full first movers.
The selected residual generator gives a literal backward path; both its
small and its large image alternatives contradict the original fixed core. -/
theorem false_of_original_large_critical_equal_movers
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      4 < (Q R z).relIndex (Z R a) → False := by
  intro R geometry hb a z path heq hlarge
  obtain ⟨g,hg,hgen⟩ := c.original_large_equal_mover_residual_generator eK geometry hb path heq hlarge
  have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  have hga : act R g⁻¹ a = a := hgS
  let d := act R g⁻¹ (path.walk.getVert 2)
  let t := act R g⁻¹ (path.walk.getVert 1)
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat₀ : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt₀ : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hat : Adjacent R a t := by
    simpa only [hga] using (adjacent_act_iff R g⁻¹ _ _).mpr hat₀
  have hdt : Adjacent R d t := (adjacent_act_iff R g⁻¹ _ _).mpr hdt₀
  have hgen' : Ltilde R a ≤ LocalPackage.J R d t ⊔ Z R z := by
    change Ltilde R a ≤ LocalPackage.J R (act R g⁻¹ (path.walk.getVert 2))
      (act R g⁻¹ (path.walk.getVert 1)) ⊔ Z R z
    rw [smallMoverJoin_act,inv_inv,heq]
    exact hgen
  have hmove : 4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
      (geometry.Z_normal a)).relIndex (U R d) := by
    rw [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega)
      path.start_color g⁻¹ hgS]
    exact c.original_critical_strict_movement eK geometry hb path
  have hbad : ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
    intro hn
    have hJ := (LocalPackage.J_le_radical R d t).trans
      (ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat hdt)
    have hh := c.original_normal_neighbor_join_moving_index_eq_one eK geometry
      (by change 2 < geometry.b R; omega) path.start_color hat hdt
      (hgen'.trans (sup_le hJ hn))
    change (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
      (geometry.Z_normal a)).relIndex (U R d) = 1 at hh
    omega
  have hnot : ¬ Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
    intro hkernel
    have hn := c.original_critical_kernel_endpoint_normalized_of_large eK geometry hb
      path hat hdt hlarge
    rw [inf_eq_left.mpr hkernel] at hn
    exact hbad hn
  obtain ⟨back,hbt,hover⟩ := ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
    geometry (by omega) path hat hdt hnot
  by_cases hsmall : (Q R (path.walk.getVert (path.walk.length-2))).relIndex (Z R d) ≤ 4
  · exact c.original_generated_backward_small_root_impossible eK geometry hb path back hat hdt hbt hgen' hsmall
  · exact c.original_generated_backward_large_root_impossible eK geometry hb path back hat hdt hbt hgen'
      (Nat.lt_of_not_ge hsmall)

/-- The entire equal-mover branch at original critical distance greater
than four is excluded. The small starting case uses its already constructed
large backward path, preserving the actual overlap and mover equality. -/
theorem false_of_original_critical_equal_movers
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) → False := by
  intro R geometry hb a z path heq
  by_cases hlarge : 4 < (Q R z).relIndex (Z R a)
  · exact c.false_of_original_large_critical_equal_movers eK geometry hb path heq hlarge
  obtain ⟨g,hg,back,hbt,hover,heqback,hi,hrest⟩ :=
    c.original_small_critical_positioned_backward eK geometry hb path
      (by change (Q R z).relIndex (Z R a) < 16; omega)
  have htwo : back.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (Nat.zero_le _)
  apply c.false_of_original_large_critical_equal_movers eK geometry hb back
  · rw [htwo]
    exact heqback.symm
  · omega

/-- Every remaining large-distance path has unequal full movers and both
critical images exactly sixteen. In particular the small-image branch is
closed, not merely replaced by a differently marked path. -/
theorem original_large_distance_unequal_sixteen
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) ≠
        LocalPackage.J R a (path.walk.getVert 1) ∧
      (Q R z).relIndex (Z R a) = 16 ∧ (Q R a).relIndex (Z R z) = 16 := by
  intro R geometry hb a z path
  have hne := c.false_of_original_critical_equal_movers eK geometry hb path
  refine ⟨hne,?_⟩
  rcases c.original_critical_indices_four_or_sixteen eK geometry path with h | h
  · exact (hne (c.original_small_critical_first_movers_eq eK geometry hb path
      (by rw [h.1]; decide))).elim
  · exact h

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
