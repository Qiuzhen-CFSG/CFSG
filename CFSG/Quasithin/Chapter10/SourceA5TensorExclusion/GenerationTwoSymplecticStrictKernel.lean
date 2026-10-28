module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticOuterSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.StrictIndex.Kernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSmallDisplacement

/-!
# The full original kernel in the small-movement branch

Every original edge has a neighboring natural seed with nontrivial B-index.
The centralizer T0=C_Qa(U_d intersect B_a) is normal in the original starting
stabilizer. If the B-index is at most four, the marked natural action proves
|[U_d,T0]| at most four. The actual canonical edge mover centralizes this
commutator and normalizes the complete T0-fixed subgroup of U_d.

The critical-path consumer uses the literal second vertex and includes the
whole radius in T0 when b>4. These deductions establish the kernel inputs
of MS93 (5.9), printed p.920. Strict movement, the two distance exclusions,
and SymplecticPlaneRecognition remain to be proved.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterC.Sp4Four.DistanceReduction.StrictIndex
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

private theorem original_residual_edge_factorization :
    pResidual 2 c.M ⊔ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M) = ⊤ := by
  apply eq_top_iff.mpr
  intro x _
  obtain ⟨k,hk,r,hr,rfl⟩ := c.component_product.2.2.2 x
  exact Subgroup.mul_mem _ (mem_sup_left hk) (mem_sup_right hr)

/-- Every original edge has a genuinely moving neighboring natural seed.
This is nontrivial movement; the strict source bound is greater than four. -/
theorem original_exists_moving_neighbor
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a t : Vertex R}, color R a = false → Adjacent R a t →
      ∃ d, Adjacent R d t ∧
        1 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) := by
  intro R geometry a t ha hat
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  obtain ⟨_,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hne : Z R a ≠ ⊥ := by
    intro hz
    have hh := c.original_Z_card eK a ha
    rw [hz,card_bot] at hh
    omega
  obtain ⟨d,hdt,hn⟩ := exists_neighbor_seed_join_not_normalized hms geometry hb ha hat hne
  have hd : color R d = false := by
    have h₁ := adjacent_color_ne R hat
    have h₂ := adjacent_color_ne R hdt
    rw [ha] at h₁
    cases he : color R t <;> cases he' : color R d <;> simp_all
  let := finite_Z R d
  let : Finite (U R d) := Finite.of_injective (inclusion (U_le_Z d)) (inclusion_injective _)
  have hi : (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) ≠ 0 :=
    index_ne_zero_of_finite
  refine ⟨d,hdt,?_⟩
  by_contra! hle
  have heq : (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) = 1 := by omega
  apply hn
  apply neighbor_join_normalized_of_le_B geometry hb c.original_residual_edge_factorization ha hat hdt
  rw [c.original_Z_eq_U d hd]
  exact relIndex_eq_one.mp heq

/-- The literal T0 in the strict-index calculation is normal in the original
starting stabilizer, without any numerical movement assumption. -/
theorem original_strict_kernel_normalized :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
        stabilizer R a ≤ normalizer (kernelCentralizer geometry a d : Set _) := by
  intro R geometry hb a d t ha hat hdt
  exact kernelCentralizer_normalized_at_edge geometry hb c.original_residual_edge_factorization ha hat hdt

/-- In the small-movement branch the canonical neighboring mover fixes H
and normalizes the complete T0-fixed subgroup of the original natural seed. -/
theorem original_small_movement_kernel_action
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) ≤ 4 →
      Nat.card (kernelCommutator geometry a d) ≤ 4 ∧
      kernelCommutator geometry a d ≤ centralizer (LocalPackage.J R d t : Set _) ∧
      LocalPackage.J R d t ≤ normalizer
        ((U R d ⊓ centralizer (kernelCentralizer geometry a d : Set _) :
          Subgroup (FreeAmalgam R)) : Set _) := by
  intro R geometry hb a d t ha hat hdt hmove
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
    rw [ha] at h
    cases he : color R t <;> simp_all
  have hd : color R d = false := by
    have h := adjacent_color_ne R hdt
    rw [ht] at h
    cases he : color R d <;> simp_all
  let A := kernelCentralizer geometry a d
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
  have hsmall : (centralizer (A : Set (FreeAmalgam R))).relIndex (U R d) ≤ 4 :=
    (kernelCentralizer_moving_index_le geometry a d).trans hmove
  have hQt : IsPGroup 2 (Q R t) := by
    obtain ⟨i,_,_,hiT,_,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le hd hdt
    rw [←hiT]
    exact hodd.isPGroup.map i
  have hAT : A ≤ Q R t := inf_le_left.trans (Q_le_adjacent_h R ht hat)
  have hindices := (c.original_small_mover_join_indices eK hd hdt).2
  have hH := original_large_small_mover_centralizes_commutator R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq hd hfixed (Q R t) (LocalPackage.J R d t) A hQt
    (fun _ hx => hx.2 d (adjacent_symm R hdt)) (LocalPackage.J_le_radical R d t)
    hAT hindices.1 hindices.2.le (Or.inl hsmall)
  have hN := original_small_mover_join_normalizes_kernel R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq hd hfixed (Q R t) A hQt
    (fun _ hx => hx.2 d (adjacent_symm R hdt)) (Q_le_adjacent_h R ht hdt) hAT hsmall
  have hcardH := original_small_displacement_card_eq_index R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq hd hfixed A (hAT.trans (fun _ hx => hx.2 d (adjacent_symm R hdt))) hsmall
  refine ⟨?_,by simpa only [kernelCommutator,commutator_comm] using hH,hN⟩
  simpa only [kernelCommutator,commutator_comm] using hcardH.le.trans hsmall

/-- Apply the strict-index kernel calculation at the literal second vertex
of the original critical path, preserving T0 and H from MS93 (5.9). -/
theorem original_critical_small_movement_kernel
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex
        (U R (path.walk.getVert 2)) ≤ 4 →
      stabilizer R a ≤ normalizer (kernelCentralizer geometry a (path.walk.getVert 2) : Set _) ∧
      V R a ≤ kernelCentralizer geometry a (path.walk.getVert 2) ∧
      Nat.card (kernelCommutator geometry a (path.walk.getVert 2)) ≤ 4 ∧
      kernelCommutator geometry a (path.walk.getVert 2) ≤
        centralizer (LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) : Set _) ∧
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) ≤ normalizer
        ((U R (path.walk.getVert 2) ⊓ centralizer
          (kernelCentralizer geometry a (path.walk.getVert 2) : Set _) :
            Subgroup (FreeAmalgam R)) : Set _) := by
  intro R geometry hb a z path hmove
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  exact ⟨c.original_strict_kernel_normalized geometry (by change 2 < geometry.b R; omega) path.start_color hat hdt,
    radius_le_kernelCentralizer_at_edge geometry hb path.start_color hat hdt,
    c.original_small_movement_kernel_action eK geometry (by change 2 < geometry.b R; omega) path.start_color hat hdt hmove⟩
end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
