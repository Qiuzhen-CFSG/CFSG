module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticStrictAction
public import Theory.GroupAction.TwoPerfectSection128

/-!
# The full fixed intersection and kernel escape for original small movement

For a genuinely moving neighboring seed, A = U_d intersect B_a has order
at most 128. The subgroup A Z_a is locally normal, and its commutator
with Q_a lies in A and is locally normal. The order-seventeen action bound
fixes that commutator under the residual; the entire original fixed core
is trivial, so A centralizes Q_a. Thus A lies in X_a and the literal
centralizer T0 is the full Q_a.

When X_a = Z_a and the moving index is at most four, the trivial action
would put all of U_d in Z_a and contradict genuine movement. Consequently
Q_a escapes Q_d, the commutator has order four and lies in Z_a, and its
full fixed hyperplane is U_d intersect Z_a, of order sixty-four.
The final theorem applies this to the original critical path, giving an
overlapping backward path or the precise remaining small-root configuration.
It does not assert unconditional backward existence or strict movement.

Source: MS93 (5.8)--(5.9), printed pp.919--922, specialized using the
center-free full original core in Aschbacher--Smith 9.3.10, pp.734--735.
The source span and generation argument, both distance exclusions and
SymplecticPlaneRecognition remain open.
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


/-- The full fixed core excludes every residual-invariant two-subgroup of
order at most 128 in the original neighborhood kernel. -/
theorem original_small_normal_core_eq_bot
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a : Vertex R}, color R a = false →
      ∀ N : Subgroup (FreeAmalgam R), N ≤ Q R a →
      Ltilde R a ≤ normalizer (N : Set _) → Nat.card N ≤ 128 → N = ⊥ := by
  intro R a ha N hN hn hcN
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
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
  obtain ⟨π,hπ,hπker⟩ := local_residual_projection R hodd.isPGroup hodd.twoCore_le
    q (QuotientGroup.ker_mk' _) ha
  let := finite_stabilizer R a
  let : Finite N := Finite.of_injective
    (inclusion (hN.trans (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)))
    (inclusion_injective _)
  let : Finite (Ltilde R a) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer a)) (inclusion_injective _)
  have hcomm : ⁅N,Ltilde R a⁆ ≤ ⊥ :=
    commutator_le_of_twoPerfect_simple_seventeen_section_le_128
      (Ltilde R a) N ⊥ (isPPerfect_embedded_pResidual_of_finite 2 _) π hπ hπker
      (by rw [hcard]; decide)
      ((Q_isPGroup R hodd.isPGroup hodd.twoCore_le a ha).to_le hN) hn
      (by rw [normalizer_eq_top]; exact le_top) (by simp) (by simpa only [relIndex_bot_left] using hcN)
  apply le_bot_iff.mp
  rw [←c.original_fixedCore_eq_bot a ha]
  exact le_inf hN (commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hcomm))

/-- A genuinely moving neighboring seed has its entire B-intersection in
X_a. Consequently the literal T0 is the full Q_a. -/
theorem original_moving_neighbor_fixed_intersection
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      1 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      U R d ⊓ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a) ≤ X R a ∧
      kernelCentralizer geometry a d = Q R a := by
  intro R geometry hb a d t ha hat hdt hmove
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [ha] at h
    cases he : color R t <;> simp_all
  have hd : color R d = false := by
    have h := adjacent_color_ne R hdt
    rw [ht] at h
    cases he : color R d <;> simp_all
  let A := U R d ⊓ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)
  let W := A ⊔ Z R a
  let N := ⁅W,Q R a⁆
  have hAQ : A ≤ Q R a :=
    (inf_le_left.trans (U_le_Z d)).trans
      ((le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)).trans
        (geometry.V_le_Q hb a ha))
  have hZQ : Z R a ≤ Q R a := (geometry.omega_bound a ha
    (by rw [geometry.distance_constant a ha]; change 0 < geometry.b R; omega)).trans (omegaCenter_le _)
  have hWQ : W ≤ Q R a := sup_le hAQ hZQ
  have hta : Q R t ≤ stabilizer R a := fun _ hx => hx.2 a (adjacent_symm R hat)
  have htd : Q R t ≤ stabilizer R d := fun _ hx => hx.2 d (adjacent_symm R hdt)
  have hTA : Q R t ≤ normalizer (A : Set _) :=
    (le_inf (htd.trans (U_normalized d))
      (hta.trans (Escape.Propagation.Rigidity.B_normalized hb a ha))).trans
        inf_normalizer_le_normalizer_inf
  have hQA : Q R a ≤ normalizer (A : Set _) := (Q_le_adjacent_h R ht hat).trans hTA
  have hAL : ⁅A,Ltilde R a⁆ ≤ Z R a := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    exact ((mem_B_iff R a (geometry.Z_normal a)
      ((geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)) x).mp hx.2).2 l hl
  have hLW : Ltilde R a ≤ normalizer (W : Set _) :=
    normalizes_sup_of_displacement _ _ _
      ((Ltilde_le_stabilizer a).trans (Z_normalized R a)) hAL
  have hTW : Q R t ≤ normalizer (W : Set _) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp (hTA hg),
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized R a (hta hg))]
  have hgen : pResidual 2 c.M ⊔ R = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨k,hk,r,hr,rfl⟩ := c.component_product.2.2.2 x
    exact Subgroup.mul_mem _ (mem_sup_left hk) (mem_sup_right hr)
  have hSW : stabilizer R a ≤ normalizer (W : Set _) := by
    rw [←ChapterC.RankTwo.Sp4Four.local_residual_edge_generation R hgen ha hat]
    exact sup_le hLW hTW
  have hNA : N ≤ A :=
    commutator_sup_le_of_relative_normal (Q R a) A (Z R a) (Q R a) A hQA hAQ hZQ
      (le_normalizer_iff_commutator_le_left.mp hQA)
      ((Z_centralizes_Q R a ha).le.trans bot_le)
  have hSN : stabilizer R a ≤ normalizer (N : Set _) := by
    intro g hg
    change g ∈ normalizer (⁅W,Q R a⁆ : Subgroup (FreeAmalgam R))
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hSW hg),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a hg)]
  let := finite_Z R d
  let : Finite (U R d) := Finite.of_injective (inclusion (U_le_Z d)) (inclusion_injective _)
  let : Finite A := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hU : Nat.card (U R d) = 256 := by
    rw [←c.original_Z_eq_U d hd]
    exact c.original_Z_card eK d hd
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R)) A (U R d) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hU] at hmul
  have hAc : Nat.card A ≤ 128 := by nlinarith
  have hNc : Nat.card N ≤ 128 :=
    (Nat.card_le_card_of_injective (inclusion hNA) (inclusion_injective _)).trans hAc
  have hN := c.original_small_normal_core_eq_bot eK ha N (hNA.trans hAQ)
    ((Ltilde_le_stabilizer a).trans hSN) hNc
  have hcomm : ⁅A,Q R a⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono le_sup_left le_rfl).trans_eq hN)
  have hC : A ≤ centralizer (Q R a : Set _) := commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hAX : A ≤ X R a := by
    let := geometry.Z_elementary (by omega) d hd
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨hAQ hx,
      elemPow_eq_one_of_isElementaryAbelian x ((U_le_Z d) hx.1),hC hx⟩
  refine ⟨hAX,le_antisymm inf_le_left (le_inf le_rfl (le_centralizer_iff.mp hC))⟩


/-- In the original X=Z branch, genuine small movement has no trivial-action
alternative: T0 is Q_a, escapes Q_d, and moves the full U_d into an order-four
subgroup of Z_a. Its fixed hyperplane is exactly U_d intersect Z_a. -/
theorem original_moving_root_small_kernel
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      X R a = Z R a →
      1 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) ≤ 4 →
      kernelCentralizer geometry a d = Q R a ∧
      ¬ Q R a ≤ Q R d ∧
      Nat.card (⁅U R d,Q R a⁆ : Subgroup (FreeAmalgam R)) = 4 ∧
      ⁅U R d,Q R a⁆ ≤ Z R a ∧
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) = 4 ∧
      U R d ⊓ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a) = U R d ⊓ Z R a ∧
      Nat.card (U R d ⊓ Z R a : Subgroup (FreeAmalgam R)) = 64 ∧
      (Q R d).relIndex (Q R a) ≤ 4 := by
  intro R geometry hb a d t ha hat hdt hX hmove hsmall
  obtain ⟨hAX,hT⟩ := c.original_moving_neighbor_fixed_intersection eK geometry hb ha hat hdt hmove
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [ha] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  have hZB := Escape.EdgeTransfer.Z_le_B (geometry := geometry) hb a ha
  have hAeq : U R d ⊓ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a) =
      U R d ⊓ Z R a := le_antisymm (le_inf inf_le_left (hAX.trans_eq hX))
        (inf_le_inf_left _ hZB)
  rcases c.original_small_movement_kernel_alternative eK geometry hb ha hat hdt hsmall with
    ⟨hzero,hH⟩ | ⟨hescape,hH,hB,hfix,hcard,hindex,hquad⟩
  · have hcomm : ⁅U R d,Q R a⁆ = ⊥ := by
      simpa only [kernelCommutator,hT] using hH
    have hUdQa : U R d ≤ Q R a := (U_le_Z d).trans
      ((le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)).trans
        (geometry.V_le_Q hb a ha))
    have hUdXa : U R d ≤ X R a := by
      let := geometry.Z_elementary (by omega) d hd
      intro x hx
      exact mem_omegaCenter_iff.mpr ⟨hUdQa hx,
        elemPow_eq_one_of_isElementaryAbelian x ((U_le_Z d) hx),
        (commutator_eq_bot_iff_le_centralizer.mp hcomm) hx⟩
    have hone := relIndex_eq_one.mpr ((hUdXa.trans_eq hX).trans hZB)
    omega
  · rw [hT] at hescape hfix hcard hindex hquad
    have hH' : Nat.card (⁅U R d,Q R a⁆ : Subgroup (FreeAmalgam R)) = 4 := by
      simpa only [kernelCommutator,hT] using hH
    have hquad' : ⁅U R d,Q R a⁆ ≤ centralizer (Q R a : Set _) := by
      simpa only [kernelCommutator,hT] using hquad
    have ht : color R t = true := by
      have h := adjacent_color_ne R hat
      rw [ha] at h
      cases he : color R t <;> simp_all
    have hHU : ⁅U R d,Q R a⁆ ≤ U R d :=
      le_normalizer_iff_commutator_le_left.mp
        (((Q_le_adjacent_h R ht hat).trans
          (show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt))).trans
          (U_normalized d))
    have hHZ : ⁅U R d,Q R a⁆ ≤ Z R a := by
      rw [←hX]
      let := geometry.Z_elementary (by omega) d hd
      intro x hx
      exact mem_omegaCenter_iff.mpr ⟨
        ((U_le_Z d).trans
          ((le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)).trans
            (geometry.V_le_Q hb a ha))) (hHU hx),
        elemPow_eq_one_of_isElementaryAbelian x ((U_le_Z d) (hHU hx)),hquad' hx⟩
    rw [hfix,hAeq] at hcard
    exact ⟨hT,hescape,hH',hHZ,hB,hAeq,hcard,hindex⟩


/-- On the literal original critical path, the only remaining alternative
to an overlapping backward path has a moving neighbor with T0=Q_a and an
actual order-four commutator in Z_a. The kernel-escape premise is discharged
in this alternative, with both original endpoint markings retained. -/
theorem original_backward_path_or_small_root_kernel
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      (∃ d t, Adjacent R a t ∧ Adjacent R d t ∧
        (∃ back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=t ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2))) ∨
      ((Q R z).relIndex (Z R a) = 4 ∧ (Q R a).relIndex (Z R z) = 4 ∧
        X R a = Z R a ∧ X R z = Z R z ∧
        ∃ d, Adjacent R d (path.walk.getVert 1) ∧
          kernelCentralizer geometry a d = Q R a ∧ ¬ Q R a ≤ Q R d ∧
          Nat.card (⁅U R d,Q R a⁆ : Subgroup (FreeAmalgam R)) = 4 ∧
          ⁅U R d,Q R a⁆ ≤ Z R a ∧
          (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) = 4 ∧
          U R d ⊓ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a) = U R d ⊓ Z R a ∧
          Nat.card (U R d ⊓ Z R a : Subgroup (FreeAmalgam R)) = 64 ∧
          (Q R d).relIndex (Q R a) ≤ 4) := by
  intro R geometry hb a z path
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  rcases c.original_radius_displacement_or_root eK geometry path with hdisp | ⟨haz,hza,hXa,hXz⟩
  · exact Or.inl (c.original_backward_path_of_radius_displacement eK geometry path hat hdisp)
  obtain ⟨d,hdt,hmove⟩ := c.original_exists_moving_neighbor eK geometry path.start_color hat
  by_cases hsmall : (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) ≤ 4
  · exact Or.inr ⟨haz,hza,hXa,hXz,d,hdt,
      c.original_moving_root_small_kernel eK geometry (by change 2 < geometry.b R; omega)
        path.start_color hat hdt hXa hmove hsmall⟩
  · exact Or.inl (c.original_backward_path_of_strict_mover eK geometry hb path hat hdt
      (Nat.lt_of_not_ge hsmall))

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
