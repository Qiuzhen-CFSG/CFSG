module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSmallCommutator
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticKernelNormalization
/-!
# The original selected kernel has small centralizer index

The previously proved root commutator has order four. The natural module
at the neighboring vertex now turns this into the literal bound
[Z_d : C_(Z_d)(Z_z intersect Q_a)] at most four, including the original
ambient field action and its full central kernel.

The same root lies in Z_d intersect Z_a, bounding the neighboring join
modulo Z_a by 64. The proved endpoint normalization and this small-section
bound put the selected kernel in B_a when the other original generator
normalizes it. This yields the actual overlapping backward critical path
from source generation and a strict moving index. Those selected-generator
and strict-index premises remain explicit: neither the large-distance nor
the distance-four exclusion, and hence SymplecticPlaneRecognition, is claimed.

Source: MS93 (3.3)(ii), (5.7), printed pp.867 and919;
Aschbacher--Smith 9.3.10, p.734.
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

/-- The selected neighboring seed has centralizer index at most four for
the original critical hyperplane. -/
theorem original_neighbor_kernel_centralizer_index
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
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
    exact (c.original_neighbor_kernel_commutator eK geometry hb path hat hdt hcontained hbad).2.le
  rw [c.original_Z_eq_U d hd]
  exact original_small_commutator_centralizer_index R hms hodd.isPGroup hne hodd.twoCore_le
    hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq hd hfixed A hAD hsmall

/-- The selected-pair source (5.7) kernel comparison now requires only its
other generating subgroup's normalization and generation. -/
theorem original_neighbor_moving_index_le_four_of_generator
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) →
      ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      ∀ J : Subgroup (FreeAmalgam R),
      Ltilde R a ≤ J ⊔ Z R z →
      J ≤ normalizer (((Z R d ⊓ centralizer
        ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _)) ⊔ Z R a :
          Subgroup (FreeAmalgam R)) : Set _) →
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) ≤ 4 := by
  intro R geometry hb a z d t path hat hdt hcontained hbad J hgen hJ
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
  obtain ⟨π,hπ,hπker⟩ := local_residual_projection R hodd.isPGroup hodd.twoCore_le
    q (QuotientGroup.ker_mk' _) path.start_color
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [path.start_color] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  have hV := ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt
  let Y := Z R d ⊔ Z R a
  let H := (Z R d ⊓ centralizer ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _)) ⊔ Z R a
  have hHY : H ≤ Y := sup_le_sup inf_le_left le_rfl
  have hYGa : Y ≤ stabilizer R a := hV.trans
    ((geometry.V_le_Q (by omega) a path.start_color).trans (fun _ hx => hx.1))
  let := finite_stabilizer R a
  let : Finite Y := Finite.of_injective (inclusion hYGa) (inclusion_injective _)
  let := finite_Z R d
  let := finite_Z R a
  let : Finite (Z R d ⊓ Z R a : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hroot := c.original_neighbor_kernel_commutator eK geometry hb path hat hdt hcontained hbad
  have hrootD : ⁅Z R a,Z R z⁆ ≤ Z R d := by
    rw [←hroot.1]
    have ht : color R t = true := by
      have h := adjacent_color_ne R hat
      rw [path.start_color] at h
      cases he : color R t <;> simp_all
    exact le_normalizer_iff_commutator_le_left.mp
      (((inf_le_right.trans (Q_le_adjacent_h R ht hat)).trans
        (show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt))).trans
          (Z_normalized R d))
  have hfour : 4 ≤ Nat.card (Z R d ⊓ Z R a : Subgroup (FreeAmalgam R)) := by
    have h := Nat.card_le_card_of_injective
      (inclusion (le_inf hrootD (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path)))
      (inclusion_injective _)
    rw [←hroot.1,hroot.2] at h
    exact h
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R))
    (Z R d ⊓ Z R a) (Z R d) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left] at hmul
  have hZd := c.original_Z_card eK d hd
  change Nat.card (Z R d) = 256 at hZd
  rw [hZd] at hmul
  have hindexD : (Z R a).relIndex (Z R d) ≤ 64 := by nlinarith
  have hn : Z R a ≤ normalizer (Z R d : Set (FreeAmalgam R)) :=
    (((Z_le_VBall R a 2).trans
      (le_centralizer_iff_isMulCommutative.mpr (V_abelian_of_four_lt R path.start_color hb))).trans
      (Subgroup.centralizer_le (show Z R d ≤ V R a from le_sup_left.trans hV))).trans (Subgroup.centralizer_le_normalizer _)
  have hindex : (Z R a).relIndex H ≤ 64 :=
    (relIndex_le_of_le_right hHY index_ne_zero_of_finite).trans
      ((relIndex_sup_of_normalizes (Z R d) (Z R a) hn).trans_le hindexD)
  have hE := (c.original_neighbor_hyperplane_centralizer eK geometry hb path hat hdt hcontained hbad).2
  have hH := ChapterC.Sp4Four.DistanceReduction.small_residual_radius_le_B geometry
    (by omega) path.start_color π hπ hπker (by rw [hcard]; decide)
    (Q_isPGroup R hodd.isPGroup hodd.twoCore_le a path.start_color)
    H (hHY.trans hV) (hgen.trans (sup_le hJ hE)) hindex
  have hker := le_sup_left.trans hH
  exact ChapterC.Sp4Four.DistanceReduction.movingIndex_le_of_centralizer_kernel geometry
    (Z R z ⊓ Q R a) hker
    (c.original_neighbor_kernel_centralizer_index eK geometry hb path hat hdt hcontained hbad)

/-- The original selected generator and strict moving index give the
backward critical path; the root centralizer index and endpoint normalization
are discharged by the preceding source calculations. -/
theorem original_selected_generator_backward_path
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      ∀ J : Subgroup (FreeAmalgam R),
      Ltilde R a ≤ J ⊔ Z R z →
      (Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) →
        J ≤ normalizer (((Z R d ⊓ centralizer
          ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _)) ⊔ Z R a :
            Subgroup (FreeAmalgam R)) : Set _)) →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      (∃ back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1=t ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
      ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  intro R geometry hb a z d t path hat hdt hbad J hgen hJ hmove
  have hn : ¬ Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
    intro h
    have hi := c.original_neighbor_moving_index_le_four_of_generator eK geometry hb path hat hdt
      h hbad J hgen (hJ h)
    change (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) ≤ 4 at hi
    exact (not_le_of_gt hmove) hi
  exact ⟨ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
    geometry (by omega) path hat hdt hn,
    fun h => hn ((le_sup_left.trans
      (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)).trans h)⟩
end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
