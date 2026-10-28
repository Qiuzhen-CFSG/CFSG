module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.Canonical

/-!
# The actual candidate maximal two-local and its common action

The completed radical geometry supplies the canonical faithfulness, two-core,
and PSL₂ quotient on the literal candidate. The escape theorem then produces
one Y and all common-action conclusions on its K and D, including the original
multiplication map and the binary fixed-codimension bound.

The controlled Thompson index is still explicit. Its construction and the
chief-section FF contradiction remain in qt-d-1319-ff-contradiction; the earlier
canonical stars and source premises belong to qt-d-1317-supplements and
qt-d-1317-source. This is not the final source contradiction.
Source: Aschbacher--Smith 13.1.9, printed pp.870--871.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin ChapterB
open Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterA.Section04 Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Properties of the same centralizer quotient and its original conjugation
representation. Each clause is constructed in `candidate_common_action`. -/
structure CommonActionProperties (T L Y : Subgroup G) (j : ℕ)
    [(commonModule T L Y j).Normal]
    [IsElementaryAbelian 2 (commonModule T L Y j)] : Prop where
  faithful : Function.Injective (hatRepresentation T L Y j)
  canonical_nontrivial : hatImage T L Y j (canonicalSupplement T L) ≠ ⊥
  commutator_nontrivial : hatImage T L Y j (thompsonCommutator T L Y j) ≠ ⊥
  commute : ⁅hatImage T L Y j (canonicalSupplement T L),
    hatImage T L Y j (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L)⁆ = ⊥
  generate : hatImage T L Y j (canonicalSupplement T L) ⊔
    hatImage T L Y j (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L) = ⊤
  second_core : pCore 2 (hatImage T L Y j
    (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L)) = ⊥
  radical_faithful : HatRadicalFaithful T L Y j
  product : ∃ e : hatImage T L Y j (canonicalSupplement T L) ×
      hatImage T L Y j (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L) ≃*
        HatGroup T L Y j,
    ∀ a b, e (a,b) = (a : HatGroup T L Y j) * (b : HatGroup T L Y j)
  canonical_model : ∃ p : ℕ, p.Prime ∧ 3 < p ∧
    ClassicalGroup.IsPSL (hatImage T L Y j (canonicalSupplement T L)) 2 p
  actor_bound : ∀ A ∈ thompsonFamily (radicalSylowCentralizer T L) j,
    hatImage T L Y j A ≠ ⊥ → HatActorBound T L Y A j

/-- The literal outside maximal two-local supplies the common quotient action
and its rank bound. The canonical radical facts are discharged by their source
theorems. The controlled Thompson index remains with the FF-contradiction owner. -/
theorem candidate_common_action (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hs : CanonicalStars T) (hrig : QuasisimpleRigidity T)
    (hclass : QuasisimpleClassification T) {L H C : Subgroup G}
    (hL : FaithfulMaximalLocal T L) (hn : ¬ IsQuasisimple (XiQuotient L))
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hne : H ≠ normalizer (L : Set G))
    (hC : C ∈ cComponentsIn H) (hAC : canonicalSupplement T L ≤ C)
    {j : ℕ}
    (hN : normalizer (thompsonJ (radicalSylowCentralizer T L) j : Set G) ≤
      normalizer (L : Set G)) :
    ∃ Y : Subgroup G, RefinedWitness T L H C Y ∧
      ⁅⁅omegaClosure T L Y j,canonicalSupplement T L⁆,thompsonCommutator T L Y j⁆ ≠ ⊥ ∧
      ∃ n : (commonModule T L Y j).Normal,
        letI := n
        ∃ e : IsElementaryAbelian 2 (commonModule T L Y j),
        letI := e
        CommonActionProperties (T : Subgroup G) L Y j := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  have hcan := canonical_frattini_geometry h hmany hL hn
  have hTA := sylow_normalizes_canonicalSupplement hTL
  have hcent := supplement_radicalSylowCentralizer hTL hTA
    (maximal_nonquasisimple_normalizer_action_source h hmany hL hn).1 hcan.1.2
  obtain ⟨p,_,_,hmodel⟩ := canonical_twoCore_quotient h hmany hL hn
  obtain ⟨Y,w⟩ := exists_refined_witness h hmany hs hrig hclass hL hn hH hTH hne
    (canonical_mem_faithfulLocalComponents h hmany hL hn) hC hAC hTA hcan.2.1 hcent hmodel
  have hAH := hAC.trans hC.1
  have hZ := (nonquasisimple_centralizer_unique_of_stars h hmany hs hL hn).2.1
  have hD : omegaClosure T L Y j ≤ commonGroup T L Y j :=
    (omegaClosure_geometry w hTH hAH hTL j).2.1.trans le_sup_right
  have hnormal := commonModule_normal w hTH hAH hTL j
  refine ⟨Y,w,omegaClosure_double_movement h hmany hs hL hn w hH hTH hAH hTL hN,
    hnormal,?_⟩
  let := hnormal
  have helementary := commonModule_elementary h w hH hTH hAH hTL hcan.2.1 j
  refine ⟨helementary,?_⟩
  let := helementary
  refine ⟨hatRepresentation_injective (T : Subgroup G) L Y j,?_,?_,hat_images_commute h w hH hTH hAH hAC hTL hcan.2.1 j,
    hat_images_generate (T : Subgroup G) L Y j,
    hat_second_factor_twoCore h w hH hTH hAH hTL hcan.2.1 j,
    hat_radical_faithful_on_commutator h w hH hTH hAH hTL hcan.2.1 j,
    hat_direct_product h hmany hL hn w hH hTH hAH hAC hTL j,
    canonical_hat_model h hmany hL hn w hTH hAH hTL j,?_⟩
  · intro he
    exact omegaClosure_moved_by_canonical h hmany hL hn w hTH hAH hTL j
      ((hat_image_eq_bot_iff (T : Subgroup G) L Y _ j hD le_sup_left).mp he)
  · intro he
    exact omegaClosure_moved_by_K h w hH hTH hAH hTL hcan.2.1 hN hZ
      ((hat_image_eq_bot_iff (T : Subgroup G) L Y _ j hD (le_sup_left.trans le_sup_right)).mp he)
  · intro A hA hneA
    exact hat_actor_rank_bound h w hH hTH hAH hTL hcan.2.1 hA hneA

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
