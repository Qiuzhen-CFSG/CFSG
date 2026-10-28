module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.StarComparison
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.Commutator.RelativeGeneration
import all CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExclusion.NaturalBorel

/-!
# The natural-row contradiction under the joined inner-action conclusion

The literal action kernel proves K₁ ≤ J K₂ for the inner branch. This
weaker placement suffices here: the first support centralizes K₂, and
coprime commutator idempotence puts the original central involutions in J.
The surviving first-factor action also forces five-divisibility of the
literal core intersection. The natural C.2.7 row therefore gives the same
Borel and centralizer contradiction as the contained argument.

This internal extension deliberately imports NaturalBorel's private
involution lemma to reuse its two-layer averaging argument. No legacy
ordinary-centralizer residual identity is assumed. The final owner
qt-e-14615-quintic-exclusion still constructs NormalizerGeometry, selects
the source row and excludes the genuine outer five-action. The independent
earlier-source inputs retain discharge with qt-e-suitable-odd-normalizer.

Source: Aschbacher--Smith 14.6.15, printed p.1035, and C.2.7(3)(a)(i),
printed pp.145--147.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped commutatorElement Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExtraction ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (j : SourceEscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))

include s in
/-- The original residual commutator lies in the actual first support. -/
theorem source_first_residual_commutator_le_support :
    ⁅conjugateSpanBy (localModule T M) H,residual H1⁆ ≤ firstSupport a H1 := by
  have hz := (source_rankTwo_f9_hypothesis s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action s.abelian H s.outside).H_centralizes
  let c := ModuleBound.OriginalF916.conjugationSection a hz
  rw [commutator_comm]
  apply commutator_le.mpr
  intro b hb u hu
  have hbH : b ∈ H := s.factors.zero_le (s.factors.first_le ((residual_le H1) hb))
  let bH : H := ⟨b,hbH⟩
  let uU : conjugateSpanBy (localModule T M) H := ⟨u,hu⟩
  apply (mem_supportPreimage a _ ⟨⁅b,u⁆,c.commutator_mem bH uU⟩).mpr
  change (c.quotient ⟨⁅b,u⁆,c.commutator_mem bH uU⟩).toAdd ∈ _
  rw [←c.displacement bH uU]
  exact Submodule.subset_span ⟨QuotientGroup.mk' (pCore 2 H) bH,
    mem_map_of_mem _ ((residual_le H1) hb),
    (c.quotient uU).toAdd,Submodule.mem_top,rfl⟩

/-- The source central point lies in J already under K₁ ≤ J K₂.
Coprime commutator idempotence removes the possible K₂ contribution,
since the first support centralizes K₂. -/
theorem source_point_le_component_of_first_le_join
    (hr : primeRank 5 j.J = 1) (hfirst : d.K1 ≤ j.J ⊔ d.K2) :
    centralInvolutions T ≤ j.J := by
  let W := firstSupport a H1
  let U := conjugateSpanBy (localModule T M) H
  let B := residual H1
  have hi := source_component_rank_one_input s d j hr
  have hWN : W ≤ normalizer (j.J : Set G) :=
    (supportPreimage_le a _).trans ((original_module_le_radical s).trans hi.normalizes)
  have hK2N : d.K2 ≤ normalizer (j.J : Set G) :=
    (show d.K2 ≤ residualClosure H Mc from d.join_eq ▸ le_sup_right).trans
      j.normalized_by_closure
  have hW2 : ⁅d.K2,W⁆ ≤ j.J := by
    have he : ⁅d.K2,W⁆ = ⊥ := by
      rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
      exact d.first_support_le.trans d.first_centralizes
    rw [he]
    exact bot_le
  have hjoin : ⁅j.J ⊔ d.K2,W⁆ ≤ j.J :=
    commutator_sup_le_of_relative_normal (normalizer (j.J : Set G)) j.J d.K2 W j.J
      le_rfl j.J.le_normalizer hK2N
      (le_normalizer_iff_commutator_le_left.mp hWN) hW2
  have hW1 : ⁅W,d.K1⁆ ≤ j.J := by
    rw [commutator_comm]
    exact (commutator_mono hfirst le_rfl).trans hjoin
  have hBU : B ≤ normalizer (U : Set G) :=
    (residual_le H1).trans ((s.factors.first_le.trans s.factors.zero_le).trans a.normalizes)
  have he : ⁅⁅U,B⁆,B⁆ = ⁅U,B⁆ :=
    commutator_isPPerfect_idempotent B U (isPPerfect_embedded_pResidual 2 H1)
      (IsElementaryAbelian.isPGroup 2 U) hBU
  apply s.factors.point_first.trans
  rw [←he]
  exact (commutator_mono (source_first_residual_commutator_le_support s)
    d.residual_first_le).trans hW1

/-- The first generator yields five-divisibility of the literal core
intersection even when only K₁ ≤ J K₂ is known. -/
theorem source_five_dvd_core_intersection_of_first_le_join
    (hfirst : d.K1 ≤ j.J ⊔ d.K2) :
    5 ∣ Nat.card (coreImage j.J (j.J ⊓ Mc)) := by
  obtain ⟨k,hk,ho,ha⟩ := exists_first_generator_with_quotient_order s d j.J
    j.component_le j.component j.quasisimple j.outside
  have hprod : (k : G) ∈ (j.J : Set G) * (d.K2 : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right j.J d.K2 j.component_le]
    exact hfirst hk
  obtain ⟨y,hy,z,hz,he⟩ := hprod
  have hK2N : d.K2 ≤ normalizer (j.J : Set G) :=
    (show d.K2 ≤ residualClosure H Mc from d.join_eq ▸ le_sup_right).trans
      j.normalized_by_closure
  let yN : normalizer (j.J : Set G) := ⟨y,j.J.le_normalizer hy⟩
  let zN : normalizer (j.J : Set G) := ⟨z,hK2N hz⟩
  have hz0 : pCoreNormalizerAction 2 j.J zN = 1 := by
    have hd := second_factor_le_component_quotient_kernel s d j.J
      j.component_le j.component j.quasisimple j.outside hz
    obtain ⟨z',hz',he'⟩ := hd.2
    have hez : z' = zN := Subtype.ext he'
    exact hez ▸ hz'
  let π := QuotientGroup.mk' (pCore 2 j.J)
  let yJ : j.J := ⟨y,hy⟩
  have hact : pCoreNormalizerAction 2 j.J k = MulAut.conj (π yJ) := by
    have hek : k = yN * zN := Subtype.ext he.symm
    rw [hek,map_mul,hz0,mul_one]
    exact pCoreNormalizerAction_on_component 2 j.J yJ
  have hyMc : y ∈ Mc := by
    have he' : y = (k : G) * z⁻¹ := (eq_mul_inv_iff_mul_eq).mpr he
    rw [he']
    exact Mc.mul_mem (d.first_le hk) (Mc.inv_mem (d.second_le hz))
  have him : π yJ ∈ coreImage j.J (j.J ⊓ Mc) := mem_map_of_mem π ⟨hy,hyMc⟩
  have hd : 5 ∣ orderOf (π yJ) := by
    rw [hact] at ha
    exact ha ▸ orderOf_map_dvd (MulAut.conj : (j.J ⧸ pCore 2 j.J) →* _) (π yJ)
  have hcard := orderOf_dvd_natCard (⟨π yJ,him⟩ : coreImage j.J (j.J ⊓ Mc))
  rw [←Subgroup.orderOf_coe] at hcard
  exact hd.trans hcard

/-- At rank one the original core lies in the literal intersection,
independently of whether K₁ is contained in J. -/
theorem source_component_core_le_intersection_of_rank_one
    (hr : primeRank 5 j.J = 1) : pCore 2 j.J ≤ (j.J ⊓ Mc).subgroupOf j.J := by
  let := j.rank_one_normal hr
  have hi := source_component_rank_one_input s d j hr
  have hQR := ChapterC.C27Source.source_joinCore_le_radical hi
  have hJQ : j.J.pCoreIn 2 ≤ Mc.pCoreIn 2 :=
    (pCoreIn_mono_of_normalizes le_sup_left (sup_le j.J.le_normalizer hi.normalizes)).trans hQR
  intro x hx
  exact ⟨x.property,pCoreIn_le 2 Mc (hJQ (mem_map_of_mem j.J.subtype hx))⟩

/-- The natural-row contradiction needs only the proved inner-action
placement K₁ ≤ J K₂. The original central point still lies in J by the
first-support calculation, and a first generator survives in the core Borel. -/
theorem source_false_of_natural_row_of_first_le_join
    (hr : primeRank 5 j.J = 1) (hfirst : d.K1 ≤ j.J ⊔ d.K2)
    (row : NaturalStarRow j.J (Mc.pCoreIn 2)) : False := by
  have hi := source_component_rank_one_input s d j hr
  obtain ⟨_,hb,_,hc⟩ := row.geometry hi
  have hBM : (Mc ⊓ normalizer (d.K2 : Set G)) ⊓ j.J = j.J ⊓ Mc := by
    ext x
    exact ⟨fun h => ⟨h.2,h.1.1⟩,fun h => ⟨⟨h.2,j.component_le h.1⟩,h.1⟩⟩
  have hcb (hc : ChapterC.IsChiZeroBlock j.J) :
      ∃ S : Sylow 2 (j.J ⧸ pCore 2 j.J),
        coreImage j.J (j.J ⊓ Mc) = normalizer (S : Set (j.J ⧸ pCore 2 j.J)) := by
    have hh := core_borel_of_chiZero hi hc hb
    rwa [hBM] at hh
  rcases hc with ⟨n,hn⟩ | ha
  · obtain ⟨b,_⟩ := exists_naturalBorelModel_of_block hn
      (source_component_core_le_intersection_of_rank_one s d j hr)
      (hcb (Or.inl ⟨n,hn⟩))
    have hZJ := source_point_le_component_of_first_le_join s d j hr hfirst
    have hBZ : j.J ⊓ Mc ≤ centralizer (centralInvolutions T : Set G) :=
      inf_le_right.trans_eq (partner_eq_centralizer s)
    apply j.outside
    apply le_inf _ j.component_le
    apply le_trans _ (partner_eq_centralizer s).ge
    apply le_centralizer_iff.mpr
    intro z hz
    exact involution_centralizes_of_model j.characteristic_component b z
      (elemPow_eq_one_of_isElementaryAbelian z (a.kernel_le hz)) (hZJ hz)
      (le_centralizer_iff.mp hBZ hz)
  · obtain ⟨P,hP⟩ := hcb (Or.inr (Or.inr ha))
    obtain ⟨e⟩ := ha.2.2.quotient_iso
    exact Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_not_five_of_alternating_five
      e P (hP ▸ source_five_dvd_core_intersection_of_first_le_join s d j hfirst)

/-- The natural row is excluded by the actual star outer-group calculation,
without any ordinary-centralizer identity or a K₁ ≤ J callback. -/
theorem source_false_of_natural_row_of_star_outer_card
    (hn : Mc.pCoreIn 2 ≤ normalizer (j.J : Set G))
    (ho : ¬5 ∣ Nat.card (MulAut.Outer (starImage j.J (Mc.pCoreIn 2) j.J)))
    (row : NaturalStarRow j.J (Mc.pCoreIn 2)) : False := by
  obtain ⟨hr,hfirst⟩ := source_component_first_le_join_of_star_outer_card s d j hn ho
  exact source_false_of_natural_row_of_first_le_join s d j hr hfirst row

/-- On the natural row, the surviving rank-one branch has a genuine
outer five-actor. The joined inner branch is discharged above. -/
theorem source_natural_row_outer_quintic
    (hr : primeRank 5 j.J = 1) (row : NaturalStarRow j.J (Mc.pCoreIn 2)) :
    ∃ k : (normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G) : Subgroup G),
      (k : G) ∈ d.K1 ∧ (k : G) ∉ j.J ⊔ d.K2 ∧ orderOf k = 5 ∧
      orderOf (starComponentAction j.J (Mc.pCoreIn 2) k) = 5 ∧
      starComponentAction j.J (Mc.pCoreIn 2) k ∉
        MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J) ∧
      orderOf (QuotientGroup.mk' (MulAut.innerSubgroup (starImage j.J (Mc.pCoreIn 2) j.J))
        (starComponentAction j.J (Mc.pCoreIn 2) k)) = 5 := by
  rcases source_component_rank_one_first_join_or_star_outer s d j hr with hfirst | ho
  · exact (source_false_of_natural_row_of_first_le_join s d j hr hfirst row).elim
  · exact ho

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
