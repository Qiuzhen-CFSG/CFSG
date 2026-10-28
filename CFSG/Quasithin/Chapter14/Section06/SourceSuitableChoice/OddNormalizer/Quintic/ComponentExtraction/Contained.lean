module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExtraction.RankNormal
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExtraction.Intersection
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExclusion.ContainedComparison.NaturalRowExclusion
import all CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExclusion.NaturalBorel
/-!
# The contained comparison on the actual extracted component

The first factor supplies an order-five element. The rank bound is therefore
an equality, and the independent normality argument in RankNormal makes J
normal in N_G(K₂). This constructs the literal C.2.7 input, puts the original
central involutions in J, and places O₂(J) in J ∩ Mc.

On the natural star row, the existing quotient and Borel markings now give
the terminal contradiction for this extracted J. This internal extension
intentionally imports the private involution lemma from NaturalBorel to
reuse its two-layer averaging proof without the EscapingComponent record.
No residual-centralizer identity is assumed or used here.

`exists_component_for_model_comparison` applies the entire argument to one
component produced by the actual second-normalizer extraction. The geometry,
row selection, residual identification, and outer comparison still belong to
qt-e-14615-quintic-exclusion. The earlier-source inputs in Context remain
with the final owner qt-e-suitable-odd-normalizer.

Source: Aschbacher--Smith 14.6.15, printed pp.1034--1035, and C.2.7(3)(a)(i),
printed pp.145--147.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExtraction
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExclusion.ContainedComparison Chapter1.RadicalExclusions
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
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
    (J : Subgroup G) (hJN : J ≤ normalizer (d.K2 : Set G))
    (hJ : (J.subgroupOf (normalizer (d.K2 : Set G))).IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J))
    (hf : generalizedFitting J = pCore 2 J)
    (hout : ¬J ≤ Mc ⊓ normalizer (d.K2 : Set G))
    (hfirst : d.K1 ≤ J)

include hJN hJ hq hout hfirst in
/-- In the contained branch the five-rank bound is attained by an original generator. -/
theorem component_quintic_rank_eq_one : primeRank 5 J = 1 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hr := component_quintic_rank s d J hJN hJ hq hout
  obtain ⟨k,hk,ho⟩ := exists_first_generator d
  have hd : 5 ∣ Nat.card J := by
    have he : orderOf (⟨k,hfirst hk⟩ : J) = 5 := (Subgroup.orderOf_coe _).symm.trans ho
    exact he ▸ orderOf_dvd_natCard (⟨k,hfirst hk⟩ : J)
  have hn : primeRank 5 J ≠ 0 := fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hd
  omega

include hJN hJ hq hout hfirst in
/-- The actual Q₁ normalizes the contained component, using the proved rank argument. -/
theorem contained_component_radical_normalizes :
    Mc.pCoreIn 2 ≤ normalizer (J : Set G) := by
  let := component_normal_of_quintic_rank_one s d J hJN hJ hq hout
    (component_quintic_rank_eq_one s d J hJN hJ hq hout hfirst)
  have hs := (source_secondNormalizer_setup s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action s.abelian H s.outside a H1 H2 s.critical d).2.2
  exact hs.radical_le.trans (le_normalizer_of_normal_subgroupOf hJN)

include hJN hJ hq hf hout hfirst in
/-- C.2.7 is applicable to the extracted component in the contained branch. -/
theorem contained_component_input :
    Input KnownSimple.IsKnownSimple (normalizer (d.K2 : Set G)) (Mc.pCoreIn 2)
      (Mc ⊓ normalizer (d.K2 : Set G)) J := by
  have hs := (source_secondNormalizer_setup s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action s.abelian H s.outside a H1 H2 s.critical d).2.2
  exact ⟨hs,⟨hJN,hJ⟩,hq,hf,hout,
    contained_component_radical_normalizes s d J hJN hJ hq hout hfirst⟩

include hJN hJ hq hout hfirst in
/-- The source Q₁-conjugate span reduces to J only after relative normality is proved. -/
theorem contained_component_span : conjugateSpanBy J (Mc.pCoreIn 2) = J :=
  le_antisymm (conjugateSpanBy_le le_rfl
    (contained_component_radical_normalizes s d J hJN hJ hq hout hfirst))
    (le_conjugateSpanBy _ _)

include hJN hJ hq hout hfirst in
/-- The original central involutions lie in the same component. -/
theorem contained_point_le_component : centralInvolutions T ≤ J := by
  apply s.factors.point_first.trans
  exact (commutator_mono (original_module_le_radical s)
    (d.residual_first_le.trans hfirst)).trans
      (le_normalizer_iff_commutator_le_right.mp
        (contained_component_radical_normalizes s d J hJN hJ hq hout hfirst))

include hJN hJ hq hf hout hfirst in
/-- The component's core lies in the literal intersection used by the model comparison. -/
theorem contained_component_core_le_intersection : pCore 2 J ≤ (J ⊓ Mc).subgroupOf J := by
  let := component_normal_of_quintic_rank_one s d J hJN hJ hq hout
    (component_quintic_rank_eq_one s d J hJN hJ hq hout hfirst)
  have hn := contained_component_radical_normalizes s d J hJN hJ hq hout hfirst
  have hQR := ChapterC.C27Source.source_joinCore_le_radical
    (contained_component_input s d J hJN hJ hq hf hout hfirst)
  have hJQ : J.pCoreIn 2 ≤ Mc.pCoreIn 2 :=
    (pCoreIn_mono_of_normalizes le_sup_left (sup_le J.le_normalizer hn)).trans hQR
  intro x hx
  exact ⟨x.property,pCoreIn_le 2 Mc (hJQ (mem_map_of_mem J.subtype hx))⟩

include hfirst in
private theorem five_dvd_contained_core_intersection :
    5 ∣ Nat.card (coreImage J (J ⊓ Mc)) := by
  obtain ⟨k,hk,ho⟩ := exists_first_generator d
  let kJ : J := ⟨k,hfirst hk⟩
  let π := QuotientGroup.mk' (pCore 2 J)
  have hπker : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hoJ : orderOf kJ = 5 := (Subgroup.orderOf_coe _).symm.trans ho
  have hoπ : orderOf (π kJ) = 5 := by
    rw [π.orderOf_map_eq_of_coprime_of_isPGroup_ker hπker _ (by rw [hoJ]; decide),hoJ]
  have hkB : π kJ ∈ coreImage J (J ⊓ Mc) :=
    mem_map_of_mem π ⟨hfirst hk,d.first_le hk⟩
  let x : coreImage J (J ⊓ Mc) := ⟨π kJ,hkB⟩
  have hx : orderOf x = 5 := (Subgroup.orderOf_coe _).symm.trans hoπ
  exact hx ▸ orderOf_dvd_natCard x

include hJN hJ hq hf hout hfirst in
/-- The natural C.2.7 row is impossible for the actual extracted component,
without assuming the residual-centralizer field of EscapingComponent. -/
theorem contained_component_false_of_natural_row
    (row : NaturalStarRow J (Mc.pCoreIn 2)) : False := by
  have hi := contained_component_input s d J hJN hJ hq hf hout hfirst
  obtain ⟨_,hb,_,hc⟩ := row.geometry hi
  have hBM : (Mc ⊓ normalizer (d.K2 : Set G)) ⊓ J = J ⊓ Mc := by
    ext x
    exact ⟨fun h => ⟨h.2,h.1.1⟩,fun h => ⟨⟨h.2,hJN h.1⟩,h.1⟩⟩
  have hcb (hc : ChapterC.IsChiZeroBlock J) :
      ∃ S : Sylow 2 (J ⧸ pCore 2 J),
        coreImage J (J ⊓ Mc) = normalizer (S : Set (J ⧸ pCore 2 J)) := by
    have hh := core_borel_of_chiZero hi hc hb
    rwa [hBM] at hh
  rcases hc with ⟨n,hn⟩ | ha
  · obtain ⟨b,_⟩ := exists_naturalBorelModel_of_block hn
      (contained_component_core_le_intersection s d J hJN hJ hq hf hout hfirst)
      (hcb (Or.inl ⟨n,hn⟩))
    have hZJ := contained_point_le_component s d J hJN hJ hq hout hfirst
    have hBZ : J ⊓ Mc ≤ centralizer (centralInvolutions T : Set G) :=
      inf_le_right.trans_eq (partner_eq_centralizer s)
    apply hout
    apply le_inf _ hJN
    apply le_trans _ (partner_eq_centralizer s).ge
    apply le_centralizer_iff.mpr
    intro z hz
    exact involution_centralizes_of_model hf b z
      (elemPow_eq_one_of_isElementaryAbelian z (a.kernel_le hz)) (hZJ hz)
      (le_centralizer_iff.mp hBZ hz)
  · obtain ⟨P,hP⟩ := hcb (Or.inr (Or.inr ha))
    obtain ⟨e⟩ := ha.2.2.quotient_iso
    exact Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_not_five_of_alternating_five
      e P (hP ▸ five_dvd_contained_core_intersection s d J hfirst)
/-- Extract one actual component, including relative normality when its
five-rank is one and the natural-row exclusion in the contained branch.
Every property below is proved from the original normalizer geometry. -/
theorem exists_component_for_model_comparison :
    ∃ J : Subgroup G, J ≤ normalizer (d.K2 : Set G) ∧
      (J.subgroupOf (normalizer (d.K2 : Set G))).IsCComponent ∧
      IsQuasisimple (J ⧸ pCore 2 J) ∧ generalizedFitting J = pCore 2 J ∧
      ¬J ≤ Mc ⊓ normalizer (d.K2 : Set G) ∧
      residualClosure H Mc ≤ normalizer (J : Set G) ∧
      J = ⁅J,d.K1⁆ ∧ ⁅J,d.K2⁆ ≤ J.pCoreIn 2 ∧ primeRank 5 J ≤ 1 ∧
      (primeRank 5 J = 1 → (J.subgroupOf (normalizer (d.K2 : Set G))).Normal) ∧
      (d.K1 ≤ J → Input KnownSimple.IsKnownSimple (normalizer (d.K2 : Set G))
        (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G)) J) ∧
      (d.K1 ≤ J → ¬Nonempty (NaturalStarRow J (Mc.pCoreIn 2))) ∧
      (conjugateSpanBy J (Mc.pCoreIn 2) ⊓ (Mc ⊓ normalizer (d.K2 : Set G)) ≤
        normalizer (d.K1 : Set G)) ∧
      (Chapter1.IsSylowIn 2 (Mc.pCoreIn 2 ⊓ J) J ∨
        Mc.pCoreIn 2 ≤ normalizer (J : Set G)) := by
  obtain ⟨J,hJN,hJ,hq,hf,hout,hn,_,hfirst,hsecond,hr,ha⟩ :=
    exists_component_with_rank s d
  exact ⟨J,hJN,hJ,hq,hf,hout,hn,hfirst,hsecond,hr,
    component_normal_of_quintic_rank_one s d J hJN hJ hq hout,
    contained_component_input s d J hJN hJ hq hf hout,
    fun h ⟨row⟩ => contained_component_false_of_natural_row s d J hJN hJ hq hf hout h row,
    span_intersection_normalizes_first s d J,ha⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExtraction
