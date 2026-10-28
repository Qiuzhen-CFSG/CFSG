module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.HallFaithfulness.PushingUpComponents
public import CFSG.Quasithin.ChapterC.Section04.NormalSeedAction
public import CFSG.Quasithin.ChapterC.Section04.A5LinearThreeNormality
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedG2Normality
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedLinearTwo
public import Theory.GroupTheory.NormalCentralQuotientAction.SolvableKernel

/-!
# No constrained component for the actual Mathieu residual

The original normal residual acts with solvable kernel inside the escaping
component's simple central core quotient. Its actual Mathieu quotient has
order divisible by eleven, excluding the finite C.2.7 star rows. In the
large linear, symplectic and G₂ rows, the action normalizes the nontrivial
image of the original radical intersection. The parabolic quotients have
binary SL₂ sections, whose elementary two-subgroups exclude the Mathieu
quotient with its elements of order four. The SL₂ star row is already
excluded by the source radical Sylow argument.

The chosen-module application constructs the epimorphism using the literal
inclusion-compatible residual quotient. Its solvable kernel retains both
the two-core and the central covering factor. No uniqueness or model
exclusion premise is added.

Source: Aschbacher--Smith, C.2.7, C.4.3--8, pp.145--147,152--154;
4.2.12--13, pp.610--612; 4.4.14, pp.624--625.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.ChapterC.HypothesisC28
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4.Section04.NormalizedRankOneOddControl
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q] [IsQuasisimple Q]
variable {H M L R V : Subgroup G}

omit [Finite G] in
private theorem intrinsic_intersection_ne_bot
    (K : Subgroup H) (R : Subgroup G)
    (hne : coreCentralIntersectionImage (K.map H.subtype) R ≠ ⊥) :
    coreCentralIntersectionImage K (R.subgroupOf H) ≠ ⊥ := by
  let e := K.equivMapOfInjective H.subtype H.subtype_injective
  intro hb
  apply hne
  apply eq_bot_iff.mpr
  rintro x ⟨k,hk,rfl⟩
  have hk' : e.symm k ∈ (R.subgroupOf H).subgroupOf K := by
    have hh := congrArg (fun a : K.map H.subtype => (a : G)) (e.apply_symm_apply k)
    change ((e.symm k : K) : H).val = (k : G) at hh
    change ((e.symm k : K) : H).val ∈ R
    rwa [hh]
  have hh : coreCentralProjection K (e.symm k) = 1 := by
    have hh := mem_map_of_mem (coreCentralProjection K) hk'
    change coreCentralProjection K (e.symm k) ∈ coreCentralIntersectionImage K (R.subgroupOf H) at hh
    rwa [hb,mem_bot] at hh
  have hm := congrArg (coreCentralQuotientCongr e) hh
  rw [coreCentralQuotientCongr_apply,e.apply_symm_apply,map_one] at hm
  exact hm

omit [Group G] [Finite G] [Group Q] [Finite Q] [IsQuasisimple Q] in
private theorem binary_five_eleven_free {E : Type*} [Field E] [Finite E]
    (hE : Nat.card E = 2) : ¬ 11 ∣ Nat.card PSL(5,E) := by
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := E) 5
  norm_num [hE,Fin.prod_univ_succ] at hc
  rw [hc]
  decide

/-- Every constrained escaping component is excluded for the normal original
Mathieu residual, with its actual central quotient epimorphism. -/
theorem no_constrained_mathieu_normal_seed
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (hn : (L.subgroupOf M).Normal)
    (hm : HasMathieuCentralQuotient Q)
    (q : L →* (Q ⧸ center Q)) (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    (K : Subgroup H) (hK : K.IsCComponent) (hqu : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K) : False := by
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let : Group.IsPerfect (Q ⧸ center Q) := Group.IsPerfect.ofSurjective
    (f := QuotientGroup.mk' (center Q)) (QuotientGroup.mk'_surjective _)
  let := h.component.perfect
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe h.component_le).toMonoidHom)
    (subgroupOfEquivOfLe h.component_le).surjective
  obtain ⟨r,hr,hrN⟩ := h.normal_seed_inner_action hn q hq K hK hqu hout
  let := hr
  have hS := Group.IsPerfect.not_isSolvable (Q ⧸ center Q)
  have hexp := mathieu_centralQuotient_not_two_exponent hm
  have hd : 11 ∣ Nat.card (coreCentralQuotient K) :=
    (mathieu_centralQuotient_eleven_dvd hm).trans
      (SimpleSection.card_dvd_of_solvable_representation hS q hq r)
  let s := h.constrained_source_input K hK hqu hout hfK
  have hds : 11 ∣ Nat.card (starImage (K.map H.subtype) R (K.map H.subtype)) := by
    rw [Nat.card_congr (h.constrained_star_central_equiv K hK hqu hout hfK).toEquiv] at hd
    exact hd.trans (card_dvd_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _))
  have hrP := coreCentralIntersectionImage_isPGroup K (R.subgroupOf H) h.isRadical.isPGroup
  have transport {D : Type} [Group D] (e : coreCentralQuotient K ≃* D) :
      Group.IsSolvable (e.toMonoidHom.comp r).ker ∧
        (e.toMonoidHom.comp r).range ≤ normalizer
          ((coreCentralIntersectionImage K (R.subgroupOf H)).map e.toMonoidHom : Set D) := by
    constructor
    · rw [MonoidHom.ker_comp_of_injective _ _ e.injective]; exact hr
    · rw [MonoidHom.range_comp]
      exact (map_mono hrN).trans ((coreCentralIntersectionImage K (R.subgroupOf H)).le_normalizer_map e.toMonoidHom)
  cases ChapterC.C27Source.star_model_from_source s with
  | linearTwo F e =>
    exact h.no_constrained_component_star_linear_two K hK hqu hout hfK F e
  | linearThree F e =>
    by_cases hb : 1 < F.degree
    · have hF : 4 ≤ Nat.card F.Carrier := by
        rw [F.card_eq]; exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hb
      let ec := h.constrained_linear_three_simple_equiv K hK hqu hout hfK e
      have hpne := intrinsic_intersection_ne_bot K R
        (Section04Constrained.source_linear_three_intersection_ne_bot s e hF)
      obtain ⟨hr',hn'⟩ := transport ec
      let := hr'
      exact no_linear_three_local hS hexp q hq hb F.card_eq _ (hrP.map ec.toMonoidHom)
        (fun he => hpne ((Subgroup.map_eq_bot_iff_of_injective _ ec.injective).mp he))
        (ec.toMonoidHom.comp r) hn'
    · have hdF : F.degree = 1 := by have hp := F.degree_pos; omega
      rw [Nat.card_congr (h.constrained_linear_three_simple_equiv K hK hqu hout hfK e).toEquiv,
        Matrix.PSL3.LinearThree.card_projective,F.card_eq,hdF] at hd
      norm_num at hd
  | symplectic F hb e =>
    have hF : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]; exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hb
    let ec := h.constrained_symplectic_simple_equiv K hK hqu hout hfK e
    have hpne := intrinsic_intersection_ne_bot K R
      (Section04Constrained.source_symplectic_intersection_ne_bot s e hF)
    obtain ⟨hr',hn'⟩ := transport ec
    let := hr'
    exact no_symplectic_four_local hS hexp q hq _ (hrP.map ec.toMonoidHom)
      (fun he => hpne ((Subgroup.map_eq_bot_iff_of_injective _ ec.injective).mp he))
      (ec.toMonoidHom.comp r) hn'
  | g2 F hb e =>
    have hF : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]; exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hb
    let ec := h.constrained_g2_simple_equiv K hK hqu hout hfK e hF
    have hpne := intrinsic_intersection_ne_bot K R
      (Section04Constrained.source_g2_intersection_ne_bot s e hF)
    obtain ⟨hr',hn'⟩ := transport ec
    let := hr'
    exact no_g2_local hS hexp q hq (by omega : 2 < Nat.card F.Carrier) _ (hrP.map ec.toMonoidHom)
      (fun he => hpne ((Subgroup.map_eq_bot_iff_of_injective _ ec.injective).mp he))
      (ec.toMonoidHom.comp r) hn'
  | g2DerivedTwo e =>
    rw [Nat.card_congr e.toEquiv] at hds
    have hd' := hds.trans (commutator (Atlas.G2.Model (ZMod 2))).card_subgroup_dvd_card
    rw [Atlas.G2.card_Model,Nat.card_zmod] at hd'
    norm_num at hd'
  | alternating n hn e =>
    rw [Nat.card_congr e.toEquiv] at hds
    rcases hn with rfl | rfl | rfl | rfl <;>
      rw [nat_card_alternatingGroup] at hds <;> norm_num [Nat.factorial] at hds
  | linearFiveTwo e =>
    let ec := (h.constrained_star_central_equiv K hK hqu hout hfK).trans
      (QuotientGroup.congr _ _ e (FixedElementary.map_center e))
    rw [Nat.card_congr ec.toEquiv] at hd
    exact binary_five_eleven_free (by simp : Nat.card (ZMod 2) = 2) hd
  | tripleSix hc e =>
    rw [Nat.card_congr ((h.constrained_star_central_equiv K hK hqu hout hfK).trans e).toEquiv,
      nat_card_alternatingGroup] at hd
    norm_num [Nat.factorial] at hd

end CFSG.Quasithin.ChapterC.HypothesisC28

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter7.NormalizedSource Chapter7.NormalizedSource.MathieuGeneration
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal intersection residual discharges the normal-seed and solvable
kernel hypotheses of the constrained exclusion. -/
theorem sourceOrbit_mathieu_no_constrained_pushingUp
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hm : HasMathieuCentralQuotient D.orbitComponent)
    {A J H W : Subgroup G} (hw : Witness L V A J H W)
    (K : Subgroup H) (hK : K.IsCComponent) (hqu : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) : False := by
  rcases hw with ⟨hJ,hpush,hH,hJH,hstrict,hVJ,hc,hcover,hN,hmove,hVF,⟨e,he⟩,hrest⟩
  let F := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let : Finite D.orbitComponent :=
    Finite.of_surjective D.orbitComponentHom D.orbitComponentHom_surjective
  let := D.orbitComponent_quasisimple h
  let a := (centerQuotientCongr e).trans (D.orbitCentralQuotientEquiv h)
  let q : F →* (D.orbitComponent ⧸ center D.orbitComponent) :=
    a.toMonoidHom.comp (coreCentralProjection F)
  have hq : Function.Surjective q := a.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  let : Group.IsSolvable q.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ a.injective]
    rw [coreCentralProjection,←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact centralPreimage_pCore_isSolvable (G := F) 2
  exact hc.no_constrained_mathieu_normal_seed hN hm q hq K hK hqu hout hfK

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
