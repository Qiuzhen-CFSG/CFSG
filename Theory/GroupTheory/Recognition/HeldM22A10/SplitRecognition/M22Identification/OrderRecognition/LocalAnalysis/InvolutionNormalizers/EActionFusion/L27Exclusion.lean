module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.Interfaces
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.Nonfusion
public import Theory.SpecificGroups.SymmetricFive.ThreeCentralizer
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.NormalizerAction
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.CentralizerFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.IntersectionData
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.ActorFusion
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.L27Exclusion.IntersectionConstruction

/-!
# Excluding Janko's order-168 branch

An order-three element of N(F) has a nontrivial order-three image in N(F)/F,
since |F| = 16. If its fixed subgroup on E has order four and meets F
trivially, that four-group embeds in the centralizer of the quotient image.
The centralizer has order six in S5, contradicting Lagrange's theorem.

The final assembly constructs this intersection witness from the numerical
order-168 premise. Actor fusion follows from that same premise and the
given fusion of printed z₁ with z₃, so the supplied F-normalizer implication
provides the actual S5 quotient. Every intermediate premise is discharged;
no recognition of the order-168 quotient or global splitting is assumed.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, Lemma 6, pp.6–7.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification
open LocalModelDichotomy

private theorem quotient_centralizer_card_dvd_six {A : Type*} [Group A]
    (R B : Subgroup A) [R.Normal] (hR : ¬ 3 ∣ Nat.card R)
    (q : A) (hq : orderOf q = 3) (hB : Disjoint B R)
    (hcomm : B ≤ centralizer ({q} : Set A))
    (e : A ⧸ R ≃* Equiv.Perm (Fin 5)) : Nat.card B ∣ 6 := by
  let f : A →* Equiv.Perm (Fin 5) := e.toMonoidHom.comp (QuotientGroup.mk' R)
  have hfq : orderOf (f q) = 3 := by
    apply orderOf_eq_prime
    · rw [← map_pow, (orderOf_eq_prime_iff.mp hq).1, map_one]
    · intro h
      have hqR : q ∈ R := (QuotientGroup.eq_one_iff q).mp (e.injective (by
        simpa [f] using h))
      exact hR (hq ▸ R.orderOf_dvd_natCard hqR)
  let g : B →* Equiv.Perm (Fin 5) := f.comp B.subtype
  have hg : Function.Injective g := by
    apply (injective_iff_map_eq_one g).mpr
    intro b hb
    have hbR : (b : A) ∈ R := (QuotientGroup.eq_one_iff (b : A)).mp (e.injective (by
      simpa [f, g] using hb))
    exact Subtype.ext (Subgroup.disjoint_def.mp hB b.property hbR)
  apply Theory.SpecificGroups.SymmetricFive.card_dvd_six_of_centralizes_three (f q) hfq g hg
  intro b
  simpa only [map_mul, g, MonoidHom.comp_apply, Subgroup.subtype_apply] using congrArg f (mem_centralizer_singleton_iff.mp (hcomm b.property))

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (k : TwistedModel ≃* D.centralizer)

/-- The fixed four-group cannot occur when the actual F-normalizer quotient is S5. -/
public theorem l27_intersection_contradiction
    (hF : FNormalizerAction D k) (w : L27IntersectionWitness D k) : False := by
  let N := normalizer (CaseII.F D k : Set G)
  let R := (CaseII.F D k).subgroupOf N
  let B := CaseII.E D k ⊓ centralizer ({w.actor} : Set G)
  have hEN : CaseII.E D k ≤ N :=
    (CaseII.E_le_caseIISylow D k).trans (CaseII.caseIISylow_le_normalizer_F D k)
  have hBN : B ≤ N := inf_le_left.trans hEN
  have hRcard : Nat.card R = 16 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (CaseII.F D k).le_normalizer).toEquiv,
      CaseII.F_card]
  let q : N := ⟨w.actor, w.normalizes_F⟩
  have hq : orderOf q = 3 := by
    exact (orderOf_injective N.subtype Subtype.val_injective q).symm.trans w.actor_order
  have hdis : Disjoint (B.subgroupOf N) R := by
    apply Subgroup.disjoint_def.mpr
    intro x hx hxR
    exact Subtype.ext (Subgroup.disjoint_def.mp w.fixed_disjoint hx hxR)
  have hcomm : B.subgroupOf N ≤ centralizer ({q} : Set N) := by
    intro x hx
    apply mem_centralizer_singleton_iff.mpr
    exact Subtype.ext (mem_centralizer_singleton_iff.mp hx.2)
  obtain ⟨e⟩ := hF.quotient
  have h := quotient_centralizer_card_dvd_six R (B.subgroupOf N)
    (by rw [hRcard]; norm_num) q hq hdis hcomm e
  rw [Nat.card_congr (subgroupOfEquivOfLe hBN).toEquiv, w.fixed_card] at h
  norm_num at h

/-- The order-168 branch of Janko's Lemma 6 is impossible. The intersection
witness and actor fusion are constructed from the stated hypotheses; the
F-normalizer conclusion is used only through its supplied implication. -/
public theorem l27_exclusion [IsSimpleGroup G]
    (hz3 : IsConj D.z (CaseII.into D k (CaseII.z 2)))
    (hF : IsConj D.z (CaseII.into D k CaseII.d) → FNormalizerAction D k)
    (h168 : Nat.card (CaseII.eNormalizerQuotient D k) = 168) : False := by
  obtain ⟨w⟩ := l27IntersectionWitness_of_168 D k h168
  exact l27_intersection_contradiction D k (hF (actor_fusion_of_168 D k hz3 h168)) w

end Theory.GroupTheory.HeldM22A10.M22Identification
