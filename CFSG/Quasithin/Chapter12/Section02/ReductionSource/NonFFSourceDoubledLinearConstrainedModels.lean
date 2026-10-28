module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearOrdinary
public import CFSG.Quasithin.Chapter4.Section04.NormalizedRankOneOddControl.PushingUpConstrained
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedPlacement
public import Theory.SpecificGroups.Classical.EvenDerivedThree
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledLinearOrdinary
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48ConstrainedPlacement

/-!
# The actual constrained stars for a nonbinary linear-three residual

The literal residual has simple quotient PSL₃(2^f), of order at least 20160.
The genuine constrained local exclusions remove all large Lie rows, and
smaller finite rows fail the actual simple-section divisibility. Only A₈
and SL₅(2) remain, including the equal-order field-four case. Their complete
core quotient has trivial center, cubic rank two and two-group outer action.
Its index is prime to three, forcing the original perfect residual into K.
No whole-module replacement or parabolic placement is assumed.

Source: Aschbacher--Smith C.2.7 and C.4.5--8, printed pp.146--147,152--154,
applied to the original 7.3.4 reciprocal witness, p.699, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open Chapter4.Section04.NormalizedRankOneOddControl
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem linear_three_card_ge (F : BinaryField) (hF : 1 < F.degree) :
    20160 ≤ Nat.card PSL(3,F.Carrier) := by
  rw [Matrix.PSL3.LinearThree.card_projective,F.card_eq]
  by_cases hf : F.degree = 2
  · norm_num [hf]
  have hq : 8 ≤ 2 ^ F.degree :=
    Nat.pow_le_pow_right (n := 2) (by decide) (by omega : 3 ≤ F.degree)
  have hb := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.pow_le_pow_left hq 3)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 3) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
  have hden : Nat.gcd 3 (2 ^ F.degree - 1) ≤ 3 := Nat.gcd_le_left _ (by decide)
  have hh := (Nat.div_le_div_right hb (c := 3)).trans
    (Nat.div_le_div_left hden (Nat.gcd_pos_of_pos_left _ (by decide)))
  norm_num at hh
  omega

private theorem constrained_binary_models_of_large_simple
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    {H M F R W : Subgroup G}
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M F R W)
    (hn : M ≤ normalizer (F : Set G))
    (hS : ¬ Group.IsSolvable S) (hsize : 20160 ≤ Nat.card S)
    (hexp : ¬ ∀ P : Subgroup S, IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : F →* S) (hπ : Function.Surjective π)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K)) (hout : ¬ K ≤ M.subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    Nonempty (starImage (K.map H.subtype) R (K.map H.subtype) ≃* alternatingGroup (Fin 8)) ∨
    Nonempty (starImage (K.map H.subtype) R (K.map H.subtype) ≃* SL(5,ZMod 2)) := by
  let X := starImage (K.map H.subtype) R (K.map H.subtype)
  let ec := h.constrained_star_central_equiv K hK hq hout hfK
  have hd := (constrained_normalized_simple_order_dvd h hn hS π hπ K hK hq hout).trans
    ((Nat.card_congr ec.toEquiv).symm ▸ (center X).card_quotient_dvd_card)
  have hsmall (hx : Nat.card X < 20160) : False := by
    have hh := Nat.le_of_dvd Nat.card_pos hd
    omega
  have hm := ChapterC.C27Source.star_model_from_source
    (h.constrained_source_input K hK hq hout hfK)
  cases hm with
  | linearTwo E e => exact (h.no_constrained_component_star_linear_two K hK hq hout hfK E e).elim
  | linearThree E e =>
    by_cases hE : 1 < E.degree
    · exact (no_constrained_normalized_linear_three h hn hS hexp π hπ K hK hq hout hfK E hE e).elim
    · have hdeg : E.degree = 1 := by have := E.degree_pos; omega
      apply (hsmall ?_).elim
      rw [Nat.card_congr e.toEquiv]
      have hc := (center SL(3,E.Carrier)).index_mul_card
      rw [Atlas.ExceptionalSupport.card_sl_center] at hc
      change Nat.card PSL(3,E.Carrier) * Nat.gcd 3 (Nat.card E.Carrier - 1) = _ at hc
      rw [←hc,Matrix.PSL3.LinearThree.card_projective_mul_scalar,E.card_eq,hdeg]
      norm_num
  | symplectic E hE e =>
    exact (no_constrained_normalized_symplectic h hn hS hexp π hπ K hK hq hout hfK e (by
      rw [E.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ E.degree))).elim
  | g2 E hE e =>
    exact (no_constrained_normalized_g2 h hn hS hexp π hπ K hK hq hout hfK e (by
      rw [E.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ E.degree))).elim
  | g2DerivedTwo e =>
    apply (hsmall ?_).elim
    rw [Nat.card_congr e.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
    norm_num
  | alternating n hn' e =>
    rcases hn' with rfl | rfl | rfl | rfl
    · apply (hsmall ?_).elim
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    · apply (hsmall ?_).elim
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    · apply (hsmall ?_).elim
      rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    · exact Or.inl ⟨e⟩
  | linearFiveTwo e => exact Or.inr ⟨e⟩
  | tripleSix ez e =>
    apply (hsmall ?_).elim
    have hc := (center X).index_mul_card
    change Nat.card (X ⧸ center X) * Nat.card (center X) = Nat.card X at hc
    rw [Nat.card_congr e.toEquiv,Nat.card_congr ez.toEquiv,nat_card_alternatingGroup] at hc
    norm_num at hc
    omega

variable {T : Sylow 2 G} {L V : Subgroup G} (D : ChosenModule T L V)

/-- The original nonbinary reciprocal witness leaves only the actual binary
SL₄/SL₅ constrained stars, retaining the field-four equal-order case. -/
theorem sourceOrbit_linear_witness_constrained_models
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃*
      alternatingGroup (Fin 8)) ∨
    Nonempty (starImage (K.map H.subtype) (J.pCoreIn 2) (K.map H.subtype) ≃* SL(5,ZMod 2)) := by
  have hc := D.sourceOrbit_linear_witness_hypothesisC28 h hd F hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  obtain ⟨e⟩ := D.linear_central_quotient h F hmodel
  let := h.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (PSL(3,F.Carrier)) := e.symm.isSimpleGroup
  let : Group.IsPerfect (PSL(3,F.Carrier)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  rcases hw with ⟨_,_,_,_,_,_,_,_,_,_,_,⟨c,_⟩,_⟩
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let π : LH →* PSL(3,F.Carrier) := e.toMonoidHom.comp
    ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp
      (c.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH))))
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (c.surjective.comp (QuotientGroup.mk'_surjective _)))
  exact constrained_binary_models_of_large_simple hc hn (Group.IsPerfect.not_isSolvable _)
    (linear_three_card_ge F hF)
    (Matrix.PSL3.LinearThree.not_two_exponent (MulEquiv.refl _) F.card_eq) π hπ K hK hq hout hfK

/-- The same original perfect residual lies in the actual constrained K;
normality and the prime-to-three index are derived from the retained star. -/
theorem sourceOrbit_linear_witness_constrained_placement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3)))
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    K.Normal ∧
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).subgroupOf H ≤ K := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hc := D.sourceOrbit_linear_witness_hypothesisC28 h hd F hmodel hw hWJ hJC
  have hn := (normal_subgroupOf_iff_le_normalizer hc.component_le).mp
    hw.2.2.2.2.2.2.2.2.1
  have hspan := hc.normalized_span_eq hn
  let : Group.IsPerfect LH := by
    have hh := hc.span_perfect
    rwa [hspan] at hh
  have hfacts := core_facts_of_linear_star hc K hK hq hout hfK
    (D.sourceOrbit_linear_witness_constrained_models h hd F hF hmodel hw hWJ hJC K hK hq hout hfK)
  let := hq
  let : K.Normal := hc.constrained_component_normal_of_core_threeRank K hK hq hout hfK hfacts.2.1
  have ho : Nat.Coprime 3 (Nat.card (MulAut.Outer (K ⧸ pCore 2 K))) := by
    obtain ⟨n,hn⟩ := hfacts.2.2.exists_card_eq
    rw [hn]
    exact (show Nat.Coprime 3 2 by decide).pow_right n
  have hi := cComponent_index_coprime_three_of_quotient K hK hfacts.1 hfacts.2.1
    (hc.sqtk.stronglyQuasithin 3 (by decide) (by decide)) ho
  obtain ⟨e⟩ := D.linear_central_quotient h F hmodel
  let := h.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : IsSimpleGroup (PSL(3,F.Carrier)) := e.symm.isSimpleGroup
  let : Group.IsPerfect (PSL(3,F.Carrier)) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  rcases hw with ⟨_,_,_,_,_,_,_,_,_,_,_,⟨c,_⟩,_⟩
  let r : LH →* (L ⧸ pCore 2 L) := c.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH))
  have hrk : r.ker = pCore 2 LH := by
    rw [MonoidHom.ker_comp_of_injective _ _ c.injective,QuotientGroup.ker_mk']
  let : Group.IsNilpotent (pCore 2 LH) := pCore_isPGroup.isNilpotent
  let : Group.IsSolvable r.ker := hrk.symm ▸ inferInstanceAs (Group.IsSolvable (pCore 2 LH))
  let π : LH →* PSL(3,F.Carrier) := e.toMonoidHom.comp
    ((QuotientGroup.mk' (center (L ⧸ pCore 2 L))).comp r)
  have hπ : Function.Surjective π := e.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp (c.surjective.comp (QuotientGroup.mk'_surjective _)))
  let : Group.IsSolvable π.ker := by
    have he : π.ker = (center (L ⧸ pCore 2 L)).comap r := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective,
        ←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    rw [he]
    exact isSolvable_comap_of_solvable_ker r _
  have hLH : LH ≤ H := hc.component_le.trans hc.local_le
  let f : LH →* H ⧸ K := (QuotientGroup.mk' K).comp (inclusion hLH)
  have hf : f = 1 := by
    by_contra hne
    let : Group.IsSolvable f.ker := solvable_ker_of_nontrivial_hom_of_simple_quotient π hπ f hne
    have hdvd := SimpleSection.card_dvd_of_solvable_representation
      (Group.IsPerfect.not_isSolvable (PSL(3,F.Carrier))) π hπ f
    have hthree : 3 ∣ Nat.card PSL(3,F.Carrier) :=
      (Theory.SpecificGroups.Classical.EvenDerivedThree.three_dvd_card_psl_commutator
        (F := F.Carrier) (show (0 : Fin 3) ≠ 1 by decide)).trans (card_subgroup_dvd_card _)
    rw [←index_eq_card] at hdvd
    exact Nat.prime_three.coprime_iff_not_dvd.mp hi (hthree.trans hdvd)
  refine ⟨inferInstance,?_⟩
  intro x hx
  let l : LH := ⟨x,hx⟩
  exact (QuotientGroup.eq_one_iff x).mp (DFunLike.congr_fun hf l)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
