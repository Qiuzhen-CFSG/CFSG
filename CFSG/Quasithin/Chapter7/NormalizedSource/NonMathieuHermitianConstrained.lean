module

public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianPushingUp
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.ConstrainedLinear
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedG2Normality
public import CFSG.Quasithin.ChapterC.Section04.ConstrainedLinearTwo
public import Theory.GroupTheory.Commutator.PerfectCoreKernel
public import Theory.GroupTheory.PerfectAutomorphismStabilizer
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order

/-!
# Excluding the constrained Hermitian pushing-up alternatives

The original normal residual has central quotient PSL₃(2^(2n)), n > 1.
Every nontrivial action of that residual has this projective group as a
quotient. A split-torus prime therefore has rank at least two in the actual
component action, and its perfect inner realization has order exceeding
9,999,360. The literal C.2.7 star catalogue is now excluded: the large linear,
symplectic and G₂ actions have odd rank at most one, and the remaining finite
rows violate the order bound. No natural-module or arbitrary-action input is
used. The selected escaping component is consequently ordinary and contains
both the original residual and the full moved module.

The actual chosen-orbit application is in
`Chapter12/Section02/ReductionSource/NonFFSourceNonMathieuHermitianOrdinary`.
Its ordinary-component exclusion and field-four endgame remain with
qt-d-1222-nonmathieu-hermitian-exclusion.
Source: Aschbacher--Smith C.2.7, C.3.2--4 and C.4.5--8, printed
pp.146--154, applied in 4.4 and 7.4.1 (refs/quasithin.pdf).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian

private theorem nontrivial_image_central_quotient {X Y : Type*} [Group X] [Finite X]
    [Group Y] [Finite Y] [Group.IsPerfect X] [IsQuasisimple (X ⧸ pCore 2 X)]
    (f : X →* Y) (hne : f ≠ 1) :
    ∃ g : f.range →* (X ⧸ pCore 2 X) ⧸ center (X ⧸ pCore 2 X),
      Function.Surjective g := by
  let q := QuotientGroup.mk' (pCore 2 X)
  have hproper : f.ker ≠ ⊤ := fun ht => hne (MonoidHom.ker_eq_top_iff.mp ht)
  have hc : f.ker.map q ≤ center (X ⧸ pCore 2 X) := by
    apply commutator_top_right_eq_bot_iff_le_center.mp
    rw [←map_top_of_surjective q (QuotientGroup.mk'_surjective _), ←map_commutator,
      Subgroup.map_eq_bot_iff]
    simpa only [q,QuotientGroup.ker_mk'] using normal_kernel_commutator_le_twoCore f.ker hproper
  let c := (QuotientGroup.mk' (center (X ⧸ pCore 2 X))).comp q
  have hk : f.ker ≤ c.ker := by
    intro x hx
    exact (QuotientGroup.eq_one_iff (q x)).mpr (hc (mem_map_of_mem q hx))
  let g := QuotientGroup.lift f.ker c hk
  have hg : Function.Surjective g :=
    QuotientGroup.lift_surjective_of_surjective f.ker c
      ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)) hk
  let e := QuotientGroup.quotientKerEquivRange f
  exact ⟨g.comp e.symm.toMonoidHom,hg.comp e.symm.surjective⟩

variable {G E : Type*} [Group G] [Finite G] [Field E] [Finite E]
variable {H M B R W : Subgroup G}

omit [Finite E] in
theorem constrained_hermitian_action_quotient
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal) [IsQuasisimple (B ⧸ pCore 2 B)]
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) :
    ∃ g : coreCentralActorImage K ((conjugateSpanBy B M).subgroupOf H) →*
      PSL(3,E), Function.Surjective g := by
  have hn : M ≤ normalizer (B : Set G) :=
    (normal_subgroupOf_iff_le_normalizer h.component_le).mp hN
  have hs : conjugateSpanBy B M = B :=
    le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)
  let X := (conjugateSpanBy B M).subgroupOf H
  have hXH : conjugateSpanBy B M ≤ H :=
    (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let := h.span_perfect
  let ex := subgroupOfEquivOfLe hXH
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := ex.symm.toMonoidHom) ex.symm.surjective
  let ec : (X ⧸ pCore 2 X) ≃* (B ⧸ pCore 2 B) :=
    (QuotientGroup.congr _ _ ex (pCore_map_iso 2 ex)).trans
      (QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hs)
        (pCore_map_iso 2 (MulEquiv.subgroupCongr hs)))
  let : IsQuasisimple (X ⧸ pCore 2 X) := IsQuasisimple.of_mulEquiv ec.symm
  have hnorm := h.constrained_span_normalizes_intrinsic K hK hq
  let j := inclusion hnorm
  let f := (normalizerCoreCentralAction K).comp j
  have he : f.range = coreCentralActorImage K X := by
    ext a
    constructor
    · rintro ⟨x,rfl⟩
      exact mem_map_of_mem _ (show j x ∈ X.subgroupOf _ from x.property)
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨(x : H),hx⟩,rfl⟩
  have hne : f ≠ 1 := by
    intro hf
    apply h.constrained_span_action_nontrivial K hK hq hout
    rw [←he,hf,MonoidHom.range_one]
  obtain ⟨g,hg⟩ := nontrivial_image_central_quotient f hne
  let es := (QuotientGroup.congr _ _ ec (FixedElementary.map_center ec)).trans e
  let er := MulEquiv.subgroupCongr he
  exact ⟨es.toMonoidHom.comp (g.comp er.symm.toMonoidHom),
    es.surjective.comp (hg.comp er.symm.surjective)⟩

theorem constrained_hermitian_action_rank
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal) [IsQuasisimple (B ⧸ pCore 2 B)]
    {n : ℕ} (hn : 1 < n) (hc : Nat.card E = 2^(2*n))
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧
      2 ≤ primeRank p (coreCentralActorImage K ((conjugateSpanBy B M).subgroupOf H)) := by
  obtain ⟨g,hg⟩ := constrained_hermitian_action_quotient h hN e K hK hq hout
  obtain ⟨p,hp,hp3,hd⟩ := Nat.BinarySignedTorus.exists_prime_gt_three_dvd_sub
    (by omega : 3 < 2*n)
  let : Fact p.Prime := ⟨hp⟩
  have ho := hp.odd_of_ne_two (by omega : p ≠ 2)
  have hr := Matrix.PSL3.SplitPrimeRank.projective_rank E (by omega : p ≠ 3)
    (by simpa only [hc] using hd)
  refine ⟨p,hp,ho,?_⟩
  by_contra! hrank
  let P : Sylow p (coreCentralActorImage K ((conjugateSpanBy B M).subgroupOf H)) :=
    Classical.choice inferInstance
  have hu := P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one ho (by omega)) g hg
  omega

private theorem large_projective_order (hc : 16 ≤ Nat.card E) :
    9999360 < Nat.card PSL(3,E) := by
  have he := Matrix.PSL3.LinearThree.card_projective_mul_scalar E
  have hg : Nat.gcd 3 (Nat.card E - 1) ≤ 3 := Nat.gcd_le_left _ (by decide)
  have hl := Nat.mul_le_mul
    (Nat.mul_le_mul (Nat.pow_le_pow_left hc 3)
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hc 3) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hc 2) 1)
  norm_num at hl
  have hu := Nat.mul_le_mul_left (Nat.card PSL(3,E)) hg
  nlinarith

theorem constrained_hermitian_core_card_gt
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal) [IsQuasisimple (B ⧸ pCore 2 B)]
    {n : ℕ} (hn : 1 < n) (hc : Nat.card E = 2^(2*n))
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) :
    9999360 < Nat.card (coreCentralQuotient K) := by
  obtain ⟨g,hg⟩ := constrained_hermitian_action_quotient h hN e K hK hq hout
  let := hq
  let Q := coreCentralQuotient K
  let : IsSimpleGroup Q := hq.simple
  let X := conjugateSpanBy B M
  let A := X.subgroupOf H
  let C := coreCentralActorImage K A
  have hXH : X ≤ H := (conjugateSpanBy_le_self h.component_le).trans h.local_le
  let := h.span_perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hXH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hXH).symm.surjective
  let : Group.IsPerfect C := coreCentralActorImage_perfect K A
    (h.constrained_span_normalizes_intrinsic K hK hq)
  let : Group.IsSolvable (MulAut.Outer Q) := h.constrained_core_central_outer_solvable K hq
  have hz : center Q = ⊥ := by
    rcases (inferInstance : (center Q).Normal).eq_bot_or_eq_top with hc | hc
    · exact hc
    · exact (Group.IsPerfect.not_isMulCommutative Q (center_eq_top_iff.mp hc)).elim
  obtain ⟨f,hf,_⟩ := MulAut.perfect_subgroup_exists_inner_lift C hz
  have hlarge : 16 ≤ Nat.card E := by
    rw [hc]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 4 ≤ 2*n)
  exact (large_projective_order hlarge).trans_le
    ((Nat.card_le_card_of_surjective g hg).trans (Nat.card_le_card_of_injective f hf))

private theorem card_linear_three_two {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) : Nat.card SL(3,F) = 168 := by
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
  norm_num [hF,Fin.prod_univ_succ] at hc
  rw [card_eq_card_quotient_mul_card_subgroup (center SL(3,F)),
    Atlas.ExceptionalSupport.card_sl_center]
  change Nat.card PSL(3,F) * Nat.gcd 3 (Nat.card F - 1) = 168
  norm_num [hF,hc]

private theorem card_linear_five_two {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) : Nat.card SL(5,F) = 9999360 := by
  have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
  norm_num [hF,Fin.prod_univ_succ] at hc
  rw [card_eq_card_quotient_mul_card_subgroup (center SL(5,F)),
    Atlas.ExceptionalSupport.card_sl_center]
  change Nat.card PSL(5,F) * Nat.gcd 5 (Nat.card F - 1) = 9999360
  norm_num [hF,hc]

open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer

theorem no_constrained_hermitian_component
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hN : (B.subgroupOf M).Normal) [IsQuasisimple (B ⧸ pCore 2 B)]
    {n : ℕ} (hn : 1 < n) (hc : Nat.card E = 2^(2*n))
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E))
    (K : Subgroup H) (hK : K.IsCComponent) (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ M.subgroupOf H) (hfK : generalizedFitting K = pCore 2 K) : False := by
  have hm := ChapterC.C27Source.star_model_from_source
    (h.constrained_source_input K hK hq hout hfK)
  have hcard := constrained_hermitian_core_card_gt h hN hn hc e K hK hq hout
  have hsmall (hsize : Nat.card (starImage (K.map H.subtype) R (K.map H.subtype)) ≤
      9999360) : False := by
    have hle : Nat.card (coreCentralQuotient K) ≤
        Nat.card (starImage (K.map H.subtype) R (K.map H.subtype)) := by
      rw [Nat.card_congr (h.constrained_star_central_equiv K hK hq hout hfK).toEquiv]
      exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    omega
  obtain ⟨p,hp,ho,hr⟩ := constrained_hermitian_action_rank h hN hn hc e K hK hq hout
  let : Fact p.Prime := ⟨hp⟩
  cases hm with
  | linearTwo F es =>
    exact h.no_constrained_component_star_linear_two K hK hq hout hfK F es
  | linearThree F es =>
    by_cases hlarge : 1 < F.degree
    · have hF : 4 ≤ Nat.card F.Carrier := by
        rw [F.card_eq]
        exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
      have hu := linear_three_span_odd_rank h K hK hq hout hfK es hF ho
      omega
    · have hd : F.degree = 1 := by have := F.degree_pos; omega
      apply hsmall
      rw [Nat.card_congr es.toEquiv,card_linear_three_two (by rw [F.card_eq,hd,pow_one])]
      decide
  | symplectic F hlarge es =>
    have hF : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
    have hu := h.constrained_symplectic_span_rank_le_one K hK hq hout hfK es hF ho
    omega
  | g2 F hlarge es =>
    have hF : 4 ≤ Nat.card F.Carrier := by
      rw [F.card_eq]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
    have hu := h.constrained_g2_span_rank_le_one K hK hq hout hfK es hF ho
    omega
  | g2DerivedTwo es =>
    apply hsmall
    rw [Nat.card_congr es.toEquiv,Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)]
    decide
  | alternating m hm es =>
    apply hsmall
    rw [Nat.card_congr es.toEquiv]
    rcases hm with rfl | rfl | rfl | rfl <;> rw [nat_card_alternatingGroup] <;> norm_num
  | linearFiveTwo es =>
    apply hsmall
    rw [Nat.card_congr es.toEquiv,card_linear_five_two (by simp)]
  | tripleSix ez es =>
    rw [Nat.card_congr (h.constrained_star_central_equiv K hK hq hout hfK).toEquiv,
      Nat.card_congr es.toEquiv,nat_card_alternatingGroup] at hcard
    norm_num at hcard

theorem pushingUp_ordinary_component
    (h : ChapterC.HypothesisC28 KnownSimple.IsKnownSimple H M B R W)
    (hstrict : M < H) (hN : (B.subgroupOf M).Normal) [IsQuasisimple (B ⧸ pCore 2 B)]
    {n : ℕ} (hn : 1 < n) (hc : Nat.card E = 2^(2*n))
    (e : ((B ⧸ pCore 2 B) ⧸ center (B ⧸ pCore 2 B)) ≃* PSL(3,E)) :
    ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧ ¬ K ≤ M.subgroupOf H ∧
      B.subgroupOf H ≤ K ∧ W.subgroupOf H ≤ K := by
  obtain ⟨K,hK,hq,hout,_,hcases⟩ := pushingUp_escaping_component h hstrict hn hc e
  rcases hcases with ⟨ho,hn,hB,hW⟩ | ⟨hfK,_,_⟩
  · exact ⟨K,ho,hn,hout,hB,hW⟩
  · exact (no_constrained_hermitian_component h hN hn hc e K hK hq hout hfK).elim

end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitian
