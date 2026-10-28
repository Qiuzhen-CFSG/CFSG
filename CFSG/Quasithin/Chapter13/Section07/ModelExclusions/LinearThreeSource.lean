module
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.LinearThreeAction
public import CFSG.Quasithin.Chapter13.Section07.ModelExclusions.RankOne
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.Earlier
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.Lifting
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.GroupTheory.PrimeRankZero
/-!
# The source setup for the contained three-dimensional linear branch

The whole natural action gives H=KT. The component quotient has order168,
so its three-rank is at most one. The nontrivial original point residual
normalizes the seed, giving rank exactly one there; 13.7.5(5) makes the
local quotient ordinary A6. These are the actual inputs to the C3-system
construction in the n=3 exclusion, which is a separate source obligation.

Source: Aschbacher–Smith, 13.7.6(1), printed p.939.
-/
@[expose] public section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07.ModelExclusions
open Section08.SourceCompletion
open Section08.TransvectionRecognition Component
open Section08.TransvectionRecognition.Component.ModelExtension
open Section08.TransvectionRecognition.Component.RecognitionStep
open Section08.TransvectionParabolic.Marking
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
  [(V₁.subgroupOf (Section08.Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Section08.Source.Utilde H V₃ V₁)]
include d
/-- The actual three-dimensional case gives H=KT, ordinary L and the full natural actor. -/
theorem linear_three_source_setup_of_one_le
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 3) eK) :
    (H : Set G) = (K : Set G) * (T : Set G) ∧
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
    primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) = 1 ∧
    ∃ (eH : Section08.Source.Hstar H ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
      (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)),
      (∀ k : K, eH (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) =
        eK (QuotientGroup.mk' (pCore 2 K) k)) ∧
      ∀ a v, eV (ρ a v) = eH a (eV v) := by
  obtain ⟨eH,eV,heK,heV⟩ := linear_three_full_action_of_one_le d hH hF9 hKH hK hL₁K ρ hρ eK hs
  have hprod : (H : Set G) = (K : Set G) * (T : Set G) := by
    apply product_of_star_product_sylow T H K hF9.T_le_H hKH
    intro x
    obtain ⟨y,hy⟩ := eK.surjective (eH x)
    obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) y
    have he : QuotientGroup.mk' (pCore 2 H) (inclusion hKH k) = x := eH.injective (by rw [heK,hk,hy])
    refine ⟨_,⟨inclusion hKH k,k.property,rfl⟩,1,one_mem _,?_⟩
    exact (mul_one _).trans he |>.symm
  have hkr : primeRank 3 K ≤ 1 := by
    rw [←primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup,
      primeRank_equiv 3 (eK.trans (BinaryLinear.OuterCyclic.slEquivLinear 3).symm)]
    let P : Sylow 3 BinaryLinearThree.Group := default
    apply P.primeRank_le_one_of_isCyclic
    obtain ⟨a,ha⟩ := P.isPGroup'.exists_card_eq
    have hsmall : a ≤ 1 := by
      by_contra! hh
      have hd := (ha ▸ pow_dvd_pow 3 (by omega : 2 ≤ a)).trans
        (P : Subgroup BinaryLinearThree.Group).card_subgroup_dvd_card
      rw [Matrix.PSL3Two.card_SL] at hd
      norm_num at hd
    apply isCyclic_of_card_dvd_prime (p := 3)
    rw [ha]
    simpa using pow_dvd_pow 3 hsmall
  have hu := (primeRank_mono 3 (show K ⊓ normalizer (V₃ : Set G) ≤ K from inf_le_left)).trans hkr
  have hn : primeRank 3 (sourceOne L T V₁) ≠ 0 := by
    intro hz
    have hq : primeRank 3 (sourceOne L T V₁ ⧸ pCore 2 (sourceOne L T V₁)) = 0 := by
      rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) _ pCore_isPGroup,hz]
    have hnd := PrimeRank.eq_zero_iff_not_dvd_card.mp hq
    rcases point_residual_quotient_card d with hc | hc <;> rw [hc] at hnd <;> exact hnd (by decide)
  have hl := primeRank_mono 3 (le_inf hL₁K (point_residual_normalizes_seed d))
  have hr : primeRank 3 (K ⊓ normalizer (V₃ : Set G) : Subgroup G) = 1 := by omega
  exact ⟨hprod,ordinary_of_rank_one d hL₁K hr,hr,eH,eV,heK,heV⟩

/-- Original13.7.6(i): the component has no fixed vector on the actual quotient module. -/
theorem linear_three_fixed_eq_bot_of_one_le
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin 3 → ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 3) eK) :
    Representation.BinaryOffender.fixedSpace ρ (Section08.Source.starImage H K) = ⊥ := by
  obtain ⟨eH,eV,heK,heV⟩ := linear_three_full_action_of_one_le d hH hF9 hKH hK hL₁K ρ hρ eK hs
  apply _root_.eq_bot_iff.mpr
  intro u hu
  change u = 0
  have hf : eV u ∈ OneCohomology.fixed BinaryLinearThree.W := by
    intro g
    obtain ⟨y,hy⟩ := eK.surjective (BinaryLinear.OuterCyclic.slEquivLinear 3 g)
    obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) y
    let x := QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)
    have hu' := hu ⟨x, ⟨inclusion hKH k,k.property,rfl⟩⟩
    calc
      (BinaryLinearThree.W g) (eV u) = eH x (eV u) := by
        rw [heK, hk, hy]
        rfl
      _ = eV (ρ x u) := (heV x u).symm
      _ = eV u := congrArg eV hu'
  rw [OneCohomology.SLHigherNatural.fixed_eq_bot (by decide : 2 ≤ 3)] at hf
  exact eV.injective (hf.trans (map_zero eV).symm)
/-- The same original branch in the literal projective matrix convention of13.7.6(1). -/
theorem projective_three_source_setup_of_one_le
    (hH : H ∈ Section08.Source.Hz (sourceOne L T V₁) T G₁ M)
    (hF9 : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hL₁K : sourceOne L T V₁ ≤ K)
    (ρ : Representation (ZMod 2) (Section08.Source.Hstar H)
      (Additive (Section08.Source.Utilde H V₃ V₁)))
    (hρ : IsConjugation H V₃ V₁ ρ)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
    (hs : HasSectionModel H V₃ V₁ ρ K hKH (projectiveRepresentation 3 (by decide)) eK) :
    (H : Set G) = (K : Set G) * (T : Set G) ∧
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
    ∃ (eH : Section08.Source.Hstar H ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))
      (eV : Additive (Section08.Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] (Fin 3 → ZMod 2)),
      (∀ k : K, eH (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k)) =
        eK (QuotientGroup.mk' (pCore 2 K) k)) ∧
      ∀ a v, eV (ρ a v) = (projectiveRepresentation 3 (by decide)) (eH a) (eV v) := by
  let c := BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 3)
  have hs' : HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation 3) (eK.trans c) := by
    obtain ⟨hst,e,he⟩ := hs
    exact ⟨hst,e,he⟩
  obtain ⟨hp,hc,_,eH,eV,heK,heV⟩ :=
    linear_three_source_setup_of_one_le d hH hF9 hKH hK hL₁K ρ hρ (eK.trans c) hs'
  refine ⟨hp,hc,eH.trans c.symm,eV,?_,?_⟩
  · intro k
    change c.symm (eH (QuotientGroup.mk' (pCore 2 H) (inclusion hKH k))) = _
    rw [heK]
    exact c.symm_apply_apply _
  · intro a v
    change eV (ρ a v) = linearRepresentation 3 (c (c.symm (eH a))) (eV v)
    rw [c.apply_symm_apply]
    exact heV a v
end CFSG.Quasithin.Chapter13.Section07.ModelExclusions
