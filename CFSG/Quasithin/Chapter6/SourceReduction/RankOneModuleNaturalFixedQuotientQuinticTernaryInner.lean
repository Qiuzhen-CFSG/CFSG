module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticEffectiveProduct
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientQuinticQuotient
public import Theory.GroupTheory.PPerfectQuinticExponent
public import Theory.SpecificGroups.PSL3.OddPrimeOuterExponent
public import Theory.SpecificGroups.SU3.OddPrimeOuterExponent

/-!
# The whole original quintic action in odd-prime ternary carriers

The actual quintic residual is two-perfect and has quotient of order five
by its two-core. Every outer automorphism of either odd-prime ternary
carrier has sixth power one. Thus the original normalizer action has
trivial outer image. The diagonal cubic automorphisms cause no difficulty:
the proof uses the exponent bound without declaring the outer group a
two-group. The same original core-central quotient and action are retained.

Source: Aschbacher--Smith 6.1.4, printed pp.665--666, and A.3.18,
printed pp.51--53; GLS3 Theorem 2.5.12.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped MatrixGroups
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

private theorem original_inner_of_sixth_power
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁)
    (hpow : ∀ a : MulAut (coreCentralQuotient K),
      a ^ 6 ∈ MulAut.innerSubgroup (coreCentralQuotient K)) :
    coreCentralActorImage K (quinticResidual T L) ≤
      MulAut.innerSubgroup (coreCentralQuotient K) := by
  let X := quinticResidual T L
  have hXN : X ≤ normalizer (K : Set G) :=
    original_hermitian_quintic_normalizes_component h hout hm hM₁ hCM₁ hK
  let f : X →* MulAut (coreCentralQuotient K) :=
    (normalizerCoreCentralAction K).comp (inclusion hXN)
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (coreCentralQuotient K))
  have hz := hom_eq_one_of_twoPerfect_quintic_of_sixth_power
    (quinticResidual_twoPerfect T L)
    (original_hermitian_quintic_core_quotient h hout hm).2 (q.comp f) (by
      intro x
      change q (f x) ^ 6 = 1
      rw [←map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (hpow (f x)))
  rintro _ ⟨a,ha,rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  exact DFunLike.congr_fun hz ⟨a.val,ha⟩

private theorem sixth_power_inner_transport {C D : Type*} [Group C] [Group D]
    (e : C ≃* D) (hp : ∀ a : MulAut D, a ^ 6 ∈ MulAut.innerSubgroup D)
    (a : MulAut C) : a ^ 6 ∈ MulAut.innerSubgroup C := by
  have hh := hp (MulAut.congr e a)
  rw [←MulAut.map_innerSubgroup_congr e] at hh
  obtain ⟨b,hb,he⟩ := hh
  exact (show b = a ^ 6 from (MulAut.congr e).injective
    (he.trans (map_pow (MulAut.congr e) a 6).symm)) ▸ hb

/-- In the odd-prime linear-three row, the entire original quintic
normalizer action lies in the actual inner automorphism subgroup. -/
theorem original_hermitian_quintic_odd_linear_three_inner
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hc : ClassicalGroup.IsPSL (coreCentralQuotient K) 3 p) :
    coreCentralActorImage K (quinticResidual T L) ≤
      MulAut.innerSubgroup (coreCentralQuotient K) := by
  let := hq
  let : IsSimpleGroup (coreCentralQuotient K) := IsQuasisimple.simple
  let : Group.IsPerfect (coreCentralQuotient K) := Group.IsPerfect.ofSurjective
    (QuotientGroup.mk'_surjective (center (K ⧸ pCore 2 K)))
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hc
  let : IsSimpleGroup PSL(3,F) := e.isSimpleGroup_congr.mp inferInstance
  let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  apply original_inner_of_sixth_power h hout hm hM₁ hCM₁ hK
  exact sixth_power_inner_transport e
    (Matrix.PSL3.odd_prime_sixth_power_inner
      (Group.IsPerfect.not_isSolvable PSL(3,F)) hp ho hF)

/-- In the odd-prime unitary-three row, the entire original quintic
normalizer action is inner, including when diagonal outer cubics exist. -/
theorem original_hermitian_quintic_odd_unitary_three_inner
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (p : ℕ) (hp : p.Prime) (ho : Odd p)
    (hc : ClassicalGroup.IsPSU (coreCentralQuotient K) 3 p) :
    coreCentralActorImage K (quinticResidual T L) ≤
      MulAut.innerSubgroup (coreCentralQuotient K) := by
  let := hq
  let : IsSimpleGroup (coreCentralQuotient K) := IsQuasisimple.simple
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hc
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    e.isSimpleGroup_congr.mp inferInstance
  apply original_inner_of_sixth_power h hout hm hM₁ hCM₁ hK
  exact sixth_power_inner_transport e (J.odd_prime_sixth_power_inner hp ho hF hconj)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
