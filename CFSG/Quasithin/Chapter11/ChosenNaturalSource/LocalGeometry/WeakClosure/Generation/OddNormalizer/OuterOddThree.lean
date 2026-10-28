module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.OuterJankoThree
public import CFSG.Quasithin.ChapterA.Section02.OddBModelTwoRank

/-!
# Excluding odd ternary component covers in both actions

A faithful odd-characteristic action of degree three bounds the Sylow
Frattini quotient by 16. A normal abelian self-centralizing subgroup has
at most three weights, so its index is at most two and its first omega
subgroup has order at most eight. The projective linear and unitary
quotient maps retain this bound. The proved PSL₃(4) section obstruction
therefore rules out the original outer action on either ternary row.
The placed action is excluded by its original rank-six image.

The source consumer retains the actual component and all its original
normalizer, module and covering-quotient data. Remaining outer rows and
moved J₄ stay with qt-d-1222-natural-odd-kernel-normalizer; final 11.2.1
assembly stays with qt-d-1222-natural-weak-closure-source.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, using I.3.1
and the weight-permutation argument of A.3.21(c), pp.55--56.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative TensorProduct MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
variable {F P V : Type*} [Field F] [Group P] [Finite P]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

private theorem degree_three_frattini_le_sixteen
    (hP : IsPGroup 2 P) (rho : Representation F P V)
    (hrho : Function.Injective rho) (h2 : (2 : F) ≠ 0)
    (hdim : Module.finrank F V ≤ 3) :
    Nat.card (P ⧸ frattini P) ≤ 16 := by
  classical
  obtain ⟨A, hAn, hAc, hCA⟩ := exists_normal_abelian_selfCentralizing hP
  let : A.Normal := hAn
  let : IsMulCommutative A := hAc
  let E := AlgebraicClosure F
  let sigma := rho.extendScalars E
  have hsigma : Function.Injective sigma :=
    (extendScalars_faithful_iff E rho).mp hrho
  have h2E : (2 : E) ≠ 0 := by
    intro h
    apply h2
    apply (algebraMap F E).injective
    simpa only [map_ofNat, map_zero] using h
  have horderAE : (Nat.card A : E) ≠ 0 := by
    obtain ⟨k, hk⟩ := (hP.to_subgroup A).exists_card_eq
    rw [hk, Nat.cast_pow]
    exact pow_ne_zero _ h2E
  have hdimE : Module.finrank E (E ⊗[F] V) ≤ 3 := by
    simpa only [Module.finrank_baseChange] using hdim
  obtain ⟨hfinite, hweights⟩ :=
    characterWeight_card_le (sigma.comp A.subtype) horderAE
  let W := CharacterWeight (sigma.comp A.subtype)
  let : Finite W := hfinite
  let := Fintype.ofFinite W
  let i : P →* Subgroup.normalizer (A : Set P) :=
    (MonoidHom.id P).codRestrict _ (fun g => by
      rw [A.normalizer_eq_top]
      trivial)
  let f : P →* Equiv.Perm W :=
    ((automizerWeightPerm sigma A).comp A.normalizerMonoidHom.rangeRestrict).comp i
  have hker : f.ker = A := by
    have h := normalizerWeightPerm_ker sigma A hsigma horderAE
    ext g
    change i g ∈ ((automizerWeightPerm sigma A).comp
      A.normalizerMonoidHom.rangeRestrict).ker ↔ g ∈ A
    rw [h]
    change g ∈ Subgroup.centralizer (A : Set P) ↔ g ∈ A
    exact ⟨fun h => hCA h, fun h => A.le_centralizer h⟩
  have hdiv : A.index ∣ (Nat.card W).factorial := by
    rw [← hker, Subgroup.index_ker]
    have hd := f.range.card_subgroup_dvd_card
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm] using hd
  have hdiv6 : A.index ∣ 6 :=
    hdiv.trans (Nat.factorial_dvd_factorial (hweights.trans hdimE))
  have hidx6 : A.index ≤ 6 := by
    exact Nat.le_of_dvd (by decide) hdiv6
  obtain ⟨n, hncard⟩ := hP.index A
  have hnlt : n < 3 := by
    by_contra! hh
    have hh' := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    rw [← hncard] at hh'
    norm_num at hh'
    omega
  have hi2 : A.index ≤ 2 := by
    rw [hncard] at hdiv6 ⊢
    interval_cases n <;> norm_num at *
  let O := omega₁ A (p := 2)
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative A
  have hO : Nat.card O ≤ 8 := by
    exact (elementary_card_le_pow_finrank_of_involutive
      ((rho.comp A.subtype).comp O.subtype)
      ((hrho.comp A.subtype_injective).comp O.subtype_injective) h2).trans
      (pow_le_pow_right' (by decide) hdim)
  calc
    Nat.card (P ⧸ frattini P) ≤ A.index * Nat.card O :=
      hP.card_frattini_quotient_le_index_mul_omega_one A
    _ ≤ 2 * 8 := Nat.mul_le_mul hi2 hO
    _ = 16 := by norm_num


private theorem odd_linear_three_frattini_le_sixteen
    {Q : Type*} [Group Q] [Finite Q] {q : ℕ} (ho : Odd q)
    (hm : ClassicalGroup.IsPSL Q 3 q) (P : Sylow 2 Q) :
    Nat.card (P ⧸ frattini P) ≤ 16 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have h2 : (2 : F) ≠ 0 :=
    Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card (k := 1) ho
      (by simpa using hF)
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
  apply Theory.SpecificGroups.OddClassicalSylowFrattini.card_le_of_surjective
    (QuotientGroup.mk' (center SL(3,F))) (QuotientGroup.mk'_surjective _) ?_
    (P.mapSurjective e.surjective)
  intro U
  let f := Matrix.SpecialLinearGroup.toGL.comp (U : Subgroup SL(3,F)).subtype
  exact degree_three_frattini_le_sixteen U.isPGroup'
    ((generalLinearNatural 3).comp f)
    ((generalLinearNatural_injective 3).comp
      (Matrix.SpecialLinearGroup.toGL_injective.comp Subtype.val_injective)) h2 (by simp)

private theorem odd_unitary_three_frattini_le_sixteen
    {Q : Type*} [Group Q] [Finite Q] {q : ℕ} (ho : Odd q)
    (hm : ClassicalGroup.IsPSU Q 3 q) (P : Sylow 2 Q) :
    Nat.card (P ⧸ frattini P) ≤ 16 := by
  obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
  have h2 : (2 : F) ≠ 0 :=
    Theory.SpecificGroups.OddThreeRank.two_ne_zero_of_odd_card ho hF
  rw [SylowFrattiniBounds.card_congr (e.subgroupMap (P : Subgroup Q))]
  apply Theory.SpecificGroups.OddClassicalSylowFrattini.card_le_of_surjective
    (Matrix.ProjGenLinGroup.mk.subgroupMap J.specialSubgroup)
    (Matrix.ProjGenLinGroup.mk.subgroupMap_surjective J.specialSubgroup) ?_
    (P.mapSurjective e.surjective)
  intro U
  let f := J.specialSubgroup.subtype.comp (U : Subgroup J.specialSubgroup).subtype
  exact degree_three_frattini_le_sixteen U.isPGroup'
    ((generalLinearNatural 3).comp f)
    ((generalLinearNatural_injective 3).comp
      (Subtype.val_injective.comp Subtype.val_injective)) h2 (by simp)

open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L W : Subgroup G}
    (D : ChosenModule T L W) (S : D.NonbinaryNaturalInput)
include D S

/-- Neither odd ternary classical row can carry the original outer section.
The PSU parameter is the fixed-field order; its defining field has order q². -/
theorem moved_outer_not_odd_three {A : Subgroup G}
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (hB : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (houter : ∃ U : Subgroup (MulAut.Outer K), ∃ f : U →* coreCentralQuotient L,
      Function.Surjective f) {q : ℕ} (ho : Odd q) :
    ¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 q ∧
      ¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 q := by
  let P : Sylow 2 (K ⧸ center K) := default
  constructor
  · intro hm
    exact moved_outer_not_of_frattini_le_thirtytwo D S K hK houter hB P
      ((odd_linear_three_frattini_le_sixteen ho hm P).trans (by decide))
  · intro hm
    exact moved_outer_not_of_frattini_le_thirtytwo D S K hK houter hB P
      ((odd_unitary_three_frattini_le_sixteen ho hm P).trans (by decide))

open Chapter4 Chapter4.Section04
/-- The actual selected component avoids both odd ternary rows in either action.
The placed case uses its original rank-six image, and the outer case its actual
simple section. Neither argument replaces the original module or cover. -/
theorem moved_component_not_odd_three {A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (W : Set G))
    (hodd : Odd (Nat.card A))
    (hu : UniqueMaximalOvergroup (oddActorResidual L A) (normalizer (L : Set G)))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G))
    (K : Subgroup (normalizer (A : Set G)))
    (hK : IsComponent (normalizer (A : Set G)) K)
    (hB : ChapterA.Section02.IsTheoremBModel (K ⧸ center K))
    (houtK : ¬ K.map (normalizer (A : Set G)).subtype ≤ normalizer (L : Set G))
    {q : ℕ} (ho : Odd q) :
    ¬ ClassicalGroup.IsPSL (K ⧸ center K) 3 q ∧
      ¬ ClassicalGroup.IsPSU (K ⧸ center K) 3 q := by
  rcases moved_component_inner_or_outer_section D S hA hodd K hK with hi | ho'
  · obtain ⟨_,_,_,_,_,hr,_⟩ :=
      moved_component_placement_of_inner D S hA hodd hu hout K hK houtK hi
    constructor
    · intro hm
      have := ChapterA.Section02.odd_psl_three_twoRank_le_two ho hm
      omega
    · intro hm
      have := ChapterA.Section02.odd_psu_three_twoRank_le_two ho hm
      omega
  · exact moved_outer_not_odd_three D S K hK hB ho' ho

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer
