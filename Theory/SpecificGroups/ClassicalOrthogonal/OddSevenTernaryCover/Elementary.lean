module

public import Theory.SpecificGroups.ClassicalOrthogonal.OddSevenTernaryCover.Geometry
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Geometry
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Image.Containment
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover.Rank

/-!
# An elementary 3⁴ subgroup in an actual odd-seven involution centralizer

The concrete elementary subgroup of PSU₄(3) lifts isomorphically through
SU₄(3)'s scalar kernel of order four. The signed exterior realization maps
that lift injectively into the literal minus-six commutator: its kernel
consists of scalar signs and is already killed by the unitary projection.
The ternary minus-six block embeds projectively in the odd-seven carrier,
where its central negation remains a nonidentity involution.

This constructs the actual elementary-four centralizer witness needed by
the odd-central-cover argument, without any simplicity, quotient-quasithin,
or multiplier assumption. Source: Aschbacher–Smith I.2.1 and A.2.17; GLS3 §2.7.
-/

public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open ClassicalOrthogonal.Minus ClassicalOrthogonal.Minus.OddSixComparison
open Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
open Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover
namespace ClassicalOrthogonal.OddSevenTernaryCover
variable {F : Type} [Field F] [Finite F]

theorem exists_minusSix_elementary_four (hcard : Nat.card F = 3) :
    ∃ (A : Type) (_ : Group A) (_ : Finite A) (_ : IsElementaryAbelian 3 A),
      Nat.card A = 3^4 ∧ ∃ j : A →* MinusSix (F := F), Function.Injective j := by
  let J := unitaryForm 3 1
  have hF : Nat.card (Extension 3 1) = 3^2 := by simpa using card_extension 3 1
  have hJ : ∀ x, J.conj x = x^3 := by intro x; exact unitaryForm_conj 3 1 x
  obtain ⟨V,hG,hfin,hV,hVc,v,hv⟩ := exists_elementary_four_embedding J
    Nat.prime_three (by decide) hF hJ
  let := hG
  let := hfin
  let := hV
  let : IsElementaryAbelian 3 v.range :=
    IsElementaryAbelian.of_surjective v.rangeRestrict v.rangeRestrict_surjective
  have hcop : Nat.Coprime 3 (Nat.card (project J).ker) := by
    rw [card_project_kernel J hJ hF]
    decide
  obtain ⟨A,hA,hAm,hAc⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    (project J) (project_surjective J) hcop v.range
  let := hA
  have hAi := injective_comp_subtype_of_coprime_ker (project J) hcop A
    (IsElementaryAbelian.isPGroup 3 A)
  let R := Geometry.realization 3 1 F (by simpa using hcard)
  let w := R.omegaAction (R.action_mem_commutator (by decide : 3 ≠ 2))
  refine ⟨A,inferInstance,inferInstance,inferInstance,?_,w.comp A.subtype,?_⟩
  · rw [hAc,← Nat.card_congr (MonoidHom.ofInjective hv).toEquiv,hVc]
  · apply (injective_iff_map_eq_one _).mpr
    intro a ha
    have haa : R.action (a : J.specialSubgroup) = 1 := by
      have hh := congrArg Subtype.val ha
      simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, w,
        ExteriorRealization.omegaAction_val, Subgroup.coe_one] using hh
    have hp : project J (a : J.specialSubgroup) = 1 := by
      obtain ⟨c,_,hc⟩ := (R.action_eq_one_iff _).mp haa
      exact (unitary_project_eq_one_iff_scalar _).mpr ⟨c,hc⟩
    exact hAi (hp.trans (map_one _).symm)

theorem exists_elementary_four_involution_centralizer (hcard : Nat.card F = 3) :
    ∃ (z : POmegaOdd 3 F), orderOf z = 2 ∧
      ∃ (A : Type) (_ : Group A) (_ : Finite A) (_ : IsElementaryAbelian 3 A),
        Nat.card A = 3^4 ∧
          ∃ j : A →* centralizer ({z} : Set (POmegaOdd 3 F)), Function.Injective j := by
  let := Fintype.ofFinite F
  let : CharP F 3 := charP_of_card_eq_prime_pow (f := 1)
    (by simpa only [pow_one,Nat.card_eq_fintype_card] using hcard)
  obtain ⟨A,hG,hfin,hA,hAc,j,hj⟩ := exists_minusSix_elementary_four hcard
  let := hG
  let := hfin
  let := hA
  let z := projectiveBlock hcard (negativeSix hcard)
  have hz2 : z^2=1 := by rw [← map_pow,negativeSix_square,map_one]
  have hz1 : z ≠ 1 := fun hh => negativeSix_ne_one hcard
    (projectiveBlock_injective hcard (hh.trans (map_one _).symm))
  let k := (projectiveBlock hcard).comp j
  have hk : ∀ a, k a ∈ centralizer ({z} : Set (POmegaOdd 3 F)) := by
    intro a
    exact mem_centralizer_singleton_iff.mpr
      ((negativeSix_commute hcard (j a)).map (projectiveBlock hcard))
  refine ⟨z,orderOf_eq_prime hz2 hz1,A,inferInstance,inferInstance,inferInstance,hAc,
    k.codRestrict _ hk,?_⟩
  intro a b hab
  exact hj (projectiveBlock_injective hcard (congrArg Subtype.val hab))

end ClassicalOrthogonal.OddSevenTernaryCover
