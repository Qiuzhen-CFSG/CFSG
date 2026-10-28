module
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.Models
public import CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu.Action
public import Theory.AtlasPort.LinearGroups.G2.PerfectTwoNormalizer
public import Theory.SpecificGroups.Triality.PerfectTwoNormalizer
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.PerfectThreeRank
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# The full Mathieu seed in the remaining binary simple sections

The actual parabolic normalizer bounds in binary G₂, triality and Ree F₄
exclude perfect Mathieu sections from normalizers of nontrivial two-groups.
Consequently the original two-core of the full seed dies in its literal
simple-section map. If the seed modulo that core is quasisimple, its image
is an ordinary quasisimple M₂₂ cover. No covering kernel is suppressed.

The application is Hall.OddNormalizer.OddLocalSeed. This is one part of the
odd-local comparison in Aschbacher--Smith 4.4.3, printed p.623; exclusion of
these three remaining binary families is a separate step. The concrete
parabolic results retain the source attribution of their imported modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu
open Sporadic.Mathieu

/-- A Mathieu radical quotient forces three-rank at least two before quotienting. -/
theorem mathieu_radical_three_rank {B : Type*} [Group B] [Finite B]
    (e : (B ⧸ solvableRadical B) ≃* M22) : 2 ≤ primeRank 3 B := by
  by_contra hn
  let P : Sylow 3 B := Sylow.nonempty.some
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (solvableRadical B))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hh := P.primeRank_le_one_of_surjective
    (P.isCyclic_of_odd_of_primeRank_le_one (by decide) (by omega)) f hf
  rw [m22_primeRank_three] at hh
  omega

/-- A perfect Mathieu section in a remaining binary model normalizes no
nontrivial two-subgroup of that model. -/
theorem rank_two_normalized_two_group_eq_bot {S : Type*} [Group S] [Finite S]
    (hm : RemainingOddLocalRankTwoModel S)
    (B U : Subgroup S) [Group.IsPerfect B]
    (eB : (B ⧸ solvableRadical B) ≃* M22)
    (hU : IsPGroup 2 U) (hN : B ≤ normalizer (U : Set S)) : U = ⊥ := by
  classical
  by_contra hne
  have hr := mathieu_radical_three_rank eB
  have step {X : Type} [Group X] [Finite X] (e : S ≃* X)
      (bound : ∀ (P : Subgroup X), IsPGroup 2 P → P ≠ ⊥ →
        ∀ (A : Subgroup X), Group.IsPerfect A →
          A ≤ normalizer (P : Set X) → primeRank 3 A ≤ 1) : False := by
    let A := B.map e.toMonoidHom
    let P := U.map e.toMonoidHom
    let a : B ≃* A := B.equivMapOfInjective e.toMonoidHom e.injective
    have hAn : A ≤ normalizer (P : Set X) := (map_mono hN).trans (U.le_normalizer_map e.toMonoidHom)
    have hPn : P ≠ ⊥ := fun hh => hne ((map_eq_bot_iff_of_injective _ e.injective).mp hh)
    have hb := bound P (hU.map _) hPn A (Group.IsPerfect.ofSurjective
      (f := a.toMonoidHom) a.surjective) hAn
    rw [←primeRank_equiv 3 a] at hb
    omega
  rcases hm with ⟨n,hn,F,_,_,hF,⟨e⟩⟩ | ⟨n,hn,ht⟩ | ⟨m,hm,⟨e⟩⟩
  · let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    apply step e
    intro P hp hpne A hA hAN
    let := hA
    exact Atlas.G2.PerfectSubgroups.perfect_subgroup_two_normalizer_odd_rank_le_one
      P hp hpne (by
        rw [hF]
        exact lt_of_lt_of_le (by decide : 2 < 2^2)
          (Nat.pow_le_pow_right (by decide) hn)) A hAN (by decide : Odd 3)
  · obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff S n (by omega)).mp ht
    apply step e
    intro P hp hpne A hA hAN
    let := hA
    exact Triality.Standard.PerfectTwoNormalizer.perfect_subgroup_two_normalizer_odd_rank_le_one
      n hn P hp hpne A hAN (by decide : Odd 3)
  · apply step e
    intro P hp hpne A hA hAN
    let := hA
    exact ReeF4.ConverseParabolics.perfect_two_normalizer_threeRank_le_one hm A P hp hpne hAN

/-- The image of the full seed's original two-core vanishes in the binary
simple section; no kernel of the full seed is discarded in this assertion. -/
theorem rank_two_seed_core_killed {P S : Type*} [Group P] [Finite P]
    [Group.IsPerfect P] [Group S] [Finite S]
    (hm : RemainingOddLocalRankTwoModel S) (f : P →* S)
    (e : (f.range ⧸ solvableRadical f.range) ≃* M22) :
    pCore 2 P ≤ f.ker := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hN : f.range ≤ normalizer ((pCore 2 P).map f : Set S) := by
    simpa only [normalizer_eq_top,map_top,←MonoidHom.range_eq_map] using
      (pCore 2 P).le_normalizer_map f
  have hz := rank_two_normalized_two_group_eq_bot hm f.range ((pCore 2 P).map f)
    e (pCore_isPGroup.map f) hN
  exact (Subgroup.map_eq_bot_iff _).mp hz

/-- The same literal image is an ordinary quasisimple Mathieu cover once
the source seed's two-core quotient is quasisimple. -/
theorem rank_two_seed_quasisimple {P S : Type*} [Group P] [Finite P]
    [Group.IsPerfect P] [IsQuasisimple (P ⧸ pCore 2 P)] [Group S] [Finite S]
    (hm : RemainingOddLocalRankTwoModel S) (f : P →* S) (hne : f.range ≠ ⊥)
    (e : (f.range ⧸ solvableRadical f.range) ≃* M22) :
    pCore 2 P ≤ f.ker ∧ IsQuasisimple f.range ∧
      Nonempty ((f.range ⧸ center f.range) ≃* M22) := by
  have hk := rank_two_seed_core_killed hm f e
  let : Nontrivial f.range := (nontrivial_iff_ne_bot _).mpr hne
  have hkr : pCore 2 P ≤ f.rangeRestrict.ker := by
    rwa [MonoidHom.ker_rangeRestrict]
  let q := QuotientGroup.lift (pCore 2 P) f.rangeRestrict hkr
  let : IsQuasisimple f.range := IsQuasisimple.of_surjective q
    (QuotientGroup.lift_surjective_of_surjective _ _ f.rangeRestrict_surjective _)
  have hc : solvableRadical f.range = center f.range := le_antisymm
    IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical _ inferInstance (Group.isSolvable_of_comm
      (fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm)))
  exact ⟨hk,inferInstance,⟨(QuotientGroup.quotientMulEquivOfEq hc).symm.trans e⟩⟩
end CFSG.Quasithin.Chapter4.Section04.OddLocalMathieu
