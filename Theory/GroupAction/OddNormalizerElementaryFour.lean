module
public import Theory.GroupAction.OddInvariantSylowConjugacy.Ambient
public import Theory.GroupAction.FiveThirtyTwoCentralizer
public import Theory.GroupTheory.ElementaryThirtyTwoFiveSevenCores
public import Theory.GroupTheory.ElementaryThirtyTwoThirtyOneNormalizer
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse
public import Theory.ElementaryAbelian.Quotient
public import Mathlib.RingTheory.IntegralDomain

/-!
# Odd subgroups normalized by a four-group in binary degree four or five

Let an elementary four-group normalize an odd-order subgroup X of a
faithful binary linear group in degree four or five. Two-group orbit
counting supplies invariant Sylow subgroups of X. The checked normalizer
bounds exclude seven and thirty-one. For five, the centralizer has odd
order, so conjugation would embed the four-group in the cyclic group
Aut(C5), a contradiction. The remaining order divides nine; the binary
degree bound excludes order-nine elements, making X elementary abelian.

Adjoining a fixed line reduces degree four to degree five. No solvability
hypothesis on X is needed. The source application is the odd-core step
of Aschbacher--Smith, original 12.2.25, printed p.806. The small normalizer
bounds are the calculations recorded in Parrott (1972), printed p.673,
and the coprime five-centralizer calculation in the imported modules.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupAction
variable {G E : Type*} [Group G] [Finite G] [Group E] [Finite E]
  [IsElementaryAbelian 2 E]

/-- A four-group normalizing an odd subgroup in GL(5,2) forces the odd
subgroup's order to divide nine. The invariant Sylow argument uses no
solvability assumption. -/
theorem odd_card_dvd_nine
    (ρ : G →* MulAut E) (hρ : Function.Injective ρ) (hE : Nat.card E = 32)
    (S X : Subgroup G) [IsElementaryAbelian 2 S] (hS : Nat.card S = 4)
    (hX : Odd (Nat.card X)) (hSX : S ≤ normalizer (X : Set G)) :
    Nat.card X ∣ 9 := by
  let : MulDistribMulAction G E := MulDistribMulAction.compHom E ρ
  let : FaithfulSMul G E := ⟨by
    intro a b hab
    apply hρ
    ext e
    exact hab e⟩
  have hAut : Nat.card (MulAut E) = 9999360 := by
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow E 5 (by simpa using hE)]
    decide
  have hd : Nat.card X ∣ 9765 := by
    have hh := X.card_subgroup_dvd_card.trans (card_dvd_of_injective ρ hρ)
    rw [hAut] at hh
    exact (hX.coprime_two_right.pow_right 10).dvd_of_dvd_mul_left hh
  have htwo : IsPGroup 2 S := IsPGroup.of_card (n := 2) hS
  have hprime (p : ℕ) [Fact p.Prime] (hp : p = 5 ∨ p = 7 ∨ p = 31)
      (hpX : p ∣ Nat.card X) :
      ∃ A : Subgroup G, Nat.card A = p ∧ S ≤ normalizer (A : Set G) := by
    obtain ⟨Q,hSQ,_⟩ := Theory.GroupAction.exists_invariant_sylow_ambient_fixed_control
      X S hX htwo hSX p
    obtain ⟨n,hn⟩ := Q.isPGroup'.exists_card_eq
    have hn0 : n ≠ 0 := by
      intro he
      have hh := Q.dvd_card_of_dvd_card hpX
      rw [hn,he,pow_zero] at hh
      exact (Fact.out : p.Prime).not_dvd_one hh
    have hn2 : ¬ 2 ≤ n := by
      intro he
      have hh : p ^ 2 ∣ 9765 := (pow_dvd_pow p he).trans
        (hn ▸ Q.card_subgroup_dvd_card.trans hd)
      rcases hp with rfl | rfl | rfl <;> norm_num at hh
    have hn1 : n = 1 := by omega
    refine ⟨(Q : Subgroup X).map X.subtype, ?_,hSQ⟩
    rw [card_map_of_injective X.subtype_injective,hn,hn1,pow_one]
  have hfive : ¬ 5 ∣ Nat.card X := by
    intro hx
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    obtain ⟨A,hA,hSA⟩ := hprime 5 (Or.inl rfl) hx
    have hC := Subgroup.FiveThirtyTwo.centralizer_card_dvd_fifteen (V := E) A hA hE
    have hdis : Disjoint S (centralizer (A : Set G)) :=
      disjoint_of_coprime_natCard (by
        rw [hS]
        exact (show Nat.Coprime 4 15 by decide).of_dvd_right hC)
    let f : S →* MulAut A := A.normalizerMonoidHom.comp (inclusion hSA)
    have hf : Function.Injective f := by
      apply (injective_iff_map_eq_one f).mpr
      intro s hs
      apply Subtype.ext
      apply disjoint_def.mp hdis s.property
      have hk : inclusion hSA s ∈ A.normalizerMonoidHom.ker := hs
      rwa [normalizerMonoidHom_ker] at hk
    let : IsCyclic A := isCyclic_of_prime_card hA
    let e : MulAut A ≃* (ZMod 5)ˣ := by
      have he := IsCyclic.mulAutMulEquiv A
      rw [hA] at he
      exact he
    let : IsCyclic (MulAut A) := isCyclic_of_injective e.toMonoidHom e.injective
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) hS
      (isCyclic_of_injective f hf)
  have hseven : ¬ 7 ∣ Nat.card X := by
    intro hx
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    obtain ⟨A,hA,hSA⟩ := hprime 7 (Or.inr (Or.inl rfl)) hx
    have hnorm : S.map ρ ≤ normalizer (A.map ρ : Set (MulAut E)) :=
      (map_mono hSA).trans (A.le_normalizer_map ρ)
    have hA' : Nat.card (A.map ρ) = 7 := (card_map_of_injective hρ).trans hA
    have hS' : Nat.card (S.map ρ) = 4 := (card_map_of_injective hρ).trans hS
    exact not_four_dvd_card_normalizer_of_elementary_thirtytwo_seven hE (A.map ρ) hA'
      (hS' ▸ card_dvd_of_le hnorm)
  have hthirtyone : ¬ 31 ∣ Nat.card X := by
    intro hx
    let : Fact (Nat.Prime 31) := ⟨by decide⟩
    obtain ⟨A,hA,hSA⟩ := hprime 31 (Or.inr (Or.inr rfl)) hx
    have hnorm : S.map ρ ≤ normalizer (A.map ρ : Set (MulAut E)) :=
      (map_mono hSA).trans (A.le_normalizer_map ρ)
    have hA' : Nat.card (A.map ρ) = 31 := (card_map_of_injective hρ).trans hA
    have hS' : Nat.card (S.map ρ) = 4 := (card_map_of_injective hρ).trans hS
    have hh := odd_card_normalizer_of_elementary_thirtytwo_thirtyone E hE (A.map ρ) hA'
    exact hh.not_two_dvd_nat ((by decide : 2 ∣ 4).trans (hS' ▸ card_dvd_of_le hnorm))
  have hcop : Nat.Coprime (Nat.card X) (5 * 7 * 31) := by
    exact (((Nat.coprime_comm.mpr ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr hfive)).mul_right
      (Nat.coprime_comm.mpr ((by decide : Nat.Prime 7).coprime_iff_not_dvd.mpr hseven))).mul_right
      (Nat.coprime_comm.mpr ((by decide : Nat.Prime 31).coprime_iff_not_dvd.mpr hthirtyone)))
  exact hcop.dvd_of_dvd_mul_right hd



/-- Adjoining a fixed line includes the degree-four case. -/
theorem odd_card_dvd_nine_of_card_sixteen_or_thirtytwo
    (ρ : G →* MulAut E) (hρ : Function.Injective ρ)
    (hE : Nat.card E = 16 ∨ Nat.card E = 32)
    (S X : Subgroup G) [IsElementaryAbelian 2 S] (hS : Nat.card S = 4)
    (hX : Odd (Nat.card X)) (hSX : S ≤ normalizer (X : Set G)) :
    Nat.card X ∣ 9 := by
  rcases hE with hE | hE
  · let F := E × Multiplicative (ZMod 2)
    let : IsElementaryAbelian 2 F := {
      toIsMulCommutative := inferInstance
      exponent_dvd_p := by
        rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
        rintro ⟨e,x⟩
        apply Prod.ext
        · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
            (IsElementaryAbelian.exponent_dvd_p 2 E) e
        · change (2 : ℕ) • x.toAdd = 0
          rw [nsmul_eq_mul]
          change (2 : ZMod 2) * x.toAdd = 0
          rw [show (2 : ZMod 2) = 0 by decide,zero_mul] }
    let σ : G →* MulAut F := {
      toFun g := (ρ g).prodCongr (MulEquiv.refl _)
      map_one' := by
        apply MulEquiv.ext
        rintro ⟨e,x⟩
        change (ρ 1 e,x) = (e,x)
        rw [map_one]
        rfl
      map_mul' a b := by
        apply MulEquiv.ext
        rintro ⟨e,x⟩
        change (ρ (a*b) e,x) = (ρ a (ρ b e),x)
        rw [map_mul]
        rfl }
    have hσ : Function.Injective σ := by
      intro a b he
      apply hρ
      ext e
      exact congrArg (fun f : MulAut F => (f (e,1)).1) he
    apply odd_card_dvd_nine σ hσ ?_ S X hS hX hSX
    change Nat.card (E × Multiplicative (ZMod 2)) = 32
    rw [Nat.card_prod,hE]
    change 16 * Nat.card (ZMod 2) = 32
    rw [Nat.card_zmod]
  · exact odd_card_dvd_nine ρ hρ hE S X hS hX hSX

/-- The odd subgroup is elementary abelian, including the trivial case. -/
theorem odd_elementary_of_card_sixteen_or_thirtytwo
    (ρ : G →* MulAut E) (hρ : Function.Injective ρ)
    (hE : Nat.card E = 16 ∨ Nat.card E = 32)
    (S X : Subgroup G) [IsElementaryAbelian 2 S] (hS : Nat.card S = 4)
    (hX : Odd (Nat.card X)) (hSX : S ≤ normalizer (X : Set G)) :
    IsElementaryAbelian 3 X := by
  have hd := odd_card_dvd_nine_of_card_sixteen_or_thirtytwo ρ hρ hE S X hS hX hSX
  let A := X.map ρ
  have hA : Nat.card A ∣ 9 := by rw [card_map_of_injective hρ]; exact hd
  let : IsElementaryAbelian 3 A :=
    SmallNonabelianTwoGroup.elementaryAbelian_of_card_dvd_nine
      (IsElementaryAbelian.isPGroup 2 E) (by rcases hE with hE | hE <;> omega) A hA
  let e := X.equivMapOfInjective ρ hρ
  exact IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective

end Theory.GroupAction
