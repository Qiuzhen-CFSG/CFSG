module
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.LargePrimes
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.SmallPrimes
public import Theory.ElementaryAbelian.AutomorphismCardEight

/-!
# Odd actors in the genuine J₁ Sylow normalizer

The action of any odd subgroup of a Sylow two-normalizer on its elementary
Sylow eight is faithful: a nontrivial kernel would contain a prime-order
subgroup whose normalizer contains the full Sylow, contradicting the
certified local bounds. The order 168 of the automorphism group then makes
the odd actor order divide 21. The solvable-overgroup theorem supplies the
normalizer condition in the original paired Cartan application.

Source: GLS3 Table 5.3f; Aschbacher--Smith 5.1.13, printed p.636.
-/

public noncomputable section
open Subgroup
namespace Janko1.LocalStructure

private theorem prime_bounds (p : ℕ) (hp : p.Prime) (ho : Odd p) :
    PrimeNormalizerBound p :=
  primeNormalizerBound_of_cases primeNormalizerBound_three primeNormalizerBound_five
    primeNormalizerBound_seven primeNormalizerBound_eleven primeNormalizerBound_nineteen hp ho

/-- An odd subgroup of a Sylow two-normalizer in J₁ has order dividing 21. -/
theorem odd_normalizer_card_dvd_twenty_one (S : Sylow 2 Model) (E : Subgroup Model)
    (ho : Odd (Nat.card E)) (hn : E ≤ normalizer (S : Set Model)) : Nat.card E ∣ 21 := by
  let f : E →* MulAut S := (S : Subgroup Model).normalizerMonoidHom.comp (Subgroup.inclusion hn)
  have hk : f.ker = ⊥ := by
    by_contra hne
    have hcard : Nat.card f.ker ≠ 1 := fun he => hne (card_eq_one.mp he)
    obtain ⟨p,hp,hpd⟩ := Nat.exists_prime_and_dvd hcard
    have hodd : Odd p := ho.of_dvd_nat (hpd.trans f.ker.card_subgroup_dvd_card)
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨A,hA⟩ := Sylow.exists_subgroup_card_pow_prime (G := f.ker) p (n := 1)
      (by simpa using hpd)
    let g : f.ker →* Model := E.subtype.comp f.ker.subtype
    have hg : Function.Injective g := E.subtype_injective.comp f.ker.subtype_injective
    let R := A.map g
    have hR : Nat.card R = p := by rw [card_map_of_injective hg,hA,pow_one]
    have hc : R ≤ centralizer (S : Set Model) := by
      rintro x ⟨a,_,rfl⟩
      have ha : (⟨(a.val : Model),hn a.val.property⟩ : normalizer (S : Set Model)) ∈
          (S : Subgroup Model).normalizerMonoidHom.ker := a.property
      rwa [normalizerMonoidHom_ker] at ha
    have hSN : (S : Subgroup Model) ≤ normalizer (R : Set Model) :=
      (le_centralizer_iff.mp hc).trans (centralizer_le_normalizer (R : Set Model))
    exact prime_bounds p hp hodd R hR (SylowTwo.card S ▸ card_dvd_of_le hSN)
  have hi : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hk
  let := SylowTwo.elementary S
  have hd : Nat.card E ∣ 168 := (card_mulAut_of_elementary_eight S (SylowTwo.card S)) ▸
    card_dvd_of_injective f hi
  have hcop : Nat.Coprime (Nat.card E) 8 :=
    (Nat.coprime_two_right.mpr ho).pow_right 3
  exact hcop.dvd_of_dvd_mul_right (show Nat.card E ∣ 8 * 21 from hd)

/-- Every odd subgroup in a solvable Sylow overgroup has order dividing 21. -/
theorem odd_solvable_overgroup_card_dvd_twenty_one (S : Sylow 2 Model)
    (J E : Subgroup Model) [Group.IsSolvable J]
    (hSJ : (S : Subgroup Model) ≤ J) (hEJ : E ≤ J) (ho : Odd (Nat.card E)) :
    J ≤ normalizer (S : Set Model) ∧ Nat.card E ∣ 21 := by
  have hn := solvable_overgroup_le_normalizer_of_prime_bounds prime_bounds S J hSJ
  exact ⟨hn,odd_normalizer_card_dvd_twenty_one S E ho (hEJ.trans hn)⟩
end Janko1.LocalStructure
