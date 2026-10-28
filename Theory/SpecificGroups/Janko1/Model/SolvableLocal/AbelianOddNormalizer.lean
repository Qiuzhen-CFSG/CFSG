module
public import Theory.SpecificGroups.Janko1.Model.SolvableLocal.OddNormalizer
public import Theory.GroupAction.BinarySingerRegularity
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import Mathlib.Data.Nat.Squarefree

/-!
# Abelian odd actors in the J₁ Sylow normalizer

An odd actor acts faithfully on the elementary Sylow eight: a prime subgroup
of a nontrivial kernel would contradict the certified prime normalizer bounds.
An abelian odd actor has squarefree order dividing 21, hence is cyclic. Its
faithful binary action has a free orbit, bounding its order by eight.

This eliminates the commuting seven-part in the paired J₁ argument of
Aschbacher--Smith 5.1.13, printed p.636 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Janko1.LocalStructure

/-- The literal conjugation action of an odd Sylow-normalizer subgroup is faithful. -/
theorem odd_normalizer_action_injective (S : Sylow 2 Model) (E : Subgroup Model)
    (ho : Odd (Nat.card E)) (hn : E ≤ normalizer (S : Set Model)) :
    Function.Injective ((S : Subgroup Model).normalizerMonoidHom.comp (Subgroup.inclusion hn)) := by
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
    exact (primeNormalizerBound_of_cases primeNormalizerBound_three primeNormalizerBound_five
      primeNormalizerBound_seven primeNormalizerBound_eleven primeNormalizerBound_nineteen hp hodd) R hR (SylowTwo.card S ▸ card_dvd_of_le hSN)
  exact (MonoidHom.ker_eq_bot_iff f).mp hk


/-- An abelian odd subgroup of a Sylow two-normalizer has order at most eight. -/
theorem abelian_odd_normalizer_card_le_eight (S : Sylow 2 Model) (E : Subgroup Model)
    [IsMulCommutative E] (ho : Odd (Nat.card E))
    (hn : E ≤ normalizer (S : Set Model)) : Nat.card E ≤ 8 := by
  have hd := odd_normalizer_card_dvd_twenty_one S E ho hn
  have hs : Squarefree (21 : ℕ) :=
    (Nat.squarefree_mul (by decide : Nat.Coprime 3 7)).mpr
      ⟨Nat.prime_three.squarefree, (by decide : Nat.Prime 7).squarefree⟩
  let : IsZGroup E := IsZGroup.of_squarefree (hs.squarefree_of_dvd hd)
  let : IsCyclic E := inferInstance
  let := SylowTwo.elementary S
  obtain ⟨v,hv⟩ := Theory.GroupAction.faithful_cyclic_odd_binary_exists_free_orbit
    ((S : Subgroup Model).normalizerMonoidHom.comp (Subgroup.inclusion hn))
    (odd_normalizer_action_injective S E ho hn) ho
  exact (Nat.card_le_card_of_injective _ hv).trans_eq (SylowTwo.card S)
end Janko1.LocalStructure
