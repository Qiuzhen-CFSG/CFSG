module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.Frattini
public import Theory.GroupAction.KleinFourFactorization.Ambient
/-!
# The reflected cubic-kernel order bound

The genuine reflection and its dihedral conjugator have equal odd fixed-subgroup orders. Brauer–Wielandt and the original involution-centralizer order1152 force the canonical odd kernel to have order nine or81. All reflection marks remain explicit for the independently constructed local dihedral subgroup.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma45.7, printed p.245.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G : Type*} [Group G] [Finite G] {z:G}
namespace IsType
variable (h : IsType z) (X : Subgroup G) (hX : Nat.card X=9) (hXH : X≤centralizer z)
include h hX hXH in
theorem cubic_oddKernel_reflection_count (t s : G)
    (ht : orderOf t=2) (htN : t∈normalizer (X:Set G))
    (hzt : Commute z t) (htz : IsConj z t)
    (hsN : s∈normalizer (X:Set G)) (hst : s*t*s⁻¹=t*z)
    (hXt : Nat.card (X⊓Subgroup.centralizer ({t}:Set G) : Subgroup G)=3) :
    let F := CubicNormalizer.oddKernel X⊓Subgroup.centralizer ({t}:Set G)
    (Nat.card F=3 ∨ Nat.card F=9) ∧ Nat.card (CubicNormalizer.oddKernel X)=Nat.card F^2 := by
  let V := CubicNormalizer.oddKernel X
  let F := V⊓Subgroup.centralizer ({t}:Set G)
  have hodd : Odd (Nat.card V) := CubicNormalizer.oddKernel_odd X
  have hFC : Nat.card F∣Nat.card (Subgroup.centralizer ({t}:Set G)) := card_dvd_of_le inf_le_right
  have hHC : Nat.card (Subgroup.centralizer ({t}:Set G))=1152 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp htz
    have he := (⊤:Subgroup G).card_inf_centralizer_conj g
      (mem_normalizer_iff.mpr (fun _=>by simp) : g∈normalizer (⊤:Subgroup G)) z
    simp only [top_inf_eq,hg] at he
    rw [←he]
    exact h.centralizer_card
  have hFodd : Odd (Nat.card F) := Odd.of_dvd_nat hodd (card_dvd_of_le inf_le_left)
  have hF9 : Nat.card F∣9 := by
    have hh : Nat.card F∣2^7*9 := by
      norm_num only [Nat.reducePow,Nat.reduceMul]
      rwa [hHC] at hFC
    exact (hFodd.coprime_two_right.pow_right 7).dvd_mul_left.mp hh
  have hVZ : V⊓centralizer z=X := h.toCentralizerHypothesis.cubic_oddKernel_fixed X hX hXH
  have hXV : X≤V := hVZ ▸ inf_le_left
  have h3F : 3≤Nat.card F := by
    rw [←hXt]
    exact card_le_of_le (inf_le_inf_right _ hXV)
  have hFc : Nat.card F=3 ∨ Nat.card F=9 := by
    have hh := Nat.mem_divisors.mpr ⟨hF9,(by decide : 9≠0)⟩
    have hd : Nat.divisors 9={1,3,9} := by decide
    simp only [hd,Finset.mem_insert,Finset.mem_singleton] at hh
    omega
  have htV := CubicNormalizer.normalizer_normalizes_oddKernel X htN
  have hsV := CubicNormalizer.normalizer_normalizes_oddKernel X hsN
  have hzX : z∈Subgroup.centralizer (X:Set G) := fun x hx=>mem_centralizer_singleton_iff.mp (hXH hx)
  have hzV := CubicNormalizer.normalizer_normalizes_oddKernel X ((centralizer_le_normalizer _) hzX)
  let a : normalizer (V:Set G) := ⟨z,hzV⟩
  let b : normalizer (V:Set G) := ⟨t,htV⟩
  have ha : a^2=1 := Subtype.ext (by exact h.involution ▸ pow_orderOf_eq_one z)
  have hb : b^2=1 := Subtype.ext (by exact ht ▸ pow_orderOf_eq_one t)
  have hab : Commute a b := Subtype.ext hzt.eq
  have hc := V.card_three_odd_centralizers hodd a b ha hb hab
  change Nat.card V * Nat.card ((V⊓centralizer z)⊓Subgroup.centralizer ({t}:Set G) : Subgroup G)^2 =
    Nat.card (V⊓centralizer z : Subgroup G)*Nat.card F*Nat.card (V⊓Subgroup.centralizer ({z*t}:Set G) : Subgroup G) at hc
  have hs := V.card_inf_centralizer_conj s hsV t
  rw [hst,←hzt.eq] at hs
  rw [hVZ,hXt,hX,←hs] at hc
  change Nat.card V*9=9*Nat.card F*Nat.card F at hc
  refine ⟨hFc,?_⟩
  change Nat.card V=Nat.card F^2
  nlinarith [hc]

include h hX hXH in
theorem cubic_oddKernel_card (t s : G)
    (ht : orderOf t=2) (htN : t∈normalizer (X:Set G))
    (hzt : Commute z t) (htz : IsConj z t)
    (hsN : s∈normalizer (X:Set G)) (hst : s*t*s⁻¹=t*z)
    (hXt : Nat.card (X⊓Subgroup.centralizer ({t}:Set G) : Subgroup G)=3) :
    Nat.card (CubicNormalizer.oddKernel X)=9 ∨ Nat.card (CubicNormalizer.oddKernel X)=81 := by
  obtain ⟨hf,hcard⟩ := h.cubic_oddKernel_reflection_count X hX hXH t s ht htN hzt htz hsN hst hXt
  rcases hf with hf | hf
  · left; rw [hcard,hf]; norm_num
  · right; rw [hcard,hf]; norm_num

end IsType
end Theory.GroupTheory.Recognition.UnitaryFourThree
