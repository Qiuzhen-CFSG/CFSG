module
public import Stellmacher.CentralizerQuotientRepresentation
public import Stellmacher.MaxElementaryOffenderEquality
public import Stellmacher.ElementaryAbelianMaxOrderSpecification

/-!
# Strong offenders or centralizing maximum replacements

For a normal elementary two-subgroup V contained in S, a maximum elementary
subgroup A either induces a strong offender on V or admits a maximum
replacement centralizing V. If the usual offender inequality is an equality,
V C_A(V) is the required replacement. The action is the literal quotient by
the centralizer of V, including its original kernel.

Source: the equality case of Aschbacher--Smith B.2.4, combined manuscript
of 1 March 2004, printed pp.75--76. The Section12.6 consumer uses this
alternative to compare the two-ranks of T and its nonsingular centralizer.
-/

public section
open Subgroup Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative

namespace Representation.NormalElementaryQuotient
variable {G F : Type*} [Group G] [Group F] [Finite G] [Finite F]

theorem maxElementary_strong_or_centralizer
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* F) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (S A : Subgroup G) (hVS : V ≤ S)
    (hA : A ∈ elementaryAbelianMaxSubgroups S) :
    IsStrongOffender (representation V q hq hker) (A.map q) ∨
      ∃ B ∈ elementaryAbelianMaxSubgroups S, B ≤ centralizer (V : Set G) := by
  by_cases hAk : A ≤ q.ker
  · exact .inr ⟨A,hA,hker ▸ hAk⟩
  let ρ := representation V q hq hker
  have hoff := maxElementary_isOffender V q hq hker S A hVS hA hAk
  by_cases hstrong : IsStrongOffender ρ (A.map q)
  · exact .inl hstrong
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  have hd : fixedCodim ρ (A.map q) = rank (A.map q) := by
    have hn : ¬ fixedCodim ρ (A.map q) < rank (A.map q) := fun h => hstrong ⟨hoff.1,h⟩
    exact le_antisymm hoff.2 (Nat.le_of_not_gt hn)
  have heq : Nat.card V = Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G) *
      Nat.card (A.map q) := by
    rw [←Nat.card_congr (fixedSpaceEquiv V q hq hker A)]
    have hVcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    have hFcard := Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := fixedSpace ρ (A.map q))
    have hAcard : Nat.card (A.map q) = 2 ^ rank (A.map q) := by
      obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 (A.map q)).exists_card_eq
      rw [rank,hn,Nat.log_pow (by decide : 1 < 2)]
    change Nat.card (Additive V) = _
    rw [hVcard,hFcard,Nat.card_zmod,hAcard,←pow_add]
    congr 1
    have hh := fixedCodim_add_finrank ρ (A.map q)
    omega
  have hm := (maxElementary_card_bound_and_eq S V A hVS hA.1 0
    (by simpa only [pow_zero,mul_one] using elementaryAbelianMaxSubgroups_card_eq S A hA)
    q hker).2 (by simpa only [pow_zero,mul_one] using heq)
  exact .inr ⟨_,hm,sup_le (le_centralizer_iff_isMulCommutative.mpr inferInstance) inf_le_right⟩
end Representation.NormalElementaryQuotient
