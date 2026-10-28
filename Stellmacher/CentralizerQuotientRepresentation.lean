module

public import Theory.Representation.NormalElementaryQuotient
public import Stellmacher.MaxElementaryOffender

/-!
# Maximum elementary subgroups as binary offenders

The fixed vectors of the genuine centralizer-quotient representation are
identified with the relative centralizer. The maximum-elementary-subgroup
counting bound then gives the fixed-space codimension inequality. A Thompson
subgroup with nontrivial image therefore supplies an actual FF-offender.

This extends the cardinal argument of `Stellmacher.MaxElementaryOffender` to
the binary representation API. Source: Aschbacher–Smith, *The Classification
of Quasithin Groups*, B.2.4 and the final proof of Theorem 15.3.1, combined
manuscript (1 March 2004), printed pp.75–76 and 1155.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

namespace Representation.NormalElementaryQuotient

variable {G H : Type*} [Group G] [Group H]
  (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
  (q : G →* H) (hq : Function.Surjective q)
  (hker : q.ker = centralizer (V : Set G))

variable [Finite G] [Finite H]

/-- A maximum elementary subgroup with nontrivial image is an FF-offender. -/
theorem maxElementary_isOffender (S A : Subgroup G) (hVS : V ≤ S)
    (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups S) (hne : ¬ A ≤ q.ker) :
    IsOffender (representation V q hq hker) (A.map q) := by
  let _ : IsElementaryAbelian 2 A := hA.2.1
  let _ : IsElementaryAbelian 2 (A.map q) := IsElementaryAbelian.map q
  refine ⟨⟨fun h => hne ((Subgroup.map_eq_bot_iff A).mp h), inferInstance⟩, ?_⟩
  have hc := Stellmacher.maxElementary_card_le_fixed_mul_image S V A hVS hA q hker
  rw [← Nat.card_congr (fixedSpaceEquiv V q hq hker A)] at hc
  have hVcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
  have hFcard := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace (representation V q hq hker) (A.map q))
  rw [Nat.card_zmod] at hVcard hFcard
  have hAcard : Nat.card (A.map q) = 2 ^ rank (A.map q) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 (A.map q)).exists_card_eq
    unfold rank
    rw [hn, Nat.log_pow (by decide : 1 < 2)]
  change Nat.card (Additive V) ≤ _ at hc
  rw [hVcard, hFcard, hAcard, ← pow_add] at hc
  have hd := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  have hr := fixedCodim_add_finrank (representation V q hq hker) (A.map q)
  omega

/-- A Thompson subgroup acting nontrivially supplies an actual FF-offender. -/
theorem isFFModule_of_thompson_not_le (S : Subgroup G) (hVS : V ≤ S)
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ S ≤ q.ker) :
    IsFFModule (representation V q hq hker) := by
  classical
  have h : ∃ A ∈ Stellmacher.elementaryAbelianMaxSubgroups S, ¬ A ≤ q.ker := by
    by_contra! h
    exact hJ (sSup_le h)
  obtain ⟨A, hA, hne⟩ := h
  exact ⟨A.map q, maxElementary_isOffender V q hq hker S A hVS hA hne⟩

end Representation.NormalElementaryQuotient
