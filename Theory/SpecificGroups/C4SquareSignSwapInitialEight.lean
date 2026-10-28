module

public import Theory.SpecificGroups.C4SquareSignSwap
public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Normal elementary eights in the sign-and-swap Sylow

An elementary eight in the inverting core, normalized by the whole Sylow,
lies in the extraspecial core and is self-centralizing in the Sylow.
Choose an element outside the abelian base, which has only four involutions.
That element and its conjugates by the two rotations have common centralizer
of order eight. Commutation with its swap conjugate forces the even-parity
condition defining the extraspecial core.

The finite coordinate checks use only the order-64 model, not a subgroup
classification. This is the Sylow geometry in Stellmacher (8.6)(a),
`refs/latex/stellmacher-n-group.tex`.
-/

namespace C4SquareSignSwap

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

private def triple (t : Model) : Set Model :=
  {t, rotation₁ * t * rotation₁⁻¹, rotation₂ * t * rotation₂⁻¹}

private instance (t : Model) : DecidablePred (· ∈ triple t) :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

private instance (t : Model) : DecidablePred (· ∈ Subgroup.centralizer (triple t)) :=
  fun g => decidable_of_iff (∀ x : Model, x ∈ triple t → x * g = g * x)
    Subgroup.mem_centralizer_iff.symm

private theorem base_involutions_card :
    Fintype.card {g : Model // g ∈ base ∧ g ^ 2 = 1} = 4 := by decide +kernel

private theorem even_of_swap_commutes : ∀ t : Model,
    t ∈ inverterCore → t ∉ base →
    t * (swapper * t * swapper⁻¹) = (swapper * t * swapper⁻¹) * t →
    t ∈ extraspecialCore := by decide +kernel

private theorem triple_centralizer_card : ∀ t : Model,
    t ∈ inverterCore → t ∉ base →
    Fintype.card (Subgroup.centralizer (triple t)) = 8 := by decide +kernel

private theorem triple_centralizer_le : ∀ t : Model,
    t ∈ inverterCore → t ∉ base → t ∈ extraspecialCore →
    ∀ g : Model, g ∈ Subgroup.centralizer (triple t) → g ∈ extraspecialCore := by
  decide +kernel

private instance (t : Model) : DecidablePred (· ∈ Subgroup.centralizer ({t} : Set Model)) :=
  fun g => decidable_of_iff (t * g = g * t) (by
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq])

private instance (t : Model) : DecidablePred
    (· ∈ (inverterCore ⊓ Subgroup.centralizer ({t} : Set Model) : Subgroup Model)) :=
  fun g => inferInstanceAs (Decidable (g ∈ inverterCore ∧
    g ∈ Subgroup.centralizer ({t} : Set Model)))

private theorem inverting_centralizer_card : ∀ t : Model,
    t ∈ inverterCore → t ∉ base →
    Fintype.card (inverterCore ⊓ Subgroup.centralizer ({t} : Set Model) : Subgroup Model) = 8 := by
  decide +kernel

/-- An elementary subgroup of the inverting core with more than four elements
has order eight. No normality assumption is needed for this bound. -/
public theorem elementary_inverterCore_card_eight_of_gt_four
    (U : Subgroup Model) [IsElementaryAbelian 2 U]
    (hlarge : 4 < Nat.card U) (hcore : U ≤ inverterCore) : Nat.card U = 8 := by
  have hnbase : ¬ U ≤ base := by
    intro h
    let f : U → {g : Model // g ∈ base ∧ g ^ 2 = 1} :=
      fun u => ⟨u, h u.property, elemPow_eq_one_of_isElementaryAbelian (u : Model) u.property⟩
    have hf : Function.Injective f := by
      intro a b heq
      exact Subtype.ext (congrArg
        (fun x : {g : Model // g ∈ base ∧ g ^ 2 = 1} => x.val) heq)
    have hb := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_fintype_card (α := {g : Model // g ∈ base ∧ g ^ 2 = 1}),
      base_involutions_card] at hb
    omega
  obtain ⟨t, ht, htb⟩ := SetLike.not_le_iff_exists.mp hnbase
  have hUC : U ≤ inverterCore ⊓ Subgroup.centralizer ({t} : Set Model) := by
    apply le_inf hcore
    intro u hu
    apply Subgroup.mem_centralizer_iff.mpr
    intro x hx
    have heq : x = t := hx
    subst x
    exact congrArg Subtype.val ((IsMulCommutative.is_comm (M := U)).comm
      (⟨t, ht⟩ : U) ⟨u, hu⟩)
  have hbound := Subgroup.card_le_of_le hUC
  rw [Nat.card_eq_fintype_card (α := (inverterCore ⊓
    Subgroup.centralizer ({t} : Set Model) : Subgroup Model)),
    inverting_centralizer_card t (hcore ht) htb] at hbound
  have hd := Subgroup.card_dvd_of_le hcore
  rw [card_inverterCore] at hd
  interval_cases hc : Nat.card U <;> norm_num at *

/-- An elementary eight in the inverting core is self-centralizing in that core. -/
public theorem elementary_eight_centralizer_inverterCore
    (U : Subgroup Model) [IsElementaryAbelian 2 U]
    (hcard : Nat.card U = 8) (hcore : U ≤ inverterCore) :
    inverterCore ⊓ Subgroup.centralizer (U : Set Model) = U := by
  have hnbase : ¬ U ≤ base := by
    intro h
    let f : U → {g : Model // g ∈ base ∧ g ^ 2 = 1} :=
      fun u => ⟨u, h u.property, elemPow_eq_one_of_isElementaryAbelian (u : Model) u.property⟩
    have hf : Function.Injective f := by
      intro a b heq
      exact Subtype.ext (congrArg
        (fun x : {g : Model // g ∈ base ∧ g ^ 2 = 1} => x.val) heq)
    have hb := Nat.card_le_card_of_injective f hf
    rw [hcard, Nat.card_eq_fintype_card (α := {g : Model // g ∈ base ∧ g ^ 2 = 1}),
      base_involutions_card] at hb
    omega
  obtain ⟨t, ht, htb⟩ := SetLike.not_le_iff_exists.mp hnbase
  have hbound : inverterCore ⊓ Subgroup.centralizer (U : Set Model) ≤
      inverterCore ⊓ Subgroup.centralizer ({t} : Set Model) :=
    inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ht))
  apply (Subgroup.eq_of_le_of_card_ge
    (le_inf hcore (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance)) ?_).symm
  have hc := Subgroup.card_le_of_le hbound
  rw [Nat.card_eq_fintype_card (α := (inverterCore ⊓
    Subgroup.centralizer ({t} : Set Model) : Subgroup Model)),
    inverting_centralizer_card t (hcore ht) htb] at hc
  simpa only [hcard] using hc

/-- Every Sylow-normal elementary eight in the inverting core lies in the
extraspecial core and is its own centralizer in the order-64 model. -/
public theorem normal_elementary_eight_geometry
    (U : Subgroup Model) [IsElementaryAbelian 2 U]
    (hcard : Nat.card U = 8) (hcore : U ≤ inverterCore) [U.Normal] :
    U ≤ extraspecialCore ∧ Subgroup.centralizer (U : Set Model) = U := by
  have hnbase : ¬ U ≤ base := by
    intro h
    let f : U → {g : Model // g ∈ base ∧ g ^ 2 = 1} :=
      fun u => ⟨u, h u.property, by
        have hp := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p (p := 2) (G := U)) u
        exact congrArg Subtype.val hp⟩
    have hf : Function.Injective f := by
      intro a b heq
      exact Subtype.ext (congrArg (fun x : {g : Model // g ∈ base ∧ g ^ 2 = 1} => x.val) heq)
    have hb := Nat.card_le_card_of_injective f hf
    rw [hcard, Nat.card_eq_fintype_card, base_involutions_card] at hb
    omega
  obtain ⟨t, ht, htb⟩ := SetLike.not_le_iff_exists.mp hnbase
  have hconj (g : Model) : g * t * g⁻¹ ∈ U := Subgroup.Normal.conj_mem inferInstance t ht g
  have hcomm (a b : Model) (ha : a ∈ U) (hb : b ∈ U) : a * b = b * a :=
    congrArg Subtype.val ((IsMulCommutative.is_comm (M := U)).comm
      (⟨a, ha⟩ : U) ⟨b, hb⟩)
  have hte := even_of_swap_commutes t (hcore ht) htb
    (hcomm t _ ht (hconj swapper))
  have htriple : triple t ⊆ (U : Set Model) := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact ht
    · exact hconj rotation₁
    · exact hconj rotation₂
  have hUC : U ≤ Subgroup.centralizer (triple t) := by
    intro u hu
    exact Subgroup.mem_centralizer_iff.mpr (fun x hx => hcomm x u (htriple hx) hu)
  have heq : U = Subgroup.centralizer (triple t) :=
    Subgroup.eq_of_le_of_card_ge hUC (by
      rw [hcard, Nat.card_eq_fintype_card, triple_centralizer_card t (hcore ht) htb])
  refine ⟨?_, le_antisymm ?_ ?_⟩
  · rw [heq]
    exact triple_centralizer_le t (hcore ht) htb hte
  · exact (Subgroup.centralizer_le htriple).trans heq.ge
  · exact Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance

end C4SquareSignSwap
