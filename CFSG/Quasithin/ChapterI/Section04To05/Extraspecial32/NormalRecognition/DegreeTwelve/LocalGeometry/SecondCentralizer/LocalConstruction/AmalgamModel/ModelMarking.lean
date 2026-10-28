module
public import CFSG.Quasithin.ChapterI.Section04To05.Extraspecial32.NormalRecognition.DegreeTwelve.LocalGeometry.SecondCentralizer.ModelTypes
public import Theory.ElementaryAbelian.Basic

/-!
# Intrinsic markings in the product model

A normal elementary subgroup of order four which omits the central
involution is the canonical Klein four in the symmetric factor. Its
involutions must be even, since their conjugates commute; a nontrivial
central coordinate would put the central involution in their normal
closure. Thus every isomorphism carrying the source four-group to such a
subgroup has the required first-class marking. The remaining involutions
are either central translates of that four-group or conjugates of an odd
involution and its central translate.

The permutation facts are checked on S₄ itself. Cardinality uses the
product equivalence and counts only its four-element permutation subgroup.
Source: Aschbacher, “A 2-local characterization of M12”, Illinois J. Math.
47 (2003), 31–47, the opening of Lemma 4.2, p.39.
-/

namespace CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer.Amalgam
open Subgroup

private abbrev P4 := Equiv.Perm (Fin 4)

set_option maxRecDepth 4096 in
private def evenFour : Subgroup P4 where
  carrier := {p | p ^ 2 = 1 ∧ Equiv.Perm.sign p = 1}
  one_mem' := by decide +kernel
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

private instance : DecidablePred (· ∈ evenFour) :=
  fun p => inferInstanceAs (Decidable (p ^ 2 = 1 ∧ Equiv.Perm.sign p = 1))

public def modelFour : Subgroup (Model 4) :=
  (⊥ : Subgroup (Multiplicative (ZMod 2))).prod evenFour

public theorem modelFour_mem (x : Model 4) :
    x ∈ modelFour ↔ x.1 = 1 ∧ x.2 ^ 2 = 1 ∧ Equiv.Perm.sign x.2 = 1 := Iff.rfl

public theorem modelFour_card : Nat.card modelFour = 4 := by
  change Nat.card ((⊥ : Subgroup (Multiplicative (ZMod 2))).prod evenFour) = 4
  rw [Nat.card_congr ((⊥ : Subgroup (Multiplicative (ZMod 2))).prodEquiv evenFour).toEquiv,
    Nat.card_prod, card_bot, one_mul, Nat.card_eq_fintype_card]
  decide +kernel

public theorem modelFour_first (x : Model 4) :
    FirstClass x ↔ x ∈ modelFour ∧ x ≠ 1 := by
  rw [FirstClass, modelFour_mem, orderOf_eq_prime_iff]
  constructor
  · rintro ⟨⟨hp, hn⟩, hx, hs⟩
    exact ⟨⟨hx, congrArg Prod.snd hp, hs⟩, hn⟩
  · rintro ⟨⟨hx, hp, hs⟩, hn⟩
    exact ⟨⟨Prod.ext (by simp [hx]) hp, hn⟩, hx, hs⟩

set_option maxRecDepth 4096 in
private theorem involution_commuting_conjugates_even : ∀ s : P4,
    s ^ 2 = 1 → (∀ p : P4, (s * (p * s * p⁻¹)) ^ 2 = 1) → Equiv.Perm.sign s = 1 := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem even_involution_three_conjugates : ∀ s : P4,
    s ^ 2 = 1 → Equiv.Perm.sign s = 1 →
      ∃ p q : P4, s * (p * s * p⁻¹) * (q * s * q⁻¹) = 1 := by
  decide +kernel

set_option maxRecDepth 4096 in
private theorem odd_involutions_conjugate : ∀ s u : P4,
    s ^ 2 = 1 → Equiv.Perm.sign s = -1 → u ^ 2 = 1 → Equiv.Perm.sign u = -1 →
      ∃ p : P4, p * s * p⁻¹ = u := by
  decide +kernel

public theorem model_central_unique {x : Model 4} (hx : x ∈ center (Model 4))
    (hx1 : x ≠ 1) : x = centralInvolution 4 := by
  have check : ∀ x : Model 4, (∀ y : Model 4, y * x = x * y) →
      x ≠ 1 → x = centralInvolution 4 := by decide +kernel
  exact check x (mem_center_iff.mp hx) hx1

public theorem model_central_ne_one : centralInvolution 4 ≠ 1 := by decide +kernel

/-- A normal elementary four disjoint from the central involution is forced
onto the canonical three even involutions. -/
public theorem normal_four_eq_modelFour (U : Subgroup (Model 4)) [U.Normal]
    [IsElementaryAbelian 2 U] (hcard : Nat.card U = 4)
    (ht : centralInvolution 4 ∉ U) : U = modelFour := by
  apply eq_of_le_of_card_ge ?_ (by rw [modelFour_card, hcard])
  intro x hx
  have hx2 : x ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian x hx
  have hs : Equiv.Perm.sign x.2 = 1 := by
    apply involution_commuting_conjugates_even x.2 (congrArg Prod.snd hx2)
    intro p
    have hm := U.mul_mem hx ((inferInstance : U.Normal).conj_mem x hx (1, p))
    exact congrArg Prod.snd (elemPow_eq_one_of_isElementaryAbelian _ hm)
  have hxC : x.1 = 1 := by
    by_contra hne
    obtain ⟨p, q, hpq⟩ := even_involution_three_conjugates x.2 (congrArg Prod.snd hx2) hs
    have he : x * ((1, p) * x * (1, p)⁻¹) * ((1, q) * x * (1, q)⁻¹) =
        centralInvolution 4 := by
      apply Prod.ext
      · have hc : ∀ c : Multiplicative (ZMod 2), c ≠ 1 →
            c * c * c = Multiplicative.ofAdd 1 := by decide +kernel
        simpa [centralInvolution] using hc x.1 hne
      · exact hpq
    apply ht
    rw [← he]
    exact U.mul_mem (U.mul_mem hx ((inferInstance : U.Normal).conj_mem x hx (1, p)))
      ((inferInstance : U.Normal).conj_mem x hx (1, q))
  exact (modelFour_mem x).mpr ⟨hxC, congrArg Prod.snd hx2, hs⟩

/-- The even involutions lie in V or its central translate. -/
public theorem even_involution_plane_or_translate {x : Model 4} (hx : x ^ 2 = 1)
    (hs : Equiv.Perm.sign x.2 = 1) :
    x ∈ modelFour ∨ centralInvolution 4 * x ∈ modelFour := by
  have hc : ∀ c : Multiplicative (ZMod 2), c = 1 ∨ Multiplicative.ofAdd 1 * c = 1 := by
    decide +kernel
  rcases hc x.1 with h1 | h1
  · exact Or.inl ((modelFour_mem x).mpr ⟨h1, congrArg Prod.snd hx, hs⟩)
  · apply Or.inr
    rw [modelFour_mem]
    simpa [centralInvolution] using And.intro h1 (And.intro (congrArg Prod.snd hx) hs)

/-- The two remaining involution classes are represented by any odd
involution and its central translate. -/
public theorem odd_involution_classes {r x : Model 4}
    (hr : r ^ 2 = 1) (hrsign : Equiv.Perm.sign r.2 = -1)
    (hx : x ^ 2 = 1) (hxsign : Equiv.Perm.sign x.2 = -1) :
    IsConj r x ∨ IsConj (centralInvolution 4 * r) x := by
  obtain ⟨p, hp⟩ := odd_involutions_conjugate r.2 x.2 (congrArg Prod.snd hr) hrsign
    (congrArg Prod.snd hx) hxsign
  have hc : ∀ a b : Multiplicative (ZMod 2), a = b ∨ Multiplicative.ofAdd 1 * a = b := by
    decide +kernel
  rcases hc r.1 x.1 with he | he
  · exact Or.inl (isConj_iff.mpr ⟨(1, p), Prod.ext (by simpa using he) hp⟩)
  · apply Or.inr
    apply isConj_iff.mpr
    refine ⟨(1, p), Prod.ext (by simpa [centralInvolution] using he) ?_⟩
    simpa [centralInvolution] using hp

end CFSG.Quasithin.Extraspecial32.DegreeTwelve.SecondCentralizer.Amalgam
