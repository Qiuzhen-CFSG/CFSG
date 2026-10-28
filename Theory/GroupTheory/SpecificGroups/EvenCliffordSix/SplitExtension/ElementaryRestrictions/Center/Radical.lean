module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions.Center.Reduction
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions.Center.Radical.Transport
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SplitExtension.ElementaryRestrictions.Center.Radical.Counting

/-!
# The radical branch of the center count

Normalize a noncentral radical vector to a two-letter vector, up to a central
volume factor. The signed permutation automorphism preserves squares, signed
commutation and both literal mixed coordinate equations. The normalized count
therefore bounds the original candidates by 48.

Consequently a subgroup of order 64, whose squares lie in the sign subgroup and
which contains an element with nontrivial actor, cannot be centralized by a
noncentral radical element. This discharges the radical counting premise of
`center_eq_centralIn_of_counts`; the nonradical branch is independent.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.2.2(6a),
printed pp.410 and 412 (PDF pp.421 and 423), the quartic split-extension calculation.
-/

@[expose] public section
namespace EvenCliffordSix.SplitExtension.ElementaryRestrictions
open Subgroup

/-- The two signs and 24 normalized actor-vector pairs bound the literal mixed
candidate set. -/
theorem mixedCandidates_card_le (m : Model) (x : SplitExtension)
    (hm : m ∉ center Model) (hx : x ^ 2 ∈ sign) (hr : x.right ≠ 1)
    (hc : Commute (radicalEmbedding m) x) :
    Nat.card (mixedCandidates m x) ≤ 48 := by
  obtain ⟨p, hp⟩ := Radical.exists_normalized_centralizer m hm
  have hxx := Radical.transport_mixed p m x x ⟨hx, hc, rfl, rfl⟩
  have hr' : (Radical.transport p x).right ≠ 1 := by
    intro h
    apply hr
    apply (Radical.actorConj p).injective
    exact h.trans (map_one (Radical.actorConj p)).symm
  let f (y : mixedCandidates m x) :
      mixedCandidates Structure.leftA (Radical.transport p x) :=
    let hy := Radical.transport_mixed p m x y.val y.property
    ⟨Radical.transport p y.val, hy.1, (hp _).mp hy.2.1, hy.2.2⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply (Radical.transport p).injective
    exact congrArg Subtype.val hab
  exact (Nat.card_le_card_of_injective f hinj).trans
    (Radical.canonical_card_le (Radical.transport p x) hxx.1 hr' ((hp _).mp hxx.2.1))

/-- The independent radical counting estimate required by the center assembly. -/
theorem mixedCandidates_card_lt (m : Model) (x : SplitExtension)
    (hm : m ∉ center Model) (hx : x ^ 2 ∈ sign) (hr : x.right ≠ 1)
    (hc : Commute (radicalEmbedding m) x) :
    Nat.card (mixedCandidates m x) < 64 :=
  lt_of_le_of_lt (mixedCandidates_card_le m x hm hx hr hc) (by decide)

/-- Actual subgroup application: order 64 and the square bound force every
centralizing radical element to belong to the center of the Clifford model,
provided the subgroup contains a nontrivial actor. -/
theorem radical_mem_center_of_centralizes_of_actor_ne_one
    (H : Subgroup SplitExtension) (hcard : Nat.card H = 64)
    (hsq : ∀ y ∈ H, y ^ 2 ∈ sign) (m : Model) (x : SplitExtension)
    (hx : x ∈ H) (hr : x.right ≠ 1)
    (hc : ∀ y ∈ H, Commute (radicalEmbedding m) y) :
    m ∈ center Model := by
  by_contra hm
  have hlo := card_le_mixedCandidates H hsq m x hx hc
  have hhi := mixedCandidates_card_lt m x hm (hsq x hx) hr (hc x hx)
  omega

end EvenCliffordSix.SplitExtension.ElementaryRestrictions
