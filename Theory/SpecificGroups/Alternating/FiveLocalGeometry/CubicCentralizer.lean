module

public import Theory.SpecificGroups.Alternating.FiveLocalGeometry.CubicNormalizer

/-!
# Cubic centralizers in A₅

The centralizer of a subgroup of order three has order three. It lies in
the normalizer of order six, and the normalizer contains an element that
does not centralize the cubic subgroup. This applies through an actual A₅
isomorphism, including the quotient in the J₂ involution centralizer.

Source: Aschbacher, *Sporadic Groups* (1994), the local calculation in
47.3, printed p.262. The argument also occurs in the source-specific
`ThreeLocal.SecondNormalizer.NormalRoot` calculation.
-/

public section
open Subgroup
namespace alternatingGroup.FiveLocalGeometry

/-- A subgroup of order three in an actual A₅ carrier is self-centralizing. -/
theorem cubic_centralizer_card {H : Type*} [Group H] [Finite H]
    (e : H ≃* A5) (P : Subgroup H) (hP : Nat.card P = 3) :
    Nat.card (centralizer (P : Set H)) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  have hPC : P ≤ centralizer (P : Set H) := P.le_centralizer
  have hCN := centralizer_le_normalizer (P : Set H)
  have hn := cubic_normalizer_card e P hP
  have hd := card_dvd_of_le hCN
  rw [hn] at hd
  have hle := Nat.le_of_dvd (by omega : 0 < 6) hd
  have hp := card_dvd_of_le hPC
  rw [hP] at hp
  have hpos : 0 < Nat.card (centralizer (P : Set H)) := Nat.card_pos
  have hne : Nat.card (centralizer (P : Set H)) ≠ 6 := by
    intro hc
    have he := eq_of_le_of_card_ge hCN (by omega)
    obtain ⟨a, ha, x, hx, hm⟩ := exists_noncommuting_normalizer e P hP
    have haC : a ∈ centralizer (P : Set H) := he.symm ▸ ha
    exact hm (haC x hx).symm
  omega

end alternatingGroup.FiveLocalGeometry
