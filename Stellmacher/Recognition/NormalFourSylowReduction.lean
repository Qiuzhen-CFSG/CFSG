module

public import Stellmacher.Recognition.RankTwoSylowReduction
public import Stellmacher.Recognition.LyonsU3Four.Basic
public import Theory.GroupTheory.PGroup.RankTwoFour

/-!
# Checked interfaces for the normal-four Sylow branch

The source handles an abelian Sylow first, then a nonabelian Sylow whose
center's first omega subgroup has order four, and finally the case
with a unique central involution. The first case retains the dihedral
alternative; a normal elementary four-group does not rule it out.

This module proves the elementary-four conclusion and the precise bridge
between the rank-two Lyons predicate and Lyons's full intrinsic hypothesis.
The latter bridge uses the ambient elementary rank bound to show that every
involution lies in the elementary center of order four. Thus the omitted
omega equality is proved, rather than dropped from Lyons's theorem.

The ambient normal-four classification itself still requires the abelian
Sylow, central-four, and cyclic-center arguments in Janko–Thompson, Math. Z.
113 (1970), §§3–6, pp.389–396. These are not assumed as fields of a recognition
predicate here. The exact case ordering and the odd-core quotient in Lemma
4.1 are recorded in `refs/original/n-group-global/odd-core-rank-two-source/
normal-four-case-split.md`. The intrinsic interface is Lyons, Trans. AMS 164
(1972), Theorem 2, p.372.
-/

namespace Stellmacher.Recognition

/-- Under the ambient rank bound the rank-two Lyons predicate supplies every
hypothesis of Lyons's Theorem 2, including the first omega equality. -/
public theorem IsLyonsSylow.sylowStructure_of_elementary_card_lt_eight
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (hS : IsLyonsSylow S) : LyonsU3Four.SylowStructure S := by
  obtain ⟨Z, hc, hZ, hd, hf, hs, he, hfour⟩ := (isLyonsSylow_iff S).mp hS
  subst Z
  let : IsElementaryAbelian 2 (Subgroup.center S) := he
  exact {
    card := hc
    center_eq_commutator := hd
    center_eq_frattini := hf
    center_eq_omega := (Subgroup.omega_one_eq_of_central_four_of_elementary_card_lt_eight
      (Subgroup.elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G))
      (Subgroup.center S) hfour le_rfl).symm
    center_eq_squares := hs
    center_card := hfour
    center_elementary := he }

/-- Lyons's full intrinsic structure implies the rank-two interface predicate. -/
public theorem LyonsU3Four.SylowStructure.isLyonsSylow
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (hS : LyonsU3Four.SylowStructure S) : IsLyonsSylow S :=
  (isLyonsSylow_iff S).mpr ⟨Subgroup.center S, hS.card, rfl, hS.center_eq_commutator,
    hS.center_eq_frattini, hS.center_eq_squares, hS.center_elementary, hS.center_card⟩

/-- The two Lyons interfaces agree under the ambient elementary rank bound. -/
public theorem isLyonsSylow_iff_sylowStructure_of_elementary_card_lt_eight
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8) :
    IsLyonsSylow S ↔ LyonsU3Four.SylowStructure S :=
  ⟨fun h => h.sylowStructure_of_elementary_card_lt_eight S hrank,
    fun h => h.isLyonsSylow⟩

/-- An elementary group of order four lies in the dihedral alternative. -/
public theorem rank_two_sylow_alternative_of_elementary_card_four
    {S : Type*} [Group S] [Finite S] [IsElementaryAbelian 2 S]
    (hcard : Nat.card S = 4) : RankTwoSylowAlternative S := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour S := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  exact (rankTwoSylowAlternative_iff S).mpr (Or.inl ⟨2, IsKleinFour.nonempty_mulEquiv⟩)

end Stellmacher.Recognition
