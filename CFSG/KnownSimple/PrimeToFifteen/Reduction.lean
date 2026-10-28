module
public import CFSG.Quasithin.Defs
public import Mathlib.GroupTheory.Solvable

/-!
# Solvability from prime-excluded simple sections

Induct on the order of a finite K-group. A proper normal subgroup and its
quotient inherit both K and the prime exclusions. The simple case is passed
to the carrier-specific theorem. The consumer is the prime-to-15 centralizer
in Aschbacher–Smith D.2.13 and the original A₅ local-module passage.
-/

public section
namespace CFSG.Quasithin
universe u

/-- A finite K-group is solvable when its simple K-sections with the same
prime exclusions are solvable. This induction keeps the full K predicate. -/
theorem IsKGroup.isSolvable_of_coprime_simple
    {K : GroupClass.{u}}
    (hsimple : ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S],
      K S → Nat.Coprime 3 (Nat.card S) → Nat.Coprime 5 (Nat.card S) →
        Group.IsSolvable S)
    (G : Type u) [Group G] [Finite G]
    (hK : IsKGroup K G) (h3 : Nat.Coprime 3 (Nat.card G))
    (h5 : Nat.Coprime 5 (Nat.card G)) : Group.IsSolvable G := by
  classical
  induction hn : Nat.card G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases hsub : Subsingleton G
    · let := hsub
      infer_instance
    let : Nontrivial G := not_subsingleton_iff_nontrivial.mp hsub
    by_cases hsimp : IsSimpleGroup G
    · let := hsimp
      exact hsimple G (hK G hsimp ⊤ (Subgroup.topEquiv.toMonoidHom)
        Subgroup.topEquiv.surjective) h3 h5
    · obtain ⟨N, hN, hbot, htop⟩ :
          ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
        by_contra h
        apply hsimp
        refine ⟨fun N hN => ?_⟩
        by_cases hb : N = ⊥
        · exact Or.inl hb
        · exact Or.inr (by_contra fun ht => h ⟨N, hN, hb, ht⟩)
      let := hN
      have hcard : Nat.card N * Nat.card (G ⧸ N) = Nat.card G := N.card_mul_index
      have hNpos : 0 < Nat.card N := Nat.card_pos
      have hQpos : 0 < Nat.card (G ⧸ N) := Nat.card_pos
      have hNbig : 1 < Nat.card N := by
        let : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hbot
        exact Finite.one_lt_card
      have hQbig : 1 < Nat.card (G ⧸ N) := N.one_lt_index_of_ne_top htop
      have hNlt : Nat.card N < n := by nlinarith
      have hQlt : Nat.card (G ⧸ N) < n := by nlinarith
      apply (Group.isSolvable_iff_subgroup_quotient N).mpr
      constructor
      · exact ih _ hNlt N (hK.subgroup N)
          (h3.of_dvd_right N.card_subgroup_dvd_card)
          (h5.of_dvd_right N.card_subgroup_dvd_card) rfl
      · exact ih _ hQlt (G ⧸ N) (hK.quotient N)
          (h3.of_dvd_right N.card_quotient_dvd_card)
          (h5.of_dvd_right N.card_quotient_dvd_card) rfl
end CFSG.Quasithin
