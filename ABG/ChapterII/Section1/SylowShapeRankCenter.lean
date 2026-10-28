module

public import ABG.ChapterII.Section1.WreathedElementaryRank
public import ABG.ChapterII.Section1.WreathedCenter
public import Theory.GroupTheory.SemidihedralFourSubgroup
public import Theory.GroupTheory.CyclicIndexTwoElementary

/-!
# Exact elementary rank and cyclic centers of the two Sylow presentations

Semidihedral and wreathed groups have elementary abelian two-rank exactly two
and cyclic center. In the semidihedral case, the rotation subgroup has index
two, bounding every elementary abelian subgroup by four; the half-order
rotation and reflection generate a four-group. In the wreathed case use the
base four-group, the elementary subgroup bound and the diagonal center.

Source: Alperin–Brauer–Gorenstein II.1 Lemmas 1–2, article pp. 9–10;
Aschbacher–Smith A.3.21(b), printed p. 55.
-/

namespace ABG

/-- The exact elementary rank and cyclic center follow from the genuine
semidihedral or wreathed presentations. The rank statement retains an actual
four-subgroup together with the bound on all elementary abelian subgroups. -/
public theorem rank_two_and_cyclic_center_of_sylow_shape
    {S : Type*} [Group S] [Finite S]
    (hS : Stellmacher.IsSemidihedralGroup S ∨ IsWreathedGroup S) :
    (∃ E : Subgroup S, IsElementaryAbelian 2 E ∧ Nat.card E = 4) ∧
    (∀ E : Subgroup S, IsElementaryAbelian 2 E → Nat.card E ≤ 4) ∧
    IsCyclic (Subgroup.center S) := by
  rcases hS with hS | ⟨n, hS⟩
  · obtain ⟨n, hn, hc, a, b, ha, hb, hab, hgen⟩ := hS
    refine ⟨⟨_, Semidihedral.canonical_four hn a b ha hb hab hgen⟩, ?_, ?_⟩
    · intro E hE
      let : IsElementaryAbelian 2 E := hE
      have hindex : (Subgroup.zpowers a).index = 2 := by
        apply Nat.eq_of_mul_eq_mul_left (pow_pos (by decide : 0 < 2) (n - 1))
        calc
          2 ^ (n - 1) * (Subgroup.zpowers a).index =
              Nat.card (Subgroup.zpowers a) * (Subgroup.zpowers a).index := by
            rw [Nat.card_zpowers, ha]
          _ = Nat.card S := (Subgroup.zpowers a).card_mul_index
          _ = 2 ^ (n - 1) * 2 := by
            rw [hc, ← pow_succ]
            congr 1
            omega
      exact Subgroup.card_le_four_of_pow_two_of_cyclic_index_two _ hindex E
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
          (IsElementaryAbelian.exponent_dvd_p 2 E))
    · rw [Semidihedral.center_eq hn a b ha hb hab hgen]
      infer_instance
  · obtain ⟨P⟩ := Wreathed.nonempty_presentation hS
    let : IsKleinFour P.T := P.T_isFourGroup
    have hE : IsElementaryAbelian 2 P.T :=
      { toIsMulCommutative := IsKleinFour.isMulCommutative
        exponent_dvd_p := by simp }
    exact ⟨⟨P.T, hE, IsKleinFour.card_four⟩,
      fun E hE => @Wreathed.Presentation.elementary_card_le_four S _ _ n P E hE,
      P.center_cyclic⟩
end ABG
