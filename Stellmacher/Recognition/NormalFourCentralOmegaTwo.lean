module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Stellmacher.Recognition.NormalFourNormalImage
public import Stellmacher.Recognition.NormalFourNonnormalImage
public import Theory.GroupTheory.PGroup.MultipleNormalFourSylow

/-!
# Normal fours with one central involution: rank contradiction

The setup in `NormalFourOddCoreSetup` uses the actual quotient image in
`N_G(Ω₁(Z(S)))/O₂′(N_G(Ω₁(Z(S))))`. This module records the contradiction
needed at the end of the normal-image argument: under the ambient elementary
rank bound, two distinct four-groups in the Sylow subgroup cannot commute.

The final theorem below assembles the multiple-normal-four theorem (1.2), the
nonnormal-image argument (§4), and the normal-image fusion argument (§6) of
Janko–Thompson, Math. Z. 113 (1970), pp.385–395.
-/

namespace Stellmacher.Recognition.NormalFourCentralOmegaTwo

/-- The commuting distinct fours produced by the normal-image fusion argument
contradict the ambient elementary rank bound. -/
public theorem not_exists_distinct_commuting_fours
    {G : Type*} [Group G] [Finite G]
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) :
    ¬ ∃ E F : Subgroup S,
      IsElementaryAbelian 2 E ∧ Nat.card E = 4 ∧
      IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
      F ≤ Subgroup.centralizer (E : Set S) ∧ E ≠ F := by
  rintro ⟨E, F, he, hE, hf, hF, hcomm, hne⟩
  let : IsElementaryAbelian 2 E := he
  let : IsElementaryAbelian 2 F := hf
  exact hne (Subgroup.four_eq_of_le_centralizer_of_elementary_card_lt_eight
    (Subgroup.elementary_card_lt_eight_of_subgroup hrank (S : Subgroup G))
    E F hE hF hcomm).symm

/- The normal four case of the rank-two Sylow classification. -/
public theorem dihedral_or_c4WreathC2_of_normal_four
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (Subgroup.center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) :
    IsDihedralGroup S ∨ Nonempty (S ≃* C4WreathC2) := by
  by_cases hmultiple : ∃ F : Subgroup S,
      F.Normal ∧ IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧ F ≠ E
  · obtain ⟨F, hFn, hFe, hFc, hne⟩ := hmultiple
    let : F.Normal := hFn
    let : IsElementaryAbelian 2 F := hFe
    have hd : Nonempty (S ≃* DihedralGroup 4) :=
      Sylow.dihedral_of_distinct_normal_fours S hrank E F hE hFc hne.symm
    exact Or.inl ⟨4, hd⟩
  · have hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E := by
      intro F hFn hFe hFc
      by_contra hne
      exact hmultiple ⟨F, hFn, hFe, hFc, hne⟩

    by_cases hnormal : (fourImage S E).Normal
    · let : (fourImage S E).Normal := hnormal
      exact (false_of_normal_fourImage hns hrank S hZ E hE hunique).elim
    · exact Or.inr (NormalFourNonnormalImage.nonempty_mulEquiv_c4WreathC2_of_fourImage_not_normal
        hns hN hrank S hnonab hZ E hE hunique hnormal)

end Stellmacher.Recognition.NormalFourCentralOmegaTwo
