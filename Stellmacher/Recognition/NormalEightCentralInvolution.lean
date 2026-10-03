module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Theory.GroupTheory.PGroup.NormalEightFour
public import Stellmacher.Recognition.NormalEightMultipleFour
public import Stellmacher.Recognition.NormalEightNonnormalImage
public import Stellmacher.Recognition.NormalEightNormalImage

/-!
# The central-involution reduction for normal elementary eights

Under the no-normal-eight hypothesis, a normal four contains central omega.
Two distinct normal fours yield a normal dihedral central factor. Otherwise
the normal four is unique, and the remaining alternatives concern its actual
image in `N_G(Ω₁(Z(S)))/O₂′(N_G(Ω₁(Z(S))))`.

The three branch exclusions complete the ambient contradiction using only a
bound on normal elementary subgroups. The normal-image branch includes the
order-256 exclusion; the elementary sixteen on p.395 alone is not a
contradiction to the hypotheses here.

Source: Janko–Thompson, Math. Z. 113 (1970), result 1.2 and §§3–4, 6,
pp.385–396.
-/

namespace Stellmacher.Recognition.NormalEightCentralInvolution

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- The central omega containment needed in the quotient setup uses only the
absence of normal elementary eights when the chosen four is normal. -/
public theorem centralOmega_le_normal_four
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4) :
    centralOmega S ≤ W.map (S : Subgroup G).subtype :=
  map_mono (omega_one_center_le_normal_four_of_no_normal_eight hno W hW)

/-- The normalizer is solvable, the quotient image is an elementary four,
and the intrinsic centralizer has index two. No rank bound on arbitrary
elementary subgroups enters this setup. -/
public theorem normal_four_setup
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4) :
    Group.IsSolvable (omegaNormalizer S) ∧
      IsElementaryAbelian 2 (fourImage S W) ∧ Nat.card (fourImage S W) = 4 ∧
      (centralizer (W : Set S)).index = 2 :=
  ⟨omegaNormalizer_solvable hN S hZ, fourImage_elementary S W,
    fourImage_card S W hW, centralizer_index_two S hZ W hW⟩

/-- The three source branches: a second normal four produces a dihedral central
factor; for a unique normal four, split on normality only after quotienting. -/
public theorem multiple_or_unique_fourImage_cases
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4) :
    (∃ F : Subgroup S, F.Normal ∧ IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧ F ≠ W ∧
      Nonempty (↥(W ⊔ F) ≃* DihedralGroup 4) ∧
      (W ⊔ F) ⊔ centralizer ((W ⊔ F : Subgroup S) : Set S) = ⊤) ∨
    ((∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W) ∧
      ((fourImage S W).Normal ∨ ¬ (fourImage S W).Normal)) := by
  classical
  by_cases hu : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W
  · exact Or.inr ⟨hu, Classical.em _⟩
  · push Not at hu
    obtain ⟨F, hFn, hFe, hF, hne⟩ := hu
    let : F.Normal := hFn
    let : IsElementaryAbelian 2 F := hFe
    exact Or.inl ⟨F, hFn, hFe, hF, hne,
      sup_dihedral_of_distinct_normal_fours_of_no_normal_eight hno W F hW hF hne.symm,
      sup_centralizer_eq_top_of_distinct_normal_fours_of_no_normal_eight
        S.isPGroup' hno W F hW hF hne.symm⟩

/-- An elementary subgroup of order at least eight in this central-involution
configuration is incompatible with the absence of normal elementary eights.
The unique-four branches retain normality of the actual odd-core quotient
image as their dividing hypothesis. -/
public theorem false_of_no_normal_eight
    [IsSimpleGroup G] (hns : ¬ Group.IsSolvable G)
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (A : Subgroup S) [IsElementaryAbelian 2 A] (hA : 8 ≤ Nat.card A)
    (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4) :
    False := by
  rcases multiple_or_unique_fourImage_cases S hno W hW with hmultiple | ⟨hunique, himage⟩
  · obtain ⟨F, hFn, hFe, hF, hne, _⟩ := hmultiple
    let : F.Normal := hFn
    let : IsElementaryAbelian 2 F := hFe
    exact NormalEightMultipleFour.false_of_distinct_normal_fours
      hns S A hA hno W F hW hF hne
  · rcases himage with hnormal | hnonnormal
    · let : (fourImage S W).Normal := hnormal
      exact NormalEightNormalImage.false_of_normal_fourImage
        hns hN S A hA hnonab hZ hno W hW hunique
    · exact NormalEightNonnormalImage.false_of_nonnormal_image
        hns hN S A hA hnonab hZ hno W hW hunique hnonnormal

end Stellmacher.Recognition.NormalEightCentralInvolution
