module

public import Stellmacher.Recognition.NormalFourOddCoreSetup
public import Stellmacher.Recognition.NormalFourNonnormalOrderFusion
public import Stellmacher.Recognition.NormalFourOrder32FusionRecognition
public import ABG.ChapterII.Section1.WreathedRegularModel
public import Theory.SpecificGroups.AffineEight.ElementaryEight

/-!
# Classification of the nonnormal quotient-image branch

The wreathed presentation of height two gives the concrete `C4WreathC2`
required by the Sylow classification. The other terminal model in §4,
the faithful split extension of C₈ by a four-group, is the holomorph of C₈.
Its elementary subgroup of order eight excludes it under our elementary
rank bound, without a further ambient transfer or Fong hypothesis.

The final theorem assembles the ambient order-and-fusion argument with
the order-32 recognition theorem and the concrete wreath-model adapter.
Nonnormality of `fourImage S E` is retained in the actual odd-core quotient
throughout; it is not replaced by nonnormality before taking that quotient.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, pp.389–393, especially
the last two paragraphs of Lemma 4.1; see `normal-four-case-split.md` beside
the saved source PDF.
-/

namespace Stellmacher.Recognition.NormalFourNonnormalImage

/-- The presentation conclusion identifies the exact model used by the public
rank-two Sylow interface. -/
public theorem nonempty_mulEquiv_c4WreathC2_of_wreathed
    {P : Type*} [Group P] (hP : ABG.IsWreathedOfHeight P 2) :
    Nonempty (P ≃* C4WreathC2) :=
  hP.nonempty_mulEquiv_regularWreath

/-- The split cyclic-eight alternative is incompatible with the ambient rank
bound, by its elementary subgroup of order eight. -/
public theorem not_affineEight_of_elementary_card_lt_eight
    {G : Type*} [Group G]
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) : ¬ Nonempty (S ≃* AffineEight.Model) := by
  rintro ⟨e⟩
  exact AffineEight.not_injective_of_elementary_card_lt_eight hrank
    ((S : Subgroup G).subtype.comp e.symm.toMonoidHom)
    ((S : Subgroup G).subtype_injective.comp e.symm.injective)

/-- Assemble the two terminal alternatives once they have been established by
the ambient nonnormal-image argument. -/
public theorem nonempty_mulEquiv_c4WreathC2_of_terminal_alternatives
    {G : Type*} [Group G]
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G)
    (hS : ABG.IsWreathedOfHeight S 2 ∨ Nonempty (S ≃* AffineEight.Model)) :
    Nonempty (S ≃* C4WreathC2) := by
  rcases hS with hW | hA
  · exact nonempty_mulEquiv_c4WreathC2_of_wreathed hW
  · exact (not_affineEight_of_elementary_card_lt_eight hrank S hA).elim

/-- The Sylow-structure conclusion of Janko–Thompson Lemma 4.1: a unique
normal four with nonnormal image in `N_G(Ω₁(Z(S)))/O₂′` forces the Sylow
subgroup to be the concrete wreath product `C₄ ≀ C₂`. -/
public theorem nonempty_mulEquiv_c4WreathC2_of_fourImage_not_normal
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) (hN : Stellmacher.IsNTwoGroup G)
    (hrank : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A < 8)
    (S : Sylow 2 G) (hnonab : ¬ IsMulCommutative S)
    (hZ : Nat.card (omega₁ (Subgroup.center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hnormal : ¬ (NormalFourCentralOmegaTwo.fourImage S E).Normal) :
    Nonempty (S ≃* C4WreathC2) := by
  obtain ⟨hS, hfusion⟩ :=
    NormalFourCentralOmegaTwo.order_and_fusion_of_fourImage_not_normal
      hns hN hrank S hnonab hZ E hE hunique hnormal
  exact nonempty_mulEquiv_c4WreathC2_of_wreathed
    (NormalFourOrder32FusionRecognition.isWreathedOfHeight_two_of_fusion
      S hS hZ hrank E hE hfusion)

end Stellmacher.Recognition.NormalFourNonnormalImage
