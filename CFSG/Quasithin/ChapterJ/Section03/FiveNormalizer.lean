module
public import CFSG.Quasithin.ChapterJ.Section03.FiveNormalizer.Fitting
public import Theory.SpecificGroups.GL2.FiveWreathSylow

/-!
# The original-source five-normalizer structure

The actual extraspecial odd core and its order32 complement have been
constructed from the original TypeRu local setup. The faithful Frattini
quotient action identifies that complement with the literal C₄ wr C₂.
Together with its generalized Fitting subgroup and ambient Sylow promotion,
this proves J.3.6 from the preceding J.3.1 order, its only remaining input.

Source: Aschbacher--Smith J.3.6, printed p.439.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Section03
open Centralizers Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}

/-- The actual local complement is the cyclic-four wreath product. -/
theorem exists_five_normalizer_wreath (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hG : Nat.card G=2^14*3^3*5^3*7*13*29) :
    ∃ R : Subgroup G, R≤d.toTypeRuSetup.H ∧
      R≤normalizer (B5Image B5 : Set G) ∧ Nat.card R=32 ∧ CQ B5≤R ∧
      Disjoint (fiveOddPart B5) R ∧
      normalizer (B5Image B5 : Set G)=fiveOddPart B5⊔R ∧
      Nonempty (R≃*RegularWreathProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2))) ∧
      c.z∈(center R).map R.subtype := by
  obtain ⟨R,hRH,hRN,hR32,hQR,hd,hgen,hz⟩ := exists_five_normalizer_product c B5
  obtain ⟨f,hf⟩ := exists_five_local_two_linear_action c B5 hG R hRH hRN hR32 hQR
  exact ⟨R,hRH,hRN,hR32,hQR,hd,hgen,
    Matrix.GeneralLinearGroup.FiveWreathSylow.wreath_equiv_of_injective_card32 f hf hR32,hz⟩

/-- J.3.6 with only the preceding J.3.1 group order retained. All groups and
involutions are the original source objects. -/
theorem lemma_J_3_6_of_order (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hG : Nat.card G=2^14*3^3*5^3*7*13*29) :
    IsExtraspecial 5 (fiveOddPart B5) ∧
      (∃ S : Sylow 5 G, (S : Subgroup G)=fiveOddPart B5) ∧
      (Theory.GroupTheory.generalizedFitting (normalizer (B5Image B5 : Set G))).map
        (normalizer (B5Image B5 : Set G)).subtype=fiveOddPart B5 ∧
      ∃ R : Subgroup G, R≤d.toTypeRuSetup.H ∧ Disjoint (fiveOddPart B5) R ∧
        normalizer (B5Image B5 : Set G)=fiveOddPart B5⊔R ∧
        Nonempty (R≃*RegularWreathProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2))) ∧
        c.z∈(center R).map R.subtype := by
  obtain ⟨S,hS,_,_⟩ := five_oddPart_sylow c B5 hG
  obtain ⟨R,hRH,_,_,_,hd,hgen,he,hz⟩ := exists_five_normalizer_wreath c B5 hG
  refine ⟨five_oddPart_extraspecial c B5 hG,⟨S,hS⟩,?_,R,hRH,hd,hgen,he,hz⟩
  rw [five_normalizer_generalizedFitting c B5 hG,map_subgroupOf_eq_of_le
    ((fiveOddPart_le_G5 B5).trans (Subgroup.centralizer_le_normalizer _))]

end CFSG.Quasithin.ChapterJ.Section03
