module
public import CFSG.Quasithin.ChapterI.Section03.MathieuFixedRankTwoModels
public import CFSG.Quasithin.ChapterA.Section02.Statements.Sections
public import Theory.Representation.BinaryTwoPowerDegree.Four
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
public import Theory.Mathieu.M22.Properties.OrderEight

/-!
# No Mathieu section in binary unitary four-space

Lift a section of the projective group through the actual SU₄ projection.
Its numerator acts faithfully on four-dimensional space in characteristic
two, so none of its homomorphic images has an element of order eight.
The explicit native M₂₂ element of order eight rules out that section.
This excludes a full M₂₂ cover, without discarding its center or imposing
an involution class.

The resulting Theorem B comparison leaves only the three odd Lie families
and McL. Its actual consumer is MathieuGeneration.HallFaithfulness.ModelResidue.
Source: Aschbacher--Smith 4.2.13, printed p.612, and Theorem B, p.33.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.MathieuPumpup
open Sporadic.Mathieu ChapterA.Section02 BenderSuzuki.MatrixGroups

private theorem no_unitary_four_section {F : Type*} [Field F] [Finite F] [CharP F 2]
    (J : HermitianForm 4 F) (hs : IsSectionOf M22 (ProjectiveSpecialUnitaryMatrixGroup J)) : False := by
  obtain ⟨U,f,hf⟩ := hs.ambient_surjective (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project F J)
    (Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag.project_surjective F J)
  let ρ : Representation F U (Fin 4 → F) :=
    Matrix.toLinAlgEquiv'.toMonoidHom.comp
      ((Units.coeHom _).comp (J.specialSubgroup.subtype.comp U.subtype))
  have hi : Function.Injective ρ := Matrix.toLinAlgEquiv'.injective.comp
    (Units.val_injective.comp (J.specialSubgroup.subtype_injective.comp U.subtype_injective))
  obtain ⟨x,hx⟩ := m22_exists_order_eight
  obtain ⟨y,rfl⟩ := hf x
  exact Representation.BinaryTwoPowerDegree.image_order_ne_eight ρ hi
    (by simp only [Module.finrank_fin_fun]; omega) f y hx

/-- No binary projective unitary four-space contains a full M₂₂ cover,
including as a component of an involution fixed subgroup. -/
theorem HasMathieuFixedComponent.not_binary_unitary_four
    {S : Type*} [Group S] (h : HasMathieuFixedComponent S)
    {n : ℕ} (_hn : 1 ≤ n) (hm : ClassicalGroup.IsPSU S 4 (2 ^ n)) : False := by
  obtain ⟨F,_,_,J,hF,_,⟨e⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
    simpa only [Nat.card_eq_fintype_card,pow_mul] using hF)
  obtain ⟨a,ha,B,hB,⟨b⟩⟩ := h.of_mulEquiv e
  have hs : IsSectionOf M22 B := IsSectionOf.of_surjective
    (b.toMonoidHom.comp (QuotientGroup.mk' (center B)))
    (b.surjective.comp (QuotientGroup.mk'_surjective _))
  exact no_unitary_four_section J (hs.ambient_injective B.subtype B.subtype_injective)
/-- The remaining models are the three odd Lie families and McL. -/
@[expose] def RemainingMathieuOddSporadicModel (S : Type*) [Group S] : Prop :=
  RemainingMathieuLargeOddModel S ∨
    Nonempty (S ≃* Sporadic.LeechRelated.McL.Carrier)

/-- Remove the final binary family from the literal fixed-component comparison. -/
theorem HasMathieuFixedComponent.odd_sporadic_model_rows
    {S : Type*} [Group S] [IsSimpleGroup S] [Group.IsPerfect S]
    (h : HasMathieuFixedComponent S) (hm : IsTheoremBModel S) :
    RemainingMathieuOddSporadicModel S := by
  rcases h.proper_model_residue hm with ho | ⟨n,hn,hu⟩ | hmc
  · exact Or.inl ho
  · exact (h.not_binary_unitary_four hn hu).elim
  · exact Or.inr hmc

end CFSG.Quasithin.ChapterI.MathieuPumpup
