module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.Actions
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.QuotientAlternatives.BinaryRecognition.Preservation
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.QuotientAlternatives.BinaryRecognition.Symplectic
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# Order-360 overgroups of the parity-twisted binary S₄ are A₆

The twisted S₄ fixes the alternating form with matrix J+I. Its three-cycle
fixes no other nondegenerate alternating form, so an order-360 overgroup's
orbit of this form has cardinal 1 modulo 3. Orbit-stabilizer also makes that
cardinal divide 15, forcing the entire overgroup to preserve the form.

The explicit basis change in `Symplectic` embeds this overgroup in the actual
Sp₄(2). Composing with the concrete six-letter polar equivalence embeds it
in S₆, where its order makes it the unique index-two subgroup A₆. Thus the
conclusion follows from the specified representation and order, without an
additional simplicity, odd-core, or form-preservation premise.

Source: the order-360 identification in Z. Janko,
*A characterization of the Mathieu simple groups, I*, J. Algebra 9 (1968),
Section 2, Lemma 6, p.6. The normalizer quotient and other source clauses are
assembled by the consumer of this concrete recognition theorem.
-/

public section

open Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
namespace Theory.GroupTheory.HeldM22A10.BinaryRecognition

/-- Every order-360 binary automorphism subgroup containing the exact twisted
S₄ action is isomorphic to the actual alternating group on six letters. -/
theorem equiv_alternatingSix_of_card360 (X : Subgroup (MulAut BinaryFour))
    (hX : twistedAction.range ≤ X) (hcard : Nat.card X = 360) :
    Nonempty (X ≃* alternatingGroup (Fin 6)) := by
  let inclusion : X →* formStabilizer :=
    X.inclusion (fun g hg => preserves_base X hX hcard ⟨g, hg⟩)
  have hi : Function.Injective inclusion := Subgroup.inclusion_injective _
  let f : X →* Equiv.Perm (Fin 6) :=
    Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.toMonoidHom.comp
      (stabilizerRepresentation.comp inclusion)
  have hf : Function.Injective f :=
    Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm.injective.comp
      (stabilizerRepresentation_injective.comp hi)
  have hc : Nat.card f.range = 360 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hcard
  have hi2 : f.range.index = 2 := by
    have he := f.range.index_mul_card
    rw [hc] at he
    have hs : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      decide
    rw [hs] at he
    omega
  exact ⟨(MonoidHom.ofInjective hf).trans
    (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi2))⟩

end Theory.GroupTheory.HeldM22A10.BinaryRecognition
