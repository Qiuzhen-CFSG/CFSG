module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ExtraExtensions.FactorSets
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.QuotientAction

/-!
# The actual Held centralizer as a binary action extension

An intertwiner of the quotient action changes only the coordinates on the
specified elementary kernel. Its inclusion still has image exactly that
kernel, and the quotient map is the original quotient projection. Thus the
factor-set complement construction preserves the subgroup in the source
statement, even when the group has several elementary normal subgroups.

Source: Huppert--Blackburn, *Finite Groups III*, XII.1.18(b), p.314.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions
open LocalModelDichotomy
universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
variable {α : SymmetricFour →* MulAut BinaryFour}

/-- The exact local extension in coordinates supplied by an action intertwiner. -/
@[expose] public noncomputable def localExtension (e : MulAut BinaryFour)
    (he : ∀ s w, e (D.quotientBinaryAction s w) = α s (e w)) :
    ActionExtension α D.centralizer where
  inl := D.kernel.subtype.comp (D.kernelBinaryEquiv.trans e).symm.toMonoidHom
  rightHom := D.extensionQuotient
  inl_injective := Subtype.val_injective.comp (D.kernelBinaryEquiv.trans e).symm.injective
  range_inl_eq_ker_rightHom := by
    rw [D.extensionQuotient_ker]
    ext h
    change (∃ w, ((D.kernelBinaryEquiv.trans e).symm w : D.centralizer) = h) ↔ h ∈ D.kernel
    constructor
    · rintro ⟨w, rfl⟩
      exact ((D.kernelBinaryEquiv.trans e).symm w).property
    · intro hh
      refine ⟨(D.kernelBinaryEquiv.trans e) ⟨h, hh⟩, ?_⟩
      rw [MulEquiv.symm_apply_apply]
  rightHom_surjective := D.extensionQuotient_surjective
  conjugation h w := by
    change ((D.kernelBinaryEquiv.trans e).symm (α (D.extensionQuotient h) w) : D.centralizer) =
      h * ((D.kernelBinaryEquiv.trans e).symm w : D.centralizer) * h⁻¹
    obtain ⟨f, rfl⟩ := (D.kernelBinaryEquiv.trans e).surjective w
    have heq := he (D.extensionQuotient h) (D.kernelBinaryEquiv f)
    rw [D.quotientBinaryAction_quotient] at heq
    change (D.kernelBinaryEquiv.trans e) (D.extensionConjugation h f) =
      α (D.extensionQuotient h) ((D.kernelBinaryEquiv.trans e) f) at heq
    rw [← heq, MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    exact D.extensionConjugation_apply h f

/-- Changing the binary coordinates does not change the specified kernel. -/
public theorem localExtension_inl_range (e : MulAut BinaryFour)
    (he : ∀ s w, e (D.quotientBinaryAction s w) = α s (e w)) :
    (localExtension D e he).inl.range = D.kernel :=
  (localExtension D e he).range_inl_eq_ker_rightHom.trans D.extensionQuotient_ker

/-- Vanishing of all factor sets for the normalized action suffices to split
the actual centralizer over its specified elementary subgroup. -/
public theorem complement_of_factorSets_coboundaries
    (hvanish : ∀ c : FactorSet α, c.IsCoboundary)
    (haction : ActionEquivalent D.quotientBinaryAction α) :
    ∃ K : Subgroup D.centralizer, D.kernel.IsComplement' K := by
  obtain ⟨e, he⟩ := haction
  let E := localExtension D e he
  obtain ⟨K, hK⟩ := E.complement_of_isCoboundary (hvanish E.factorSet)
  exact ⟨K, (localExtension_inl_range D e he) ▸ hK⟩

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions
