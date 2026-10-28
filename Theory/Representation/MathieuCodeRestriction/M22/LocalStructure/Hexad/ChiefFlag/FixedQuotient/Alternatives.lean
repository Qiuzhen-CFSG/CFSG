module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.FixedQuotient.Inputs
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.FixedQuotient.Cubic

/-!
# The invariant-subspace alternatives above the code commutator

Transport the actual quotient action to the binary six-point core. Its only
submodules are zero, the constant line and the whole core. Thus the only
invariant code subspaces containing V5 are V5, V6 and V. This uses the actual
linear equivalence and quotient map, not just the dimensions of the factors.

Source: Aschbacher--Smith, H.16.4(5), printed p.403, manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
namespace MathieuCode.Hexad.ChiefFlag.FixedQuotientData
open Representation Representation.BinaryOffender

/-- Classify invariant subspaces of the actual core through the established
alternating permutation-module theorem. -/
theorem core_submodule_alternatives
    (W : Submodule (ZMod 2) (BinaryPermutation.core (Fin 6)))
    (hW : ∀ g : Equiv.Perm (Fin 6), ∀ v ∈ W,
      BinaryPermutation.coreRepresentation (Fin 6) g v ∈ W) :
    W = ⊥ ∨ W = (BinaryPermutation.constants (Fin 6)).comap
      (BinaryPermutation.core (Fin 6)).subtype ∨ W = ⊤ := by
  let F := W.map (BinaryPermutation.core (Fin 6)).subtype
  have hF (g : alternatingGroup (Fin 6)) (v : BinaryPermutation.Full (Fin 6))
      (hv : v ∈ F) : BinaryPermutation.representation (Fin 6) g.val v ∈ F := by
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨BinaryPermutation.coreRepresentation (Fin 6) g.val w, hW g.val w hw, rfl⟩
  have hle : F ≤ BinaryPermutation.core (Fin 6) := by
    rintro _ ⟨v, _, rfl⟩; exact v.property
  rcases BinaryPermutation.invariant_submodule_classification (by decide) F hF with
      hz | hc | hh | ht
  · left
    apply bot_unique
    intro v hv
    have hm : v.val ∈ F := ⟨v, hv, rfl⟩
    rw [hz] at hm
    exact Subtype.ext hm
  · right; left
    ext v
    change v ∈ W ↔ v.val ∈ BinaryPermutation.constants (Fin 6)
    constructor
    · intro hv
      exact hc ▸ (show v.val ∈ F from ⟨v, hv, rfl⟩)
    · intro hv
      obtain ⟨w, hw, he⟩ := (hc.symm ▸ hv : v.val ∈ F)
      exact Subtype.ext he ▸ hw
  · right; right
    apply top_unique
    intro v _
    obtain ⟨w, hw, he⟩ := (hh.symm ▸ v.property : v.val ∈ F)
    exact Subtype.ext he ▸ hw
  · have hc : BinaryPermutation.core (Fin 6) = ⊤ := by
      apply top_unique; rwa [ht] at hle
    exact False.elim ((ne_of_lt (BinaryPermutation.core_lt_top (Fin 6))) hc)

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- Carry an actual invariant quotient image through the six-point marking. -/
def coreImage (D : Actions E) (W : Subrepresentation codeAction) :
    Submodule (ZMod 2) (BinaryPermutation.core (Fin 6)) :=
  (V5.quotientImage W).toSubmodule.map D.coreEquiv.toLinearMap

theorem coreImage_invariant (D : Actions E) (W : Subrepresentation codeAction)
    (g : Equiv.Perm (Fin 6)) (v : BinaryPermutation.core (Fin 6))
    (hv : v ∈ coreImage D W) :
    BinaryPermutation.coreRepresentation (Fin 6) g v ∈ coreImage D W := by
  obtain ⟨a, rfl⟩ := D.quotientMap_surjective g
  obtain ⟨w, hw, rfl⟩ := hv
  refine ⟨V5.quotientRepresentation a w,
    (V5.quotientImage W).apply_mem_toSubmodule a hw, ?_⟩
  exact D.coreEquiv_equivariant a w

private theorem image_injective (D : Actions E) {U W : Subrepresentation codeAction}
    (hU : V5 ≤ U) (hW : V5 ≤ W) (he : coreImage D U = coreImage D W) : U = W := by
  have he' := Submodule.map_injective_of_injective D.coreEquiv.injective he
  have he'' := congrArg (Submodule.comap V5.toSubmodule.mkQ) he'
  change (U.toSubmodule.map V5.toSubmodule.mkQ).comap V5.toSubmodule.mkQ =
    (W.toSubmodule.map V5.toSubmodule.mkQ).comap V5.toSubmodule.mkQ at he''
  rw [Submodule.comap_map_eq, Submodule.comap_map_eq, Submodule.ker_mkQ,
    sup_eq_left.mpr (show V5.toSubmodule ≤ U.toSubmodule from hU),
    sup_eq_left.mpr (show V5.toSubmodule ≤ W.toSubmodule from hW)] at he''
  exact Subrepresentation.toSubmodule_injective he''

/-- Only the actual V5, V6 and V can occur above V5. -/
theorem subrepresentation_alternatives (D : Actions E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (W : Subrepresentation codeAction) (hW : V5 ≤ W) :
    W = V5 ∨ W = D.six ∨ W = ⊤ := by
  have h5 := codeCommutatorSubrepresentation_finrank h h24
  change Module.finrank (ZMod 2) V5.toSubmodule = 5 at h5
  have hdim : Module.finrank (ZMod 2) (coreImage D D.six) = 1 := by
    rw [coreImage, LinearEquiv.finrank_map_eq]
    have hi := FixedQuotientCubic.image_finrank V5.toSubmodule D.six.toSubmodule
    rw [inf_eq_left.mpr (show V5.toSubmodule ≤ D.six.toSubmodule from D.five_le_six)] at hi
    change Module.finrank (ZMod 2) (V5.quotientImage D.six).toSubmodule + _ = _ at hi
    have hs := D.six_dim
    omega
  have hs : coreImage D D.six = (BinaryPermutation.constants (Fin 6)).comap
      (BinaryPermutation.core (Fin 6)).subtype := by
    rcases core_submodule_alternatives _ (coreImage_invariant D D.six) with hz | he | ht
    · rw [hz, finrank_bot] at hdim; omega
    · exact he
    · rw [ht, finrank_top, BinaryPermutation.finrank_core] at hdim
      norm_num at hdim
  have hz : coreImage D V5 = ⊥ := by
    change (V5.toSubmodule.map V5.toSubmodule.mkQ).map _ = _
    rw [Submodule.mkQ_map_self, Submodule.map_bot]
  have ht : coreImage D (⊤ : Subrepresentation codeAction) = ⊤ := by
    change ((⊤ : Submodule (ZMod 2) M22Code).map V5.toSubmodule.mkQ).map _ = _
    rw [Submodule.map_top, Submodule.range_mkQ, Submodule.map_top, LinearEquiv.range]
  rcases core_submodule_alternatives _ (coreImage_invariant D W) with hw | hw | hw
  · exact Or.inl (image_injective D hW le_rfl (hw.trans hz.symm))
  · exact Or.inr (Or.inl (image_injective D hW D.five_le_six (hw.trans hs.symm)))
  · exact Or.inr (Or.inr (image_injective D hW le_top (hw.trans ht.symm)))

end MathieuCode.Hexad.ChiefFlag.FixedQuotientData
