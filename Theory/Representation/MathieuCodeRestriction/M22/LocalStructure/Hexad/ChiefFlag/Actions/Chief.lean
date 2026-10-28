module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Actions.Core
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Actions.Transvections
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.Actions.Sections

/-!
# Irreducibility of the four hexad code chief factors

The checked alternating permutation-module theorem implies irreducibility
for S6. The separate earlier kernel marking and natural-module self-duality
transfer this to the dual kernel conjugation module. The constructed middle
and top action identifications, and the one-dimensional gaps, then prove
every cover in the actual code flag and irreducibility of its literal factors.

Source: Aschbacher--Smith H.16.4(1)--(3), printed p.403, manuscript of
1 March 2004. Both earlier permutation markings retain their own intertwiners.
-/

@[expose] public section
noncomputable section
open Representation
namespace MathieuCode.Hexad.ChiefFlag.Actions
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- The six-point natural section is irreducible for the full symmetric group. -/
theorem sixNatural_irreducible :
    IsIrreducible (BinaryPermutation.naturalRepresentation (Fin 6)) := by
  let hi := BinaryPermutation.alternatingNatural_isIrreducible
    (by decide : 5 ≤ Fintype.card (Fin 6))
  have hd : 0 < Module.finrank (ZMod 2) (BinaryPermutation.natural (Fin 6)) := by
    rw [BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
    decide
  let : Nontrivial (BinaryPermutation.natural (Fin 6)) := Module.nontrivial_of_finrank_pos hd
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro he
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule he)
  intro P
  let T : Subrepresentation (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) :=
    ⟨P.toSubmodule, fun g _ hv => P.apply_mem_toSubmodule g.val hv⟩
  rcases hi.eq_bot_or_eq_top T with hb | ht
  · exact Or.inl (Subrepresentation.toSubmodule_injective
      (congrArg (fun S : Subrepresentation (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) => S.toSubmodule) hb))
  · exact Or.inr (Subrepresentation.toSubmodule_injective
      (congrArg (fun S : Subrepresentation (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)) => S.toSubmodule) ht))

namespace KernelModel
variable {D : CocodeActionData E}

/-- The earlier kernel marking is dualized through the actual invariant dot product. -/
def dualNaturalEquiv (K : KernelModel D) :
    Module.Dual (ZMod 2) E ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
  K.naturalEquiv.symm.dualMap.trans (BinaryPermutation.naturalDualEquiv (Fin 6)).symm

theorem dualNaturalEquiv_equivariant (K : KernelModel D) (g : Stabilizer)
    (v : Module.Dual (ZMod 2) E) :
    K.dualNaturalEquiv (D.kernelRepresentation.dual g v) =
      BinaryPermutation.naturalRepresentation (Fin 6) (K.quotientMap g) (K.dualNaturalEquiv v) := by
  have hm (w : Module.Dual (ZMod 2) E) :
      BinaryPermutation.naturalDualEquiv (Fin 6) (K.dualNaturalEquiv w) =
        K.naturalEquiv.symm.dualMap w :=
    (BinaryPermutation.naturalDualEquiv (Fin 6)).apply_symm_apply _
  apply (BinaryPermutation.naturalDualEquiv (Fin 6)).injective
  calc
    _ = K.naturalEquiv.symm.dualMap (D.kernelRepresentation.dual g v) := hm _
    _ = (BinaryPermutation.naturalRepresentation (Fin 6)).dual (K.quotientMap g)
        (K.naturalEquiv.symm.dualMap v) :=
      dual_equivariant D.kernelRepresentation (BinaryPermutation.naturalRepresentation (Fin 6))
        K.quotientMap K.naturalEquiv K.naturalEquiv_equivariant g v
    _ = (BinaryPermutation.naturalRepresentation (Fin 6)).dual (K.quotientMap g)
        (BinaryPermutation.naturalDualEquiv (Fin 6) (K.dualNaturalEquiv v)) :=
      congrArg ((BinaryPermutation.naturalRepresentation (Fin 6)).dual (K.quotientMap g))
        (hm v).symm
    _ = _ := (BinaryPermutation.naturalDualEquiv_equivariant (Fin 6)
      (K.quotientMap g) (K.dualNaturalEquiv v)).symm

theorem kernel_dual_irreducible (K : KernelModel D) :
    IsIrreducible D.kernelRepresentation.dual :=
  irreducible_transport D.kernelRepresentation.dual
    (BinaryPermutation.naturalRepresentation (Fin 6)) K.quotientMap K.quotientMap_surjective
    K.dualNaturalEquiv K.dualNaturalEquiv_equivariant sixNatural_irreducible

end KernelModel

namespace CocodeActionData

theorem middle_irreducible (D : CocodeActionData E) (K : KernelModel D)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    IsIrreducible codeCenter.quotientRepresentation :=
  irreducible_transport codeCenter.quotientRepresentation D.kernelRepresentation.dual
    (MonoidHom.id Stabilizer) Function.surjective_id (D.middleEquiv h h24)
    (D.middleEquiv_equivariant h h24) K.kernel_dual_irreducible

/-- Every adjacent pair in the actual flag is a cover among invariant subspaces. -/
theorem code_chief (D : CocodeActionData E) (K : KernelModel D)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    (⊥ : Subrepresentation codeAction) ⋖ V1 ∧ V1 ⋖ V5 ∧
      V5 ⋖ D.codeSix ∧ D.codeSix ⋖ (⊤ : Subrepresentation codeAction) := by
  have hs := D.code_strict h h24
  refine ⟨covBy_of_finrank bot_le ?_, ?_, covBy_of_finrank D.five_le_six ?_,
    D.codeSix_covBy_top h h24⟩
  · change Module.finrank (ZMod 2) V1.toSubmodule =
      Module.finrank (ZMod 2) (⊥ : Submodule (ZMod 2) M22Code) + 1
    rw [finrank_bot, zero_add]
    exact codeFixedSubrepresentation_finrank h
  · exact covBy_of_irreducible_section hs.2.1 (D.middle_irreducible K h h24)
  · rw [D.codeSix_finrank h h24, codeCommutatorSubrepresentation_finrank h h24]

/-- Irreducibility on each literal chief factor, including both quotient actions. -/
theorem chief_factors_irreducible (D : CocodeActionData E) (K : KernelModel D)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    IsIrreducible V1.toRepresentation ∧ IsIrreducible codeCenter.quotientRepresentation ∧
      IsIrreducible (sectionSubrepresentation V5 D.codeSix).quotientRepresentation ∧
      IsIrreducible D.codeSix.quotientRepresentation := by
  have hc := D.code_chief K h h24
  exact ⟨(Subrepresentation.irreducible_iff_isAtom V1).mpr (bot_covBy_iff.mp hc.1),
    D.middle_irreducible K h h24, irreducible_section_of_covBy hc.2.2.1,
    SimpleHeadQuotient.irreducible_quotient_of_isCoatom D.codeSix (covBy_top_iff.mp hc.2.2.2)⟩

end CocodeActionData
end MathieuCode.Hexad.ChiefFlag.Actions
