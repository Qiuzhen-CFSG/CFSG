module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.DualAction.Flag
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.DualAction.Quotient
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.DualAction.CommutatorBounds
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.DualAction.Commutator
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet.DualAction.Transvections

/-!
# Conditional duality for the outer M22 quintet

The cocode chief flag dualizes to the canonical code annihilators. The
indecomposable marked kernel module rules out a proper cocode commutator,
identifying the bottom code term with the actual K-fixed space. Self-duality
of the binary five-point natural module supplies its S5 marking. Inverse
duality transfers the full center transvection action to the literal quotient,
and double-dual evaluation identifies its axis with K under Q-conjugation.

`code_structure` assembles all of H.16.3(1--3), conditional only on the precise
cocode data `CocodeFlag`, `CocodeActionData`, and the earlier facts
`EarlierInputs`. The source assembly owner must construct these inputs from
H.14.3--4 and H.15.4; no requested code conclusion is an input here.

Source: Aschbacher--Smith, H.15.4 and H.16.3, printed pp.400,403,
combined manuscript of 1 March 2004.
-/

public section
noncomputable section
namespace MathieuCode.M22Quintet.DualAction

variable {F : CocodeFlag} {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

/-- Complete conditional transfer of H.16.3(1--3) on the native code module.
The natural-module witness includes a surjective S5 marking with precisely
the relative kernel K. The last clause includes both the full faithful image
and its explicit hyperplane-transvection description, followed by an actual
group isomorphism of the axis with K intertwining ambient Q-conjugation. -/
theorem code_structure (D : CocodeActionData F E) (H : EarlierInputs D) :
    ((⊥ : Subrepresentation codeAction) ⋖ V4Subrepresentation ∧
      V4Subrepresentation ⋖ F.codeEight ∧ F.codeEight ⋖ F.codeNine ∧
      F.codeNine ⋖ (⊤ : Subrepresentation codeAction) ∧
      F.codeEight.toSubmodule = V8 ∧ F.codeNine.toSubmodule = V9 ∧
      (⊥ : Submodule (ZMod 2) M22Code) < V4 ∧ V4 < V8 ∧ V8 < V9 ∧ V9 < ⊤ ∧
      Module.finrank (ZMod 2) V4 = 4 ∧ Module.finrank (ZMod 2) V8 = 8 ∧
      Module.finrank (ZMod 2) V9 = 9 ∧
      V4 = Representation.BinaryOffender.fixedSpace m22OuterCodeRepresentation K) ∧
    (∃ q : Q →* Equiv.Perm (Fin 5), Function.Surjective q ∧
      q.ker = K.subgroupOf Q ∧
      ∃ e : V4 ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5), ∀ (g : Q) (v : V4),
        e (V4Subrepresentation.toRepresentation g v) =
          BinaryPermutation.naturalRepresentation (Fin 5) (q g) (e v)) ∧
    (Function.Injective codeQuotientKernelAction ∧
      codeQuotientKernelAction.range = BinaryLinear.radical codeAxis ∧
      Module.finrank (ZMod 2) (M22Code ⧸ V4) = 6 ∧
      Module.finrank (ZMod 2) codeAxis = 5 ∧
      Module.finrank (ZMod 2) ((M22Code ⧸ V4) ⧸ codeAxis) = 1 ∧
      (∃ f : Module.Dual (ZMod 2) (M22Code ⧸ V4), f ≠ 0 ∧ f.ker = codeAxis ∧
        ∀ t : BinaryLinear.GL (M22Code ⧸ V4),
          t ∈ codeQuotientKernelAction.range ↔
            ∃ w, ∃ hw : f w = 0, t = BinaryLinear.transvection w f hw) ∧
      ∃ e : Multiplicative codeAxis ≃* K, ∀ (g : Q) (w : codeAxis),
        (e (Multiplicative.ofAdd (F.codeAxisAction g w))).val =
          g.val * (e (Multiplicative.ofAdd w)).val * g.val⁻¹) := by
  exact ⟨⟨F.code_chief.1, F.code_chief.2.1, F.code_chief.2.2.1, F.code_chief.2.2.2,
      F.codeEight_space, F.codeNine_space,
      F.code_strict.1, F.code_strict.2.1, F.code_strict.2.2.1, F.code_strict.2.2.2,
      F.code_dimensions.1, F.code_dimensions.2.1, F.code_dimensions.2.2,
      V4_eq_fixedSpace D H⟩,
    ⟨D.quotientMap, D.quotientMap_surjective, D.quotientMap_ker,
      D.codeNaturalEquiv, D.codeNaturalEquiv_equivariant⟩,
    ⟨D.codeQuotientKernelAction_faithful, D.codeQuotientKernelAction_full,
      F.codeQuotient_dim, D.codeAxis_dim, D.codeAxis_codimension,
      D.codeQuotient_transvections, D.codeAxisMarking, D.codeAxisMarking_equivariant⟩⟩

end MathieuCode.M22Quintet.DualAction
