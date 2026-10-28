module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.Assembly
public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.CocodeAction
public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.ChiefFlag

/-!
# Hexad cocode and code transfers for M22

This endpoint retains both native M22 and the literal setwise pair action.
The fixed-space transfers and re-exported cocode action theorems prove the
rank-five deleted module, its orthogonal dual description, the avoidance
bound, xi hyperplane, pointwise centralizers, noncyclic fixed spaces and full
transvections with the genuine A6 and S6 quotient actions.

`outer_code_clauses` constructs the intermediate cocode witnesses and applies
coordinate duality and the native cubic calculation to obtain the complete
code chief flag, both section identifications and the quotient fixed space.
Its inputs are the earlier M24 statements, H.14 restriction and conjugation
markings, and the two precise prior quintet fixed dimensions. The quintet
source owner must still supply those dimensions; the chapter parent owns
discharge of the allowed M24 and H.14 premises.

Source: Aschbacher--Smith, H.15.2(2)--(6), H.16.4(1)--(5), printed
pp.398--399,403, combined manuscript of 1 March 2004.
-/

public section
noncomputable section
open MathieuCode MathieuCode.Hexad Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad

/-- The fixed-space clauses for the actual outer kernel, conditional only on
the specified earlier M24 and H.14 inputs. -/
theorem outer_fixed_clauses
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    Module.finrank (ZMod 2)
        (fixedSpace m22OuterCocodeRepresentation (m22OuterHexadKernel m22SourceOctad)) = 5 ∧
    Module.finrank (ZMod 2) (M22Cocode ⧸
        fixedSpaceSpan m22OuterCocodeRepresentation (m22OuterHexadKernel m22SourceOctad)) = 1 ∧
    (∀ I : Submodule (ZMod 2) M22Cocode,
      I ≤ fixedSpace m22OuterCocodeRepresentation (m22OuterHexadKernel m22SourceOctad) →
      Disjoint (I : Set M22Cocode) m22WeightTwoFamily → Module.finrank (ZMod 2) I ≤ 4) ∧
    (∀ A ≤ m22OuterHexadKernel m22SourceOctad, ¬ IsCyclic A →
      fixedSpace m22OuterCocodeRepresentation A =
        fixedSpace m22OuterCocodeRepresentation (m22OuterHexadKernel m22SourceOctad)) ∧
    fixedSpace m22OuterCodeRepresentation (m22OuterHexadKernel m22SourceOctad) =
      Submodule.span (ZMod 2) {codeVector m22SourceOctad m22Pair_le_sourceOctad} ∧
    Module.finrank (ZMod 2) (codeCommutator (m22OuterHexadKernel m22SourceOctad)) = 5 ∧
    Module.finrank (ZMod 2) (M22Code ⧸ codeCommutator (m22OuterHexadKernel m22SourceOctad)) = 5 := by
  have h5 := h.fixedSpace_finrank h24.displacement h24.fixed_finrank
  refine ⟨h5, h.xi_hyperplane h24.displacement h24.xi_codim
    (h.kernel_ne_bot h24.fixed_finrank), ?_, ?_, ?_, ?_, ?_⟩
  · exact avoiding_weightTwo_finrank_le (MonoidHom.id m22PairStabilizer)
      (m22OuterHexadKernel m22SourceOctad) h.kernel_image h5
  · exact fun A hA hnc => h.noncyclic_fixedSpace h24.displacement h24.noncyclic_fixed A hA hnc
  · exact code_fixedSpace_eq_span (MonoidHom.id m22PairStabilizer)
      (m22OuterHexadKernel m22SourceOctad) m22SourceOctad m22Pair_le_sourceOctad h.kernel_image
  · exact codeCommutator_finrank _ h5
  · exact codeCommutator_quotient_finrank _ h5

/-- The same transfer for M=L uses the original native M22 action; no outer
quotient is substituted for its alternating six-point quotient. -/
theorem inner_fixed_clauses
    (h : InnerRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad) :
    Module.finrank (ZMod 2)
        (fixedSpace m22CocodeRepresentation (m22InnerHexadKernel m22SourceOctad)) = 5 ∧
    Module.finrank (ZMod 2) (M22Cocode ⧸
        fixedSpaceSpan m22CocodeRepresentation (m22InnerHexadKernel m22SourceOctad)) = 1 ∧
    (∀ I : Submodule (ZMod 2) M22Cocode,
      I ≤ fixedSpace m22CocodeRepresentation (m22InnerHexadKernel m22SourceOctad) →
      Disjoint (I : Set M22Cocode) m22WeightTwoFamily → Module.finrank (ZMod 2) I ≤ 4) ∧
    (∀ A ≤ m22InnerHexadKernel m22SourceOctad, ¬ IsCyclic A →
      fixedSpace m22CocodeRepresentation A =
        fixedSpace m22CocodeRepresentation (m22InnerHexadKernel m22SourceOctad)) ∧
    fixedSpace m22CodeRepresentation (m22InnerHexadKernel m22SourceOctad) =
      Submodule.span (ZMod 2) {codeVector m22SourceOctad m22Pair_le_sourceOctad} := by
  have h5 := h.fixedSpace_finrank h24.displacement h24.fixed_finrank
  refine ⟨h5, h.xi_hyperplane h24.displacement h24.xi_codim
    (h.kernel_ne_bot h24.fixed_finrank), ?_, ?_, ?_⟩
  · exact avoiding_weightTwo_finrank_le m22ToPairStabilizer
      (m22InnerHexadKernel m22SourceOctad) h.kernel_image h5
  · exact fun A hA hnc => h.noncyclic_fixedSpace h24.displacement h24.noncyclic_fixed A hA hnc
  · exact code_fixedSpace_eq_span m22ToPairStabilizer
      (m22InnerHexadKernel m22SourceOctad) m22SourceOctad m22Pair_le_sourceOctad h.kernel_image


/-- H.16.4 with every intermediate H.15.2 cocode-action premise constructed.
The earlier M24 action, H.14 kernel marking, and two prior quintet dimensions
remain explicit for the chapter assembly owner. In particular no M22 chief
flag, transvection image, section identification, or fixed quotient is assumed. -/
theorem outer_code_clauses
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (ht : MathieuCode.Hexad.CocodeAction.Transvections.AmbientTransvectionInput m22SourceOctad)
    (k : MathieuCode.Hexad.Assembly.KernelConjugationInput)
    (hQ : MathieuCode.Hexad.ChiefFlag.QuintetDimensions) :
    MathieuCode.Hexad.ChiefFlag.Actions.CodeChiefActions
        (MathieuCode.Hexad.Assembly.cocodeActionData h h24 ht k) h h24 ∧
      Module.finrank (ZMod 2) MathieuCode.Hexad.ChiefFlag.quintetFixedAnnihilator = 9 ∧
      codeCommutator (m22OuterHexadKernel m22SourceOctad) ≤
        MathieuCode.Hexad.ChiefFlag.quintetFixedAnnihilator ∧
      ¬ codeCommutator (m22OuterHexadKernel m22SourceOctad) ≤
        fixedSpace m22OuterCodeRepresentation (m22OuterQuintetKernel m22SourceSextet) ∧
      MathieuCode.Hexad.ChiefFlag.fixedCodeQuotient =
        MathieuCode.Hexad.ChiefFlag.commutatorImage :=
  MathieuCode.Hexad.Assembly.code_clauses h h24 ht k hQ

end CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad
