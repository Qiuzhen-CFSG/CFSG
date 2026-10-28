module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag

/-!
# The complete conditional outer M22 code chief flag

The literal kernel, fixed code line and commutator are retained. Duality gives
the flag and actions, while the native cubic calculation proves the quotient
fixed-space equality. The geometric comparison uses the compatible marked
sextet and the annihilator of the actual quintet cocode fixed space.

The parent source assembly must supply the precise H.15.2 cocode action
witnesses, the earlier H.14 kernel conjugation marking, M24/H.14 restriction
inputs and the two quintet fixed dimensions. The native order-three bound is
proved internally. The existing prefix and geometric APIs are preserved.

Source: Aschbacher--Smith, H.16.4(1)--(5), printed p.403, combined manuscript
of 1 March 2004.
-/

public section
noncomputable section
open MathieuCode MathieuCode.Hexad MathieuCode.Hexad.ChiefFlag
open Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad

theorem outer_code_prefix (h : OuterRestrictionInput m22SourceOctad)
    (h24 : AmbientFixedInput m22SourceOctad) :
    ⊥ < fixedSpace m22OuterCodeRepresentation (m22OuterHexadKernel m22SourceOctad) ∧
      fixedSpace m22OuterCodeRepresentation (m22OuterHexadKernel m22SourceOctad) <
        codeCommutator (m22OuterHexadKernel m22SourceOctad) ∧
      codeCommutator (m22OuterHexadKernel m22SourceOctad) < ⊤ :=
  code_prefix_strict h h24

theorem outer_code_geometric_comparison (h : OuterRestrictionInput m22SourceOctad)
    (h24 : AmbientFixedInput m22SourceOctad) (hQ : QuintetDimensions) :
    Module.finrank (ZMod 2) quintetFixedAnnihilator = 9 ∧
      codeCommutator (m22OuterHexadKernel m22SourceOctad) ≤ quintetFixedAnnihilator ∧
      ¬ codeCommutator (m22OuterHexadKernel m22SourceOctad) ≤
        fixedSpace m22OuterCodeRepresentation (m22OuterQuintetKernel m22SourceSextet) :=
  geometric_comparison h h24 hQ

/-- The complete H.15.2-to-H.16.4 implication. The cocode witnesses contain
actual linear equivalences and conjugation equations, not code conclusions;
the source assembly remains responsible for constructing them and the stated
earlier group and quintet inputs. -/
theorem outer_code_chief_flag {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (D : Actions.CocodeActionData E) (K : Actions.KernelModel D)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (hQ : QuintetDimensions) :
    Actions.CodeChiefActions D h h24 ∧
      Module.finrank (ZMod 2) quintetFixedAnnihilator = 9 ∧
      codeCommutator (m22OuterHexadKernel m22SourceOctad) ≤ quintetFixedAnnihilator ∧
      ¬ codeCommutator (m22OuterHexadKernel m22SourceOctad) ≤
        fixedSpace m22OuterCodeRepresentation (m22OuterQuintetKernel m22SourceSextet) ∧
      fixedCodeQuotient = commutatorImage :=
  code_chief_flag D K h h24 hQ

end CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad
