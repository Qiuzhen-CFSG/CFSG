module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Quintet
public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Defs

/-!
# Quotient and duality deductions for H.15.4 and H.16.3

These deductions use the literal M22 modules and the certified compatible
sextet. The M24 middle-space dimension drops by one under the pair quotient.
Generation by elementary four-subgroup fixed spaces implies the hyperplane
xi conclusion. An actual natural S5 quotient marking, together with the
setwise stabilizer calculation, determines the ambient code centralizer.

The source chief factors, full transvection images, fixed dimensions,
four-subgroup generation and stabilizer recovery are not proved by this
module: the stated earlier inputs must still be discharged in source assembly.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
H.15.4 and H.16.3, printed pp.400,403.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterH.Section13To16
open MathieuCode Representation.BinaryOffender

/-- The M24 geometric dimension gives the M22 geometric dimension through
the literal quotient, since the pair line lies in the compatible sextet space. -/
theorem m22Quintet_middle_finrank_of_sextet
    (h : Module.finrank (ZMod 2) (CocodeLocal.sextetPairSpace m22SourceSextet) = 7) :
    Module.finrank (ZMod 2) M22Quintet.V6 = 6 :=
  M22Quintet.finrank_V6_of_U7 h

/-- This is the final implication from clause (4) to the xi part of clause (3),
with the four-subgroup generation premise still explicit. -/
theorem m22Quintet_fixedSpan_of_four_generation
    (hgen : M22Quintet.fourFixedSpan m22OuterCocodeRepresentation M22Quintet.K = ⊤)
    (A : Subgroup m22PairStabilizer) (hindex : A.relIndex M22Quintet.K = 2) :
    fixedSpaceSpan m22OuterCocodeRepresentation A = ⊤ :=
  M22Quintet.fixedSpaceSpan_eq_top_of_fourFixedSpan _ hindex hgen

/-- The source centralizer calculation from an actual quotient marking and
the native setwise stabilizer, including its two-group conclusion. -/
theorem m22Quintet_code_centralizer_of_natural_quotient
    (q : M22Quintet.Q →* Equiv.Perm (Fin 5))
    (e : (M22Cocode ⧸ M22Quintet.V6) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 5))
    (he : ∀ (g : M22Quintet.Q) v,
      e (M22Quintet.V6Subrepresentation.quotientRepresentation g v) =
        BinaryPermutation.naturalRepresentation (Fin 5) (q g) (e v))
    (hstab : subspaceStabilizer m22OuterCodeRepresentation M22Quintet.V4 = M22Quintet.Q)
    (hker : q.ker = M22Quintet.K.subgroupOf M22Quintet.Q) :
    subspaceKernel m22OuterCodeRepresentation M22Quintet.V4 ⊤ = M22Quintet.K ∧
      IsPGroup 2 (subspaceKernel m22OuterCodeRepresentation M22Quintet.V4 ⊤) := by
  have h := M22Quintet.V4_centralizer_eq_of_natural_quotient q e he hstab hker
  refine ⟨h, ?_⟩
  rw [h]
  exact M22Quintet.K_isTwoGroup

end CFSG.Quasithin.ChapterH.Section13To16
