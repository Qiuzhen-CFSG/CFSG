module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Embedding
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.SubfieldOvergroups.FieldMaps
public import Mathlib.RepresentationTheory.Invariants

/-!
# The two independent inputs to the basic Ree involution calculation

The group input says that each nonidentity involution in the large Ree group
inverts a conjugate of an element of order five or thirteen in its binary
subfield group. The representation input concerns those odd-order elements
on all exceptional basic factors of dimension at least 26, with the actual
coefficient embedding into the algebraic carrier.

These are unproved input propositions, not certificates carried by the
representations. `BasicInvolutions` proves their combined consequence,
including every exceptional twist. Guralnick--Malle, *Classification of
2F-modules, II*, Lemma 8.8, internal p.57, supplies the source route for
involution coverage and the degree-26 case. Its preceding degree exclusion
does not establish the odd-element bound on the larger basic modules.
-/

@[expose] public section

open Representation Subgroup
open ReeF4.BinaryDegree.ExceptionalTensor

namespace ReeF4.FixedSpaceEstimate.BasicInvolutions

universe u

/-- The source's inversion witnesses, marked in the literal binary subfield
group. This proposition makes no assertion about a representation. -/
def BinaryOddInversionCoverage (m : ℕ) : Prop :=
  ∀ t : Model m, t ≠ 1 → t ^ 2 = 1 →
    ∃ (e : CoefficientField 0 →+* CoefficientField m) (x : Model 0) (c : Model m),
      (orderOf x = 5 ∨ orderOf x = 13) ∧
      t * (c * Subfield.reeMap (by simp) e x * c⁻¹) * t⁻¹ =
        (c * Subfield.reeMap (by simp) e x * c⁻¹)⁻¹

/-- The remaining odd-element calculation on actual basic highest-weight
modules. It includes the larger basic factors, not only degree 26. -/
def BinaryOddDisplacement (F : Type u) [Field F] [IsAlgClosed F] : Prop :=
  ∀ B : AlgebraicFactor F, B.IsExceptionalBasic → 26 ≤ Module.finrank F B.Space →
    ∀ (f : CoefficientField 0 →+* F) (x : Model 0),
      (orderOf x = 5 ∨ orderOf x = 13) →
      20 ≤ Module.finrank F (B.Space ⧸ invariants
        ((B.restrict ((Classification.splitEmbedding f).comp (toSplitGroup 0))).ρ.comp
          (zpowers x).subtype))

end ReeF4.FixedSpaceEstimate.BasicInvolutions
