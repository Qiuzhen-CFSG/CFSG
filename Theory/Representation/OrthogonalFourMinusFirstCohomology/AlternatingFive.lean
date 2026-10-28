module

public import Theory.Representation.OrthogonalFourMinusFirstCohomology.AlternatingFive.Intertwining
public import Theory.Representation.OrthogonalFourMinusFirstCohomology

/-!
# The small orthogonal module is the natural A₅ module

This interface gives actual group and binary linear equivalences, together
with their action compatibility, for the canonical finite Hermitian model
at `n = 1`. The target is `BinaryPermutation.natural (Fin 5)` with its
permutation action restricted along the alternating subgroup inclusion.

The construction uses the five singular matrices, their sum relation and
their spanning property; see `AlternatingFive.Geometry` and
`AlternatingFive.Intertwining`. The formulas here apply directly to the
existing binary SL₂ representation, the canonical PSL₂ representation,
and the faithful matrix-action image. They discharge the module-identification
premise needed to transport the separate A₅ projectivity result.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma I.1.6(3), printed p.408 (PDF p.419).
-/

@[expose] public section

noncomputable section
namespace Representation.OrthogonalFourMinus.AlternatingFive
open FiniteModel

/-- The target is the natural permutation module restricted to the alternating subgroup. -/
def alternatingRepresentation :
    Representation (ZMod 2) (alternatingGroup (Fin 5)) (BinaryPermutation.natural (Fin 5)) :=
  (BinaryPermutation.naturalRepresentation (Fin 5)).comp (alternatingGroup (Fin 5)).subtype

/-- The canonical binary SL₂ representation is intertwined with the A₅ natural representation. -/
theorem binaryAction_intertwines (g : Group) (X : Space 1) :
    moduleEquiv (binaryAction 1 g X) =
      alternatingRepresentation (groupEquiv g) (moduleEquiv X) :=
  intertwines g X

/-- The projective identification uses the canonical characteristic-two SL₂ quotient. -/
def psl2GroupEquiv : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (Field 1) ≃*
    alternatingGroup (Fin 5) :=
  (sl2EquivPSL2 1).symm.trans groupEquiv

/-- The source's actual PSL₂ orthogonal module is the A₅ natural module. -/
theorem binaryPSL2Action_intertwines
    (g : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (Field 1)) (X : Space 1) :
    moduleEquiv (binaryPSL2Action 1 g X) =
      alternatingRepresentation (psl2GroupEquiv g) (moduleEquiv X) :=
  intertwines ((sl2EquivPSL2 1).symm g) X

/-- The same group identification on the faithful matrix-action image. -/
def imageGroupEquiv : actionImage 1 ≃* alternatingGroup (Fin 5) :=
  (sl2EquivActionImage 1).symm.trans groupEquiv

/-- Compatibility with the action image's literal action on Hermitian matrices. -/
theorem actionImage_intertwines (g : actionImage 1) (X : Space 1) :
    moduleEquiv (g • X) =
      alternatingRepresentation (imageGroupEquiv g) (moduleEquiv X) := by
  obtain ⟨a, rfl⟩ := (sl2EquivActionImage 1).surjective g
  simpa only [sl2EquivActionImage_smul, imageGroupEquiv, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, binaryAction_apply]
    using binaryAction_intertwines a X

end Representation.OrthogonalFourMinus.AlternatingFive
