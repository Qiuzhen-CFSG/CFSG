module
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.NormalClosure
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.CoefficientNormalizer

/-!
# From a recognized transvection closure to the original group

The normal transvection closure is a literal subgroup of the original
symplectic group. Once its matrix image is a conjugate coefficient copy,
the self-normalizer theorem identifies the original group with that copy.
This discharges the normalizer step of G.4.7 for the actual moving pair;
the model-recognition premise has its independent G.4.1 producer.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open DiagramAutomorphisms.FieldFixedResidual TwoConjugate
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Recognition of the same normal transvection closure identifies the
original matrix subgroup, retaining the literal coefficient embedding. -/
theorem eq_coefficient_copy_of_transvectionClosure_recognized
    (H : Subgroup (Sp F)) (K : Subfield F) (c : Sp F)
    (he : (transvectionClosure H).map H.subtype=
      (coefficientInclusion K).range.map (MulAut.conj c).toMonoidHom) :
    H=(coefficientInclusion K).range.map (MulAut.conj c).toMonoidHom :=
  eq_coefficient_copy_of_normal_recognized H (transvectionClosure H) K c he

/-- The literal opposite pair equals its recognized coefficient subgroup;
no root in the original central subgroup is required. -/
theorem moving_pair_eq_coefficient_copy_of_closure_recognized
    (V : Subgroup (Sp F)) (K : Subfield F) (c : Sp F)
    (he : (transvectionClosure (oppositePair V)).map (oppositePair V).subtype=
      (coefficientInclusion K).range.map (MulAut.conj c).toMonoidHom) :
    oppositePair V=(coefficientInclusion K).range.map (MulAut.conj c).toMonoidHom :=
  eq_coefficient_copy_of_transvectionClosure_recognized (oppositePair V) K c he

end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
