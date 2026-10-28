module
public import Theory.Representation.RankOneSymplectic.PerfectRestriction
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.NormalClosure
public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
/-!
# The perfect normal subgroups of the actual transvection closure

The F-transvections generate their literal normal closure and have rank-one
displacement on the original four-space. Hence every nontrivial perfect
normal subgroup of an irreducible transvection closure acts irreducibly.
In particular this applies to its generalized Fitting layer once its
Fitting subgroup vanishes. Source: Aschbacher--Smith G.4.9, pp.341--342.
-/

public noncomputable section
open Subgroup Module Matrix
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open InvolutionTypes
variable {F : Type*} [Field F]
private theorem action_faithful (H : Subgroup (Sp F)) :
    Function.Injective ((Representation.symplecticNatural 2).comp H.subtype) := by
  intro g h he
  apply Subtype.ext
  apply Subtype.ext
  ext i j
  have hh := congrArg (fun f : Module.End F (Vector F) => f (Pi.single j 1) i) he
  change ((g : Sp F).val *ᵥ Pi.single j 1) i = ((h : Sp F).val *ᵥ Pi.single j 1) i at hh
  simpa using hh

/-- Perfect normal restriction for the literal F-transvection closure. -/
theorem closure_perfect_normal_irreducible (H : Subgroup (Sp F))
    (hi : Representation.IsIrreducible (((Representation.symplecticNatural 2).comp H.subtype).comp
      (transvectionClosure H).subtype))
    (N : Subgroup (transvectionClosure H)) [N.Normal] [Group.IsPerfect N] (hn : N≠⊥) :
    Representation.IsIrreducible ((((Representation.symplecticNatural 2).comp H.subtype).comp
      (transvectionClosure H).subtype).comp N.subtype) := by
  let ρ : Representation F (transvectionClosure H) (Vector F) :=
    ((Representation.symplecticNatural 2).comp H.subtype).comp (transvectionClosure H).subtype
  let : ρ.IsIrreducible := hi
  have hf : Function.Injective ρ := (action_faithful H).comp (transvectionClosure H).subtype_injective
  apply Representation.RankOneSymplectic.normal_perfect_irreducible ρ hf
    {d | InvolutionTypes.IsB1 ((d : H) : Sp F)} (transvectionClosure_generated H) _ N hn
  intro d hd
  change finrank F (movedSpace ((d : H) : Sp F))=1
  exact hd.2
end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
