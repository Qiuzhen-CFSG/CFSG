module
public import Theory.Representation.PSL3Two.NaturalDualNonFF
public import Theory.Representation.PSL3Two.NaturalDualCoreObstruction

/-!
# The binary doubled action at an odd fixed residual

The marked natural–dual action has no FF offender on its faithful image.
Surjectivity of the actor map also excludes both six-dimensional Fano
permutation cores. Every automorphism of SL₃(2) is implemented on the pair,
so these exclusions survive every choice of the residual quotient marking.
The point and line cores remain distinct throughout the argument.

`NonFFSourceDoubledBinaryOddAction` applies these facts to the original
C_L(A)^∞ and its full two-core quotient, on the whole chosen orbit.
These are the module exclusions used in 4.4.3; the ambient normalizer
alternative must still be established from the source hypotheses.
Source: Aschbacher–Smith 4.4.3(2.i,iii), printed p.619, and 7.3.4/7.6.1,
printed pp.699,702, refs/quasithin.pdf; the Fano-core structure is H.5.3.
-/

public noncomputable section
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddAction
open BinaryLinearThree

private theorem twist_operator (a : MulAut Group) :
    ∃ e : NaturalDual.Space ≃ₗ[ZMod 2] NaturalDual.Space,
      ∀ g v, e (NaturalDual.action g v) = NaturalDual.action (a g) (e v) := by
  by_cases hi : a ∈ MulAut.innerSubgroup Group
  · obtain ⟨g,rfl⟩ := hi
    exact ⟨NaturalDual.innerOperator g,NaturalDual.innerOperator_covariance g⟩
  · obtain ⟨g,hg⟩ := AutomorphismAction.outer_eq_inner_graph a hi
    refine ⟨NaturalDual.graphSwap.trans (NaturalDual.innerOperator g),?_⟩
    intro k v
    change NaturalDual.innerOperator g (NaturalDual.graphSwap (NaturalDual.action k v)) = _
    rw [NaturalDual.graphSwap_covariance,NaturalDual.innerOperator_covariance,hg]
    rfl

variable {J U : Type*} [_root_.Group J] [AddCommGroup U] [Module (ZMod 2) U]
  (ρ : Representation (ZMod 2) J U) (q : J →* Group)
  (E : U ≃ₗ[ZMod 2] NaturalDual.Space)
  (hE : ∀ j v, E (ρ j v) = NaturalDual.action (q j) (E v))

include q E hE

/-- The faithful image of the whole marked pair has no FF offender. -/
theorem not_ff : ¬ IsFFModule (imageRepresentation ρ) := by
  intro hf
  apply NaturalDual.not_isFFModule_image_of_covariance
    (NaturalDual.action.comp q) (MulAut.conj.comp q) ?_
  · exact image_isFFModule_of_equivariant (NaturalDual.action.comp q) ρ
      (MonoidHom.id J) Function.surjective_id E (fun j v => (hE j v).symm) hf
  · intro j g v
    change NaturalDual.action (q j) (NaturalDual.action g v) =
      NaturalDual.action (q j * g * (q j)⁻¹) (NaturalDual.action (q j) v)
    simp only [← Module.End.mul_apply,← map_mul]
    simp [mul_assoc]

/-- Even an arbitrary reorientation of the quotient cannot make the split
pair a point permutation core. -/
theorem not_point_core (hq : Function.Surjective q) (a : MulAut Group) :
    ¬ Nonempty (ρ.Equiv (U₂.comp (a.toMonoidHom.comp q))) := by
  rintro ⟨e⟩
  obtain ⟨b,hb⟩ := twist_operator a
  let c := (e.symm.toLinearEquiv.trans E).trans b
  apply NaturalDualCoreObstruction.pointCore_not_equiv_naturalDual
  refine ⟨Representation.Equiv.mk c ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  obtain ⟨j,hj⟩ := (a.surjective.comp hq) g
  subst g
  change b (E (e.symm (U₂ (a (q j)) v))) = _
  have he := LinearMap.congr_fun (e.symm.isIntertwining' j) v
  change e.symm (U₂ (a (q j)) v) = ρ j (e.symm v) at he
  rw [he,hE,hb]
  rfl

/-- The other Fano orientation is excluded on the same marked pair. -/
theorem not_line_core (hq : Function.Surjective q) (a : MulAut Group) :
    ¬ Nonempty (ρ.Equiv
      (FanoDecomposition.lineCoreRepresentation.comp (a.toMonoidHom.comp q))) := by
  rintro ⟨e⟩
  obtain ⟨b,hb⟩ := twist_operator a
  let c := (e.symm.toLinearEquiv.trans E).trans b
  apply NaturalDualCoreObstruction.lineCore_not_equiv_naturalDual
  refine ⟨Representation.Equiv.mk c ?_⟩
  intro g
  apply LinearMap.ext
  intro v
  obtain ⟨j,hj⟩ := (a.surjective.comp hq) g
  subst g
  change b (E (e.symm (FanoDecomposition.lineCoreRepresentation (a (q j)) v))) = _
  have he := LinearMap.congr_fun (e.symm.isIntertwining' j) v
  change e.symm (FanoDecomposition.lineCoreRepresentation (a (q j)) v) =
    ρ j (e.symm v) at he
  rw [he,hE,hb]
  rfl

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryOddAction
