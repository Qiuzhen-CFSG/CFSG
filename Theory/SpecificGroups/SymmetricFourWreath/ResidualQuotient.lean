module
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation
public import Theory.GroupTheory.WreathTwoThreeCore
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# The two-core quotient of the symmetric-four wreath product

The quotient maps from each symmetric-four base factor to the symmetric group
on three letters give a surjection of wreath products. Its kernel has exponent
two, and its target has trivial two-core. Thus its kernel is the actual
two-core, giving an explicit quotient equivalence with the binary-plane actor.

Source application: the four-block local model in Aschbacher–Smith, Chapter E,
Section 2.5. Only the existing symmetric-four quotient is used; the wreath
kernel and surjectivity arguments are structural.
-/

open Subgroup
namespace SymmetricFourWreath
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev W4 := RegularWreathProduct (Equiv.Perm (Fin 4)) C2
private abbrev W3 := RegularWreathProduct (Equiv.Perm (Fin 3)) C2
private abbrev Actor := Theory.GroupTheory.WreathTwoResidual.Actor
private def wreathQuotient : W4 →* W3 where
  toFun x := ⟨fun i => Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom (x.left i),x.right⟩
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp
private theorem wreathQuotient_surjective : Function.Surjective wreathQuotient := by
  intro x
  choose a ha using fun i => Theory.SpecificGroups.SymmetricSix.DuadCalculation.quotientHom_surjective (x.left i)
  exact ⟨⟨a,x.right⟩,RegularWreathProduct.ext (funext ha) rfl⟩
private theorem wreathQuotient_kernel_two : IsPGroup 2 wreathQuotient.ker := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  have hr : x.val.right = 1 := congrArg RegularWreathProduct.right x.property
  have hl (i : C2) : x.val.left i ∈ Theory.SpecificGroups.SymmetricSix.DuadCalculation.core :=
    congrArg (fun w : W3 => w.left i) x.property
  change x.val ^ 2 = 1
  apply RegularWreathProduct.ext
  · funext i
    simpa [pow_two, hr] using
      elemPow_eq_one_of_isElementaryAbelian (p := 2) (x.val.left i) (hl i)
  · simp [pow_two, hr]
private noncomputable def wreathThreeActorEquiv : W3 ≃* Actor :=
  RegularWreathProduct.congr
    (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three).symm (MulEquiv.refl C2)
private theorem wreathThree_twoCore : pCore 2 W3 = ⊥ := by
  apply map_injective (f := wreathThreeActorEquiv.toMonoidHom) wreathThreeActorEquiv.injective
  rw [pCore_map_iso, Theory.GroupTheory.WreathTwoResidual.twoCore_eq_bot, Subgroup.map_bot]
private theorem wreathQuotient_ker : wreathQuotient.ker = pCore 2 W4 := by
  apply le_antisymm
  · exact le_sSup ⟨inferInstance, wreathQuotient_kernel_two⟩
  have hm : ((pCore 2 W4).map wreathQuotient).Normal :=
    (inferInstance : (pCore 2 W4).Normal).map _ wreathQuotient_surjective
  have hle : (pCore 2 W4).map wreathQuotient ≤ pCore 2 W3 :=
    le_sSup ⟨hm, pCore_isPGroup.map wreathQuotient⟩
  rw [wreathThree_twoCore] at hle
  exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hle)
public noncomputable def quotientEquivActor :
    (RegularWreathProduct (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2)) ⧸
      pCore 2 (RegularWreathProduct (Equiv.Perm (Fin 4)) (Multiplicative (ZMod 2)))) ≃*
      Theory.GroupTheory.WreathTwoResidual.Actor :=
  (QuotientGroup.quotientMulEquivOfEq wreathQuotient_ker.symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective wreathQuotient wreathQuotient_surjective).trans
      wreathThreeActorEquiv)

end SymmetricFourWreath
