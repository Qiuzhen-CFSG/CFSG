module
public import Theory.Representation.FirstCohomologySemidirect
public import Theory.Representation.BinaryPermutation.SixNaturalCocycles
public import Theory.Representation.BinaryPermutationMulAction
public import Theory.Representation.BinaryPermutation.Faithful
public import Theory.ElementaryAbelian.Basic

/-!
# The natural split binary A₆ block

The carrier is the literal semidirect product of the binary six-letter
natural module by A₆. Its automorphisms fixing the normal sixteen-group
pointwise are parametrized by the deleted permutation module. Thus this
actual automorphism kernel is elementary abelian of order thirty-two.

Source: Aschbacher–Smith 14.3.19(9–10), using I.1.6(1).
-/

@[expose] public section
namespace BinaryPermutation.SixNaturalSplit
open Representation.OneCohomology SemidirectProduct
abbrev Actor := alternatingGroup (Fin 6)
abbrev Vector := Multiplicative (natural (Fin 6))
noncomputable def action : Actor →* MulAut Vector :=
  (naturalMulAction (Fin 6)).comp Actor.subtype
abbrev Model := Vector ⋊[action] Actor

theorem symmetric_action_injective : Function.Injective (naturalMulAction (Fin 6)) := by
  intro s t h
  apply naturalRepresentation_injective (Fin 6) (by decide)
  apply LinearMap.ext
  intro v
  exact congrArg Multiplicative.toAdd (MulEquiv.congr_fun h (Multiplicative.ofAdd v))

theorem action_injective : Function.Injective action :=
  symmetric_action_injective.comp Subtype.val_injective

theorem action_apply (g : Actor) (v : Vector) :
    (action g v).toAdd = alternatingNaturalRepresentation (Fin 6) g v.toAdd := rfl

noncomputable abbrev pointwiseKernel := splitPointwiseKernel action

noncomputable def kernelEquiv : Multiplicative (Deleted (Fin 6)) ≃* pointwiseKernel :=
  (AddEquiv.toMultiplicative SixNaturalCocycles.deletedEquiv.toAddEquiv).trans
    (splitCocycleEquiv (alternatingNaturalRepresentation (Fin 6)) action action_apply action_injective)

theorem pointwiseKernel_card : Nat.card pointwiseKernel=32 := by
  rw [← Nat.card_congr kernelEquiv.toEquiv]
  change Nat.card (Deleted (Fin 6))=32
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,finrank_deleted]
  decide

instance pointwiseKernel_elementary : IsElementaryAbelian 2 pointwiseKernel where
  toIsMulCommutative := IsMulCommutative.of_comm (by
    intro a b
    apply kernelEquiv.symm.injective
    simp only [map_mul]
    exact mul_comm _ _)
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro a
    apply kernelEquiv.symm.injective
    rw [map_pow,map_one,pow_two]
    apply Multiplicative.toAdd.injective
    change (kernelEquiv.symm a).toAdd + (kernelEquiv.symm a).toAdd = 0
    rw [← two_nsmul,← Nat.cast_smul_eq_nsmul (ZMod 2) 2]
    exact zero_smul (ZMod 2) _)

theorem kernelEquiv_apply (d : Multiplicative (Deleted (Fin 6))) (x : Model) :
    (kernelEquiv d).val x =
      ⟨Multiplicative.ofAdd (x.left.toAdd + (SixNaturalCocycles.deletedEquiv d.toAdd).val x.right),x.right⟩ := by
  change (splitCocycleEquiv (alternatingNaturalRepresentation (Fin 6)) action action_apply
    action_injective (Multiplicative.ofAdd (SixNaturalCocycles.deletedEquiv d.toAdd))).val x = _
  rw [splitCocycleEquiv_apply]
  rfl

end BinaryPermutation.SixNaturalSplit
