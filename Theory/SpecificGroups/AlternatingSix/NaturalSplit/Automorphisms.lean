module
public import Theory.SpecificGroups.AlternatingSix.NaturalSplit.Restriction

/-!
# Automorphisms of the natural split A₆ block

The deleted binary permutation module parametrizes the automorphisms fixing
translations pointwise. Coordinate permutations act on these cocycles through
the literal deleted action. The normalizer of the natural A₆ image therefore
identifies the full automorphism group with the split group 2⁵:S₆.

Source: Aschbacher–Smith 14.3.19(10). The image-normalizer equality is kept
explicit here and discharged by the existing quasithin natural-six theorem.
-/

@[expose] public section
namespace BinaryPermutation.SixNaturalSplit
open Subgroup SemidirectProduct

noncomputable def deletedAction : Equiv.Perm (Fin 6) →* MulAut (Multiplicative (Deleted (Fin 6))) where
  toFun s := (LinearEquiv.ofBijective (deletedRepresentation (Fin 6) s)
    ((deletedRepresentation (Fin 6)).apply_bijective s)).toAddEquiv.toMultiplicative
  map_one' := by
    apply MulEquiv.ext
    intro d
    apply Multiplicative.toAdd.injective
    exact LinearMap.congr_fun (deletedRepresentation (Fin 6)).map_one d.toAdd
  map_mul' s t := by
    apply MulEquiv.ext
    intro d
    apply Multiplicative.toAdd.injective
    exact LinearMap.congr_fun ((deletedRepresentation (Fin 6)).map_mul s t) d.toAdd

abbrev AutomorphismModel := Multiplicative (Deleted (Fin 6)) ⋊[deletedAction] Equiv.Perm (Fin 6)

noncomputable def kernelHom : Multiplicative (Deleted (Fin 6)) →* MulAut Model :=
  pointwiseKernel.subtype.comp kernelEquiv.toMonoidHom

public theorem kernelHom_restriction (d : Multiplicative (Deleted (Fin 6))) :
    restriction (kernelHom d)=1 := by
  change kernelHom d ∈ restriction.ker
  rw [restriction_ker]
  exact (kernelEquiv d).property

public theorem diagonal_kernel (s : Equiv.Perm (Fin 6)) (d : Multiplicative (Deleted (Fin 6))) :
    diagonal s * kernelHom d = kernelHom (deletedAction s d) * diagonal s := by
  apply MulEquiv.ext
  intro x
  change diagonal s ((kernelEquiv d).val x) = (kernelEquiv (deletedAction s d)).val (diagonal s x)
  rw [kernelEquiv_apply,kernelEquiv_apply]
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    change naturalRepresentation (Fin 6) s
      (x.left.toAdd+(SixNaturalCocycles.deletedEquiv d.toAdd).val x.right) =
        naturalRepresentation (Fin 6) s x.left.toAdd +
          (SixNaturalCocycles.deletedEquiv (deletedRepresentation (Fin 6) s d.toAdd)).val
            (MulAut.conjNormal s x.right)
    rw [map_add,SixNaturalCocycles.deletedEquiv_action]
  · rfl

noncomputable def automorphismHom : AutomorphismModel →* MulAut Model :=
  SemidirectProduct.lift kernelHom diagonal (by
    intro s
    apply MonoidHom.ext
    intro d
    change kernelHom (deletedAction s d)=diagonal s * kernelHom d * (diagonal s)⁻¹
    exact eq_mul_inv_iff_mul_eq.mpr (diagonal_kernel s d).symm)

public theorem automorphismHom_injective : Function.Injective automorphismHom := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  intro x hx
  change kernelHom x.left * diagonal x.right=1 at hx
  have hs := congrArg restriction hx
  rw [map_mul,kernelHom_restriction,restriction_diagonal,map_one,one_mul] at hs
  have hs' : x.right=1 := symmetric_action_injective (hs.trans (map_one _).symm)
  have hd : kernelHom x.left=1 := by simpa only [hs',map_one,mul_one] using hx
  have hd' : x.left=1 := by
    apply kernelEquiv.injective
    rw [map_one]
    exact Subtype.ext hd
  exact SemidirectProduct.ext hd' hs'

public theorem automorphismHom_surjective
    (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range) :
    Function.Surjective automorphismHom := by
  intro a
  obtain ⟨k,s,hks⟩ := exists_kernel_mul_diagonal hN a
  obtain ⟨d,rfl⟩ := kernelEquiv.surjective k
  exact ⟨⟨d,s⟩,hks.symm⟩

noncomputable def automorphismEquiv
    (hN : normalizer (action.range : Set (MulAut Vector)) = (naturalMulAction (Fin 6)).range) :
    MulAut Model ≃* AutomorphismModel :=
  (MulEquiv.ofBijective automorphismHom
    ⟨automorphismHom_injective,automorphismHom_surjective hN⟩).symm

public theorem automorphismModel_card : Nat.card AutomorphismModel=23040 := by
  rw [Nat.card_congr (SemidirectProduct.equivProd : AutomorphismModel ≃ _),Nat.card_prod]
  have h : Nat.card (Multiplicative (Deleted (Fin 6)))=32 := by
    change Nat.card (Deleted (Fin 6))=32
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,finrank_deleted]
    decide
  rw [h,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
  decide

end BinaryPermutation.SixNaturalSplit
