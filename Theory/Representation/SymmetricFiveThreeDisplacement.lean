module
public import Theory.Representation.BinarySymmetricThreeNormalizer
public import Theory.Representation.BinaryPermutation.ThreeTensorDisplacement
public import Theory.Representation.AlternatingFiveInvolutionDisplacement
public import Theory.LinearAlgebra.DisplacementFiltration

/-!
# Displacement in a faithful binary S₅ × S₃ action

When the normal cubic subgroup of the S₃ factor moves the whole module,
the inverted-cubic coordinates construct two isomorphic faithful S₅ modules.
An involution in the A₅ component consequently moves at least four dimensions.
Every element of displacement at most one is the identity: pure S₅ actors
have twice their multiplicity displacement, and a nontrivial S₃ component
moves at least the multiplicity dimension.

The A₅ lower bound uses an order-five commutator, so no classification of
irreducible S₅ modules is needed. These are the representation calculations
in the last paragraph of Aschbacher–Smith 12.6, printed p.838 (PDF p.855).
-/

public section
open Module Subgroup Representation Representation.BinaryOffender InvertedCubicTensor
namespace Representation.SymmetricFiveThree
abbrev S₅ := Equiv.Perm (Fin 5)
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

variable (ρ : Representation (ZMod 2) (S₅ × S₃) V)
    (hf : Function.Injective ρ)
    (hfree : fixedSpace (rightAction ρ) (alternatingGroup (Fin 3)) = ⊥)

include hf hfree

omit [FiniteDimensional (ZMod 2) V] in
/-- Each constructed S₅ summand retains faithfulness of the full action. -/
theorem multiplicity_faithful : Function.Injective (productMultiplicity ρ) := by
  apply multiplicity_injective (rightAction ρ) (leftAction ρ) (product_commute ρ)
    ((fixedFree_iff_fixedSpace_eq_bot _).mpr hfree)
  exact hf.comp (fun _ _ h => congrArg Prod.fst h)

/-- The actual A₅ involution moves at least two dimensions in each copy. -/
theorem component_displacement (a : alternatingGroup (Fin 5)) (ha : orderOf a = 2) :
    4 ≤ finrank (ZMod 2) (ρ (a.val, 1) - LinearMap.id).range := by
  let τ := (productMultiplicity ρ).comp (alternatingGroup (Fin 5)).subtype
  have hi : Function.Injective τ :=
    (multiplicity_faithful ρ hf hfree).comp Subtype.val_injective
  have hlo := AlternatingFiveInvolutionDisplacement.displacement_lower τ hi a ha
  have hh := LinearMap.finrank_range_add_le_of_intertwining_prod
    (ρ (a.val, 1) - LinearMap.id)
    (productMultiplicity ρ a.val - LinearMap.id)
    (productMultiplicity ρ a.val - LinearMap.id)
    (productPairEquiv ρ hfree).symm (by
      intro v
      have he := productPairEquiv_equivariant ρ hfree a.val
        ((productPairEquiv ρ hfree).symm v)
      apply (productPairEquiv ρ hfree).injective
      simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub,
        LinearEquiv.apply_symm_apply]
      simp only [LinearEquiv.apply_symm_apply] at he
      rw [← he]
      change _ = (productPairEquiv ρ hfree)
        ((productMultiplicity ρ a.val ((productPairEquiv ρ hfree).symm v).1,
          productMultiplicity ρ a.val ((productPairEquiv ρ hfree).symm v).2) -
          (productPairEquiv ρ hfree).symm v)
      rw [map_sub, LinearEquiv.apply_symm_apply])
  change 2 ≤ finrank (ZMod 2) (productMultiplicity ρ a.val - LinearMap.id).range at hlo
  dsimp only [InvertedCubicTensor.F] at hh
  omega

private theorem multiplicity_dimension : 2 ≤ finrank (ZMod 2) (multiplicitySpace (rightAction ρ)) := by
  let a : alternatingGroup (Fin 5) := ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
  have ha : orderOf a = 2 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
  have hl := AlternatingFiveInvolutionDisplacement.displacement_lower
    ((productMultiplicity ρ).comp (alternatingGroup (Fin 5)).subtype)
    ((multiplicity_faithful ρ hf hfree).comp Subtype.val_injective) a ha
  exact hl.trans (Submodule.finrank_le _)

/-- There are no transvections anywhere in the faithful product action. -/
theorem no_transvection (g : S₅ × S₃)
    (hg : finrank (ZMod 2) (ρ g - LinearMap.id).range ≤ 1) : g = 1 := by
  have he := fixedCodim_map_equivariant
    (BinaryPermutation.ThreeTensor.action (productMultiplicity ρ)) ρ
    (MonoidHom.id _) (productTensorEquiv ρ hfree)
    (fun g v => productTensorEquiv_equivariant ρ hfree g v) (zpowers g)
  rw [Subgroup.map_id, fixedCodim_zpowers_eq_displacement_rank,
    fixedCodim_zpowers_eq_displacement_rank] at he
  by_cases hs : g.2 = 1
  · have hgg : g = (g.1, 1) := Prod.ext rfl hs
    rw [hgg, BinaryPermutation.ThreeTensor.displacement_first] at he
    rw [hgg] at hg
    dsimp only [InvertedCubicTensor.F] at he
    have hz : finrank (ZMod 2) (productMultiplicity ρ g.1 - LinearMap.id).range = 0 := by omega
    have hm : productMultiplicity ρ g.1 = 1 := by
      apply sub_eq_zero.mp
      apply LinearMap.range_eq_bot.mp
      exact Submodule.finrank_eq_zero.mp hz
    have hfirst : g.1 = 1 := (multiplicity_faithful ρ hf hfree) (hm.trans (map_one _).symm)
    exact Prod.ext hfirst hs
  · have hl := BinaryPermutation.ThreeTensor.dimension_le_displacement
      (productMultiplicity ρ) g hs
    have hd := multiplicity_dimension ρ hf hfree
    rw [he] at hl
    dsimp only [InvertedCubicTensor.F] at hl
    omega

end Representation.SymmetricFiveThree
