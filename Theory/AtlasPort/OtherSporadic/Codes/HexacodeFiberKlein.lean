/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeFiberPermutation
public import Theory.AtlasPort.OtherSporadic.GroupTheory.KleinFourRegular

/-!
# HexacodeFiberKlein

The kernel of the action on nonzero double-zero words is the natural Klein four subgroup
on the complementary coordinates. Its coordinate equivalence transports the regular
action on those four positions.

Source: `Atlas/Codes/HexacodeFiberKlein.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

theorem hexFiberFourPositions_card (i j : HexIndex) (hij : i ≠ j) :
    Nat.card (({i,j} : Finset HexIndex)ᶜ : Finset HexIndex) = 4 := by
  classical
  rw [Nat.card_eq_fintype_card,Fintype.card_coe,Finset.card_compl]
  simp [HexIndex,hij]

theorem hexFiberPermutation_kernel_natural (i j : HexIndex) (hij : i ≠ j) :
    (hexFiberPermutationHom i j).ker.map (hexFiberA4Equiv i j).toMonoidHom =
      alternatingGroup.kleinFour (({i,j} : Finset HexIndex)ᶜ : Finset HexIndex) := by
  classical
  let W := (hexFiberPermutationHom i j).ker.map (hexFiberA4Equiv i j).toMonoidHom
  have hc : Nat.card W = 4 := by
    rw [← Nat.card_congr ((hexFiberPermutationHom i j).ker.equivMapOfInjective
      (hexFiberA4Equiv i j).toMonoidHom (hexFiberA4Equiv i j).injective).toEquiv]
    exact hexFiberPermutation_kernel_card i j hij
  have hp : IsPGroup 2 W := IsPGroup.of_card (n := 2) hc
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  rw [alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four
    (hexFiberFourPositions_card i j hij) S] at hS
  exact Subgroup.eq_of_le_of_card_ge hS (by
    rw [hc,alternatingGroup.kleinFour_card_of_card_eq_four
      (hexFiberFourPositions_card i j hij)])

def hexFiberKernelKleinEquiv (i j : HexIndex) (hij : i ≠ j) :
    (hexFiberPermutationHom i j).ker ≃*
      alternatingGroup.kleinFour (({i,j} : Finset HexIndex)ᶜ : Finset HexIndex) :=
  ((hexFiberPermutationHom i j).ker.equivMapOfInjective
    (hexFiberA4Equiv i j).toMonoidHom (hexFiberA4Equiv i j).injective).trans
      (MulEquiv.subgroupCongr (hexFiberPermutation_kernel_natural i j hij))

theorem hexFiberKernel_regular (i j : HexIndex) (hij : i ≠ j)
    (x y : (({i,j} : Finset HexIndex)ᶜ : Finset HexIndex)) :
    ∃! g : (hexFiberPermutationHom i j).ker,
      hexPointKernelCoordinate i g.val.val x.val = y.val := by
  classical
  let e := hexFiberKernelKleinEquiv i j hij
  obtain ⟨k,hk,hunique⟩ := Atlas.GroupTheory.kleinFour_regular
    (hexFiberFourPositions_card i j hij) x y
  refine ⟨e.symm k,?_,?_⟩
  · change hexPointKernelCoordinate i (e.symm k).val.val x.val = y.val
    rw [← hexFiberA4Equiv_apply i j (e.symm k).val x]
    have he : (hexFiberA4Equiv i j (e.symm k).val) = k.val :=
      congrArg Subtype.val (e.apply_symm_apply k)
    rw [he,hk]
  · intro g hg
    apply e.injective
    rw [e.apply_symm_apply]
    apply hunique
    apply Subtype.ext
    change ((hexFiberA4Equiv i j g.val).val x).val = y.val
    rwa [hexFiberA4Equiv_apply]

end Atlas.Codes
