/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeLocalSimple

/-!
# HexacodeFiberStabilizer

Fixing a second coordinate in the local hexacode kernel gives the natural alternating
group on the complementary coordinates. Restriction of the coordinate equivalence
constructs this identification and yields order twelve when the two coordinates differ.

Source: `Atlas/Codes/HexacodeFiberStabilizer.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

def hexFiberStabilizer (i j : HexIndex) : Subgroup (hexPointKernel i) :=
  (MulAction.stabilizer (Equiv.Perm HexIndex) j).comap (hexPointKernelCoordinate i)

def hexFiberAlternatingHom (i j : HexIndex) : hexFiberStabilizer i j →*
    fixingSubgroup (alternatingGroup HexIndex) ({i,j} : Set HexIndex) where
  toFun g := ⟨(hexPointKernelAlternating i g.val).val, by
    intro x
    rcases x.prop with h | h
    · change hexPointKernelCoordinate i g.val x.val = x.val
      rw [h]
      exact g.val.val.prop
    · change hexPointKernelCoordinate i g.val x.val = x.val
      rw [h]
      exact g.prop⟩
  map_one' := by
    apply Subtype.ext
    exact congrArg (fun x : HexEvenPoint i => x.val) (map_one (hexPointKernelAlternating i))
  map_mul' g h := by
    apply Subtype.ext
    exact congrArg (fun x : HexEvenPoint i => x.val)
      (map_mul (hexPointKernelAlternating i) g.val h.val)

theorem hexFiberAlternatingHom_bijective (i j : HexIndex) :
    Function.Bijective (hexFiberAlternatingHom i j) := by
  constructor
  · intro g h he
    apply Subtype.ext
    apply hexPointKernelCoordinate_injective i
    exact congrArg (fun x => x.val.val) he
  · intro g
    have hi : g.val.val i = i := g.prop ⟨i,Or.inl rfl⟩
    have hj : g.val.val j = j := g.prop ⟨j,Or.inr rfl⟩
    obtain ⟨b,hb⟩ := hexPointKernel_coordinate_image i g.val.val hi g.val.prop
    have hbj : b ∈ hexFiberStabilizer i j := by
      change hexPointKernelCoordinate i b j = j
      rwa [hb]
    refine ⟨⟨b,hbj⟩,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hb

def hexFiberA4Equiv (i j : HexIndex) : hexFiberStabilizer i j ≃*
    alternatingGroup (({i,j} : Finset HexIndex)ᶜ : Finset HexIndex) := by
  classical
  exact (MulEquiv.ofBijective (hexFiberAlternatingHom i j)
    (hexFiberAlternatingHom_bijective i j)).trans
      ((MulEquiv.subgroupCongr (by congr 1; ext x; simp)).trans
        (Atlas.Families.Alternating.stabilizerComplementEquiv {i,j}))

theorem hexFiberStabilizer_card (i j : HexIndex) (hij : i ≠ j) :
    Nat.card (hexFiberStabilizer i j) = 12 := by
  classical
  have hc : Nat.card (({i,j} : Finset HexIndex)ᶜ : Finset HexIndex) = 4 := by
    rw [Nat.card_eq_fintype_card,Fintype.card_coe,Finset.card_compl]
    simp [HexIndex,hij]
  rw [Nat.card_congr (hexFiberA4Equiv i j).toEquiv]
  exact alternatingGroup.card_of_card_eq_four hc

theorem hexFiberA4Equiv_apply (i j : HexIndex) (g : hexFiberStabilizer i j)
    (x : (({i,j} : Finset HexIndex)ᶜ : Finset HexIndex)) :
    ((hexFiberA4Equiv i j g).val x).val = hexPointKernelCoordinate i g.val x.val := by
  classical
  apply Atlas.Families.Alternating.stabilizerComplementEquiv_apply

end Atlas.Codes
