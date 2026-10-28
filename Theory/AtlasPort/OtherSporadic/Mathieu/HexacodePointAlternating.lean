/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.HexacodePointKernel

/-!
# HexacodePointAlternating

The local hexacode kernel is multiplicatively equivalent, through its coordinate action,
to the point stabilizer in the alternating group of degree six. Injectivity and matching
orders prove surjectivity and give transitivity on the other coordinates.

Source: `Atlas/Mathieu/HexacodePointAlternating.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

/-- Even coordinate permutations fixing i: the natural A5 on the other five coordinates. -/
abbrev HexEvenPoint (i : HexIndex) := MulAction.stabilizer (alternatingGroup HexIndex) i

theorem hex_even_coordinate_transitive (i j : HexIndex) :
    ∃ g : alternatingGroup HexIndex, g • i = j := by
  classical
  by_cases hij : i = j
  · exact ⟨1,by simpa using hij⟩
  have hp : ∀ i j : HexIndex, ∃ k, k ≠ i ∧ k ≠ j := by decide
  obtain ⟨k,hki,hkj⟩ := hp i j
  let σ := Equiv.swap i j * Equiv.swap j k
  have hs : Equiv.Perm.sign σ = 1 := by
    rw [map_mul,Equiv.Perm.sign_swap hij,Equiv.Perm.sign_swap (Ne.symm hkj)]
    norm_num
  refine ⟨⟨σ,hs⟩,?_⟩
  change Equiv.swap i j (Equiv.swap j k i) = j
  rw [Equiv.swap_apply_of_ne_of_ne hij (Ne.symm hki),Equiv.swap_apply_left]

def hexEvenPointOrbitEquiv (i : HexIndex) :
    MulAction.orbit (alternatingGroup HexIndex) i ≃ HexIndex :=
  Equiv.ofBijective Subtype.val ⟨Subtype.val_injective,by
    intro j
    exact ⟨⟨j,MulAction.mem_orbit_iff.mpr (hex_even_coordinate_transitive i j)⟩,rfl⟩⟩

theorem hexEvenPoint_card (i : HexIndex) : Nat.card (HexEvenPoint i) = 60 := by
  have he := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (alternatingGroup HexIndex) i)
  rw [Nat.card_prod,Nat.card_congr (hexEvenPointOrbitEquiv i),
    nat_card_alternatingGroup] at he
  have hc : Nat.card HexIndex = 6 := by simp [HexIndex]
  rw [hc] at he
  change 6 * Nat.card (HexEvenPoint i) = 360 at he
  omega

def hexPointKernelAlternating (i : HexIndex) : hexPointKernel i →* HexEvenPoint i where
  toFun g := ⟨⟨hexPointKernelCoordinate i g,by
    change Equiv.Perm.sign (hexCoordinateHom g.val.val) = 1
    rw [← hexSign_coordinate,hexPointKernel_even]⟩,g.val.prop⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact map_one _
  map_mul' g h := by apply Subtype.ext; apply Subtype.ext; exact map_mul _ _ _

theorem hexPointKernelAlternating_bijective (i : HexIndex) :
    Function.Bijective (hexPointKernelAlternating i) := by
  classical
  let := Fintype.ofFinite (hexPointKernel i)
  let := Fintype.ofFinite (HexEvenPoint i)
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro g h he
    apply hexPointKernelCoordinate_injective i
    exact congrArg (fun x : HexEvenPoint i => x.val.val) he
  · rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card,
      hexPointKernel_card,hexEvenPoint_card]

/-- The actual local kernel is identified, through its coordinate action, with the natural A5. -/
def hexPointKernelAlternatingEquiv (i : HexIndex) : hexPointKernel i ≃* HexEvenPoint i :=
  MulEquiv.ofBijective _ (hexPointKernelAlternating_bijective i)

theorem hexPointKernel_coordinate_image (i : HexIndex) (σ : Equiv.Perm HexIndex)
    (hi : σ i = i) (hs : Equiv.Perm.sign σ = 1) :
    ∃ g : hexPointKernel i, hexPointKernelCoordinate i g = σ := by
  obtain ⟨g,hg⟩ := (hexPointKernelAlternating_bijective i).2 ⟨⟨σ,hs⟩,hi⟩
  exact ⟨g,congrArg (fun x : HexEvenPoint i => x.val.val) hg⟩

theorem hexPointKernel_transitive_complement (i j k : HexIndex) (hji : j ≠ i) (hki : k ≠ i) :
    ∃ g : hexPointKernel i, hexPointKernelCoordinate i g j = k := by
  classical
  by_cases hjk : j = k
  · exact ⟨1,by simpa using hjk⟩
  have hp : ∀ i j k : HexIndex, ∃ l, l ≠ i ∧ l ≠ j ∧ l ≠ k := by decide
  obtain ⟨l,hli,hlj,hlk⟩ := hp i j k
  let σ := Equiv.swap j k * Equiv.swap k l
  have hs : Equiv.Perm.sign σ = 1 := by
    rw [map_mul,Equiv.Perm.sign_swap hjk,Equiv.Perm.sign_swap (Ne.symm hlk)]
    norm_num
  have hi : σ i = i := by
    change Equiv.swap j k (Equiv.swap k l i) = i
    rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hki) (Ne.symm hli),
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hji) (Ne.symm hki)]
  obtain ⟨g,hg⟩ := hexPointKernel_coordinate_image i σ hi hs
  refine ⟨g,?_⟩
  rw [hg]
  change Equiv.swap j k (Equiv.swap k l j) = k
  rw [Equiv.swap_apply_of_ne_of_ne hjk (Ne.symm hlj),Equiv.swap_apply_left]

end Atlas.Codes
