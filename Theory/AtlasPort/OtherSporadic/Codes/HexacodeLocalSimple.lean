/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeKernelTransitivity
public import Theory.AtlasPort.OtherSporadic.Families.Alternating.Stabilizers

/-!
# HexacodeLocalSimple

The local coordinate kernel is identified with the natural alternating group of degree
five, hence is simple. Its transitive action on the fifteen nonzero words gives
irreducibility of the translation module and faithfulness of the affine linear action.

Source: `Atlas/Codes/HexacodeLocalSimple.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open Finset

def hexPointKernelA5Equiv (i : HexIndex) :
    hexPointKernel i ≃* alternatingGroup (({i} : Finset HexIndex)ᶜ : Finset HexIndex) := by
  classical
  have he : MulAction.stabilizer (alternatingGroup HexIndex) i =
      fixingSubgroup (alternatingGroup HexIndex) (({i} : Finset HexIndex) : Set HexIndex) := by
    ext g
    simp [mem_fixingSubgroup_iff,MulAction.mem_stabilizer_iff]
  exact (hexPointKernelAlternatingEquiv i).trans
    ((MulEquiv.subgroupCongr he).trans (Atlas.Families.Alternating.stabilizerComplementEquiv {i}))

theorem hexPointKernel_simple (i : HexIndex) : IsSimpleGroup (hexPointKernel i) := by
  classical
  have : IsSimpleGroup (alternatingGroup (({i} : Finset HexIndex)ᶜ : Finset HexIndex)) :=
    alternatingGroup.isSimpleGroup (by simp [Nat.card_eq_fintype_card,HexIndex])
  exact (hexPointKernelA5Equiv i).isSimpleGroup

theorem hexDoubleZero_nonzero_card (i j : HexIndex) (hij : i ≠ j) :
    Nat.card {u : hexDoubleZero i j // u ≠ 0} = 3 := by
  classical
  let := Fintype.ofFinite (hexDoubleZero i j)
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp only [Fintype.card_unique] at *
  rw [← Nat.card_eq_fintype_card,hexDoubleZero_card i j hij]

theorem hexZeroCoordinate_nonzero_card (i : HexIndex) :
    Nat.card {u : hexZeroCoordinate i // u ≠ 0} = 15 := by
  classical
  let := Fintype.ofFinite (hexZeroCoordinate i)
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype_compl]
  simp only [Fintype.card_unique] at *
  rw [← Nat.card_eq_fintype_card,hexZeroCoordinate_card]


theorem hexZero_invariant_subgroup (i : HexIndex)
    (W : Subgroup (Multiplicative (hexZeroCoordinate i)))
    (stable : ∀ (g : hexPointKernel i) u, u ∈ W → hexZeroAffineAction i g u ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  rcases W.bot_or_exists_ne_one with h | ⟨u,hu,hun⟩
  · exact Or.inl h
  right
  apply top_unique
  intro v _
  by_cases hv : v = 1
  · exact hv ▸ W.one_mem
  obtain ⟨g,hg⟩ := hexPointKernel_nonzero_transitive i u.toAdd v.toAdd hun hv
  have he : hexZeroAffineAction i g u = v := hg
  rw [← he]
  exact stable g u hu

theorem hexZeroAffineAction_injective (i : HexIndex) : Function.Injective (hexZeroAffineAction i) := by
  classical
  have := hexPointKernel_simple i
  rcases (inferInstance : (hexZeroAffineAction i).ker.Normal).eq_bot_or_eq_top with hbot | htop
  · exact (hexZeroAffineAction i).ker_eq_bot_iff.mp hbot
  have he (g : hexPointKernel i) : hexZeroAffineAction i g = 1 := by
    have hg : g ∈ (hexZeroAffineAction i).ker := by rw [htop]; trivial
    exact hg
  have hsub : Subsingleton {u : hexZeroCoordinate i // u ≠ 0} := by
    constructor
    intro u v
    obtain ⟨g,hg⟩ := hexPointKernel_nonzero_transitive i u.val v.val u.prop v.prop
    have hact : hexZeroLinear i g.val u.val = u.val := by
      exact congrArg (fun f : MulAut (Multiplicative (hexZeroCoordinate i)) =>
        (f (Multiplicative.ofAdd u.val)).toAdd) (he g)
    exact Subtype.ext (hact.symm.trans hg)
  let := hsub
  let := Fintype.ofFinite {u : hexZeroCoordinate i // u ≠ 0}
  have hc := Fintype.card_le_of_injective
    (fun _ : {u : hexZeroCoordinate i // u ≠ 0} => (PUnit.unit : PUnit.{1}))
    (fun _ _ _ => Subsingleton.elim _ _)
  have hh : Nat.card {u : hexZeroCoordinate i // u ≠ 0} ≤ 1 := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_punit] using hc
  rw [hexZeroCoordinate_nonzero_card] at hh
  omega

end Atlas.Codes
