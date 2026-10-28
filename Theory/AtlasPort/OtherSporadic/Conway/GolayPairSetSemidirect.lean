/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/GolayPairSetSemidirect.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.OrthogonalLineLocalOrder
public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu22PairStabilizer

/-!
The monomial action preserving a marked coordinate pair as a set.
The shortened sign kernel and actual pair stabilizer form the required semidirect product.

Source: Gerald Höhn, `Atlas/Conway/GolayPairSetSemidirect.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

abbrev GolayPairSetKernel (a : Omega) (b : Mathieu23Points a) :=
  (golayTwoCoordinateProjection a b.val).ker

theorem pairSet_fixes_or_swaps (a : Omega) (b : Mathieu23Points a) (g : Mathieu22PairModel a b) :
    (g.val.val a = a ∧ g.val.val b.val = b.val) ∨
    (g.val.val a = b.val ∧ g.val.val b.val = a) :=
  (Atlas.GroupTheory.pairStabilizer_mem a b.val (Ne.symm b.prop) g.val).mp g.prop

def golayPairSetKernelMap (a : Omega) (b : Mathieu23Points a) (g : Mathieu22PairModel a b) :
    GolayPairSetKernel a b →ₗ[Bit] GolayPairSetKernel a b where
  toFun c := ⟨golayPermutationEquiv g.val c.val,by
    have h0 := congrArg Prod.fst c.prop
    have h1 := congrArg Prod.snd c.prop
    change c.val.val a = 0 at h0
    change c.val.val b.val = 0 at h1
    change (c.val.val (g.val.val.symm a),c.val.val (g.val.val.symm b.val)) = (0,0)
    have hp := pairSet_fixes_or_swaps a b g⁻¹
    change (g.val.val.symm a = a ∧ g.val.val.symm b.val = b.val) ∨
      (g.val.val.symm a = b.val ∧ g.val.val.symm b.val = a) at hp
    rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [ha,hb]; exact Prod.ext h0 h1
    · rw [ha,hb]; exact Prod.ext h1 h0⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def golayPairSetKernelEquiv (a : Omega) (b : Mathieu23Points a) (g : Mathieu22PairModel a b) :
    GolayPairSetKernel a b ≃ₗ[Bit] GolayPairSetKernel a b where
  toLinearMap := golayPairSetKernelMap a b g
  invFun := golayPairSetKernelMap a b g⁻¹
  left_inv c := by
    apply Subtype.ext; apply Subtype.ext; funext i
    change c.val.val (g.val.val.symm (g.val.val i)) = c.val.val i
    rw [Equiv.symm_apply_apply]
  right_inv c := by
    apply Subtype.ext; apply Subtype.ext; funext i
    change c.val.val (g.val.val (g.val.val.symm i)) = c.val.val i
    rw [Equiv.apply_symm_apply]

def golayPairSetKernelAction (a : Omega) (b : Mathieu23Points a) :
    Mathieu22PairModel a b →* MulAut (Multiplicative (GolayPairSetKernel a b)) where
  toFun g := (golayPairSetKernelEquiv a b g).toAddEquiv.toMultiplicative
  map_one' := by apply MulEquiv.ext; intro c; rfl
  map_mul' g h := by apply MulEquiv.ext; intro c; rfl

abbrev GolayPairSetMonomialGroup (a : Omega) (b : Mathieu23Points a) :=
  Multiplicative (GolayPairSetKernel a b) ⋊[golayPairSetKernelAction a b] Mathieu22PairModel a b

def pairSetMonomialInclusion (a : Omega) (b : Mathieu23Points a) :
    GolayPairSetMonomialGroup a b →* GolayMonomialGroup :=
  SemidirectProduct.map (GolayPairSetKernel a b).subtype.toAddMonoidHom.toMultiplicative
    (Mathieu22PairModel a b).subtype (by intro g; rfl)

theorem pairSetMonomialInclusion_injective (a : Omega) (b : Mathieu23Points a) :
    Function.Injective (pairSetMonomialInclusion a b) := by
  intro x y he
  apply SemidirectProduct.ext
  · exact Subtype.ext (congrArg SemidirectProduct.left he)
  · exact Subtype.ext (congrArg SemidirectProduct.right he)

theorem golayPairSetMonomialGroup_order (a : Omega) (b : Mathieu23Points a) :
    Nat.card (GolayPairSetMonomialGroup a b) = 908328960 := by
  rw [SemidirectProduct.card,mathieu22Pair_order,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (GolayPairSetKernel a b) ≃ GolayPairSetKernel a b),
    golay_two_coordinate_kernel_card a b.val (Ne.symm b.prop)]

def pairSetToMonomialFixer (a : Omega) (b : Mathieu23Points a) :
    GolayPairSetMonomialGroup a b →* leechVectorStabilizer monomialSubgroup (minimumPairPlus a b.val) where
  toFun m := ⟨⟨monomialEmbedding (pairSetMonomialInclusion a b m),⟨_,rfl⟩⟩,by
    apply monomial_fixes_pair_plus _ a b.val (Ne.symm b.prop)
    · exact pairSet_fixes_or_swaps a b m.right
    · exact congrArg Prod.fst m.left.toAdd.prop
    · exact congrArg Prod.snd m.left.toAdd.prop⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext
    exact (monomialEmbedding.comp (pairSetMonomialInclusion a b)).map_one
  map_mul' g h := by
    apply Subtype.ext; apply Subtype.ext
    exact (monomialEmbedding.comp (pairSetMonomialInclusion a b)).map_mul g h

def pairSetToLineStabilizer (a : Omega) (b : Mathieu23Points a) :
    GolayPairSetMonomialGroup a b →* orthogonalLineStabilizer a b.val :=
  (orthogonalLineMonomialEquiv a b.val (Ne.symm b.prop)).symm.toMonoidHom.comp
    (pairSetToMonomialFixer a b)

theorem pairSetToLineStabilizer_injective (a : Omega) (b : Mathieu23Points a) :
    Function.Injective (pairSetToLineStabilizer a b) := by
  intro x y h
  apply pairSetMonomialInclusion_injective a b
  apply monomialEmbedding_injective
  exact congrArg (fun z : orthogonalLineStabilizer a b.val => z.val.val) h

def fullOrthogonalLineSemidirectEquiv (a : Omega) (b : Mathieu23Points a) :
    GolayPairSetMonomialGroup a b ≃* orthogonalLineStabilizer a b.val :=
  MulEquiv.ofBijective (pairSetToLineStabilizer a b)
    ((pairSetToLineStabilizer_injective a b).bijective_of_nat_card_le (by
      rw [golayPairSetMonomialGroup_order,orthogonalLineStabilizer_order a b.val (Ne.symm b.prop)]))

end Atlas.Conway
