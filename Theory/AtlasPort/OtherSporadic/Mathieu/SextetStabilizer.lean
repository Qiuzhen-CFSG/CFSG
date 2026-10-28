/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.AffineCodeCriterion
public import Theory.AtlasPort.OtherSporadic.Mathieu.PartitionAffineNormalForm

/-!
# SextetStabilizer

The actual distinguished-sextet stabilizer is multiplicatively equivalent to the affine
semidirect product of the hexacode and its monomial automorphisms. The partition normal
form and code-preservation criterion prove bijectivity, yielding order 138240.

Source: `Atlas/Mathieu/SextetStabilizer.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

/-- The actual setwise stabilizer in the existing full Golay code group. -/
def sextetStabilizer : Subgroup Mathieu24CodeModel :=
  MulAction.stabilizer Mathieu24CodeModel distinguishedUnorderedSextet

abbrev SextetStabilizer := sextetStabilizer

theorem sextetStabilizer_mem_iff (g : Mathieu24CodeModel) : g ∈ sextetStabilizer ↔
    PreservesTetradPartition g.val := by
  constructor
  · intro h; exact congrArg Subtype.val h
  · intro h; exact Subtype.ext h

def hexAffineAction : HexAutomorphisms →* MulAut (Multiplicative hexacode) where
  toFun g := (hexAction g).toAddEquiv.toMultiplicative
  map_one' := by apply MulEquiv.ext; intro w; rfl
  map_mul' _ _ := by apply MulEquiv.ext; intro w; rfl

abbrev SextetAffineGroup := Multiplicative hexacode ⋊[hexAffineAction] HexAutomorphisms

def sextetAffineHom : SextetAffineGroup →* SextetStabilizer where
  toFun x :=
    ⟨⟨affinePermutation x.left.toAdd.val x.right.val,
      affine_preserves_code _ _ x.left.toAdd.prop x.right.prop⟩,
      (sextetStabilizer_mem_iff _).mpr (affinePermutation_preserves_parts _ _)⟩
  map_one' := by apply Subtype.ext; apply Subtype.ext; exact affinePermutation_zero_one
  map_mul' x y := by
    apply Subtype.ext; apply Subtype.ext
    exact (affinePermutation_mul x.left.toAdd.val y.left.toAdd.val x.right.val y.right.val).symm

theorem sextetAffineHom_bijective : Function.Bijective sextetAffineHom := by
  constructor
  · intro x y h
    have he := congrArg (fun s : SextetStabilizer => s.val.val) h
    have hh := @affinePermutation_injective (x.left.toAdd.val,x.right.val)
      (y.left.toAdd.val,y.right.val) he
    exact SemidirectProduct.ext (Subtype.ext (Prod.mk.inj hh).1) (Subtype.ext (Prod.mk.inj hh).2)
  · intro s
    have hp := (sextetStabilizer_mem_iff s.val).mp s.prop
    let t := partitionTranslation s.val.val hp
    let g := partitionMonomial s.val.val hp
    have hr : affinePermutation t g = s.val.val := partition_affine_reconstruction _ hp
    have hc : CodePreserving (affinePermutation t g) := hr.symm ▸ s.val.prop
    obtain ⟨ht,hg⟩ := (affine_code_preservation_iff t g).mp hc
    refine ⟨⟨Multiplicative.ofAdd ⟨t,ht⟩,⟨g,hg⟩⟩,?_⟩
    apply Subtype.ext; apply Subtype.ext
    exact hr

noncomputable def sextetAffineEquiv : SextetAffineGroup ≃* SextetStabilizer :=
  MulEquiv.ofBijective sextetAffineHom sextetAffineHom_bijective

theorem sextetAffineEquiv_coordinates (x : SextetAffineGroup) (i : HexIndex) (k : Fin 4) :
    (sextetAffineEquiv x).val.val (i,k) =
      (x.right.val.perm i,rowLabel.symm
        (x.right.val.localMap (x.right.val.perm i) (rowLabel k) + x.left.toAdd.val (x.right.val.perm i))) := rfl

theorem sextetAffineEquiv_inverse_parameters (s : SextetStabilizer) :
    ((sextetAffineEquiv.symm s).left.toAdd.val,(sextetAffineEquiv.symm s).right.val) =
      (partitionTranslation s.val.val ((sextetStabilizer_mem_iff s.val).mp s.prop),
        partitionMonomial s.val.val ((sextetStabilizer_mem_iff s.val).mp s.prop)) := by
  apply affinePermutation_injective
  have h := congrArg (fun s : SextetStabilizer => s.val.val) (sextetAffineEquiv.apply_symm_apply s)
  exact h.trans (partition_affine_reconstruction _ _).symm

theorem sextetStabilizer_card : Nat.card SextetStabilizer = 138240 := by
  rw [Nat.card_congr sextetAffineEquiv.symm.toEquiv,SemidirectProduct.card,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative hexacode ≃ hexacode),
    hexacode_card,hexAutomorphisms_card]

end Atlas.Codes
