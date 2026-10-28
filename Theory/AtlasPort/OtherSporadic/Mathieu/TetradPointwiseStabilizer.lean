/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.HexacodeZeroCoordinate
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# TetradPointwiseStabilizer

The actual pointwise stabilizer of a tetrad is multiplicatively equivalent to its affine
model of order 960. Fixing every tetrad point forces the translation coordinate to
vanish and the local letter map to be trivial, characterizing the image.

Source: `Atlas/Mathieu/TetradPointwiseStabilizer.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

abbrev TetradPointStabilizer (i : HexIndex) :=
  fixingSubgroup Mathieu24CodeModel (tetrad i : Set Omega)

theorem tetradPointStabilizer_mem (i : HexIndex) (g : Mathieu24CodeModel) :
    g ∈ TetradPointStabilizer i ↔ ∀ k : Fin 4, g.val (i,k) = (i,k) := by
  rw [mem_fixingSubgroup_iff]
  constructor
  · intro hg k; exact hg (i,k) ((mem_tetrad _ _).mpr rfl)
  · intro hg p hp
    have hi := (mem_tetrad p i).mp hp
    obtain ⟨j,k⟩ := p
    dsimp only at hi
    subst j
    exact hg k

theorem tetradPointStabilizer_le_sextet (i : HexIndex) : TetradPointStabilizer i ≤ sextetStabilizer := by
  intro g hg
  apply tetrad_stabilizer_preserves_sextet i g
  change (tetrad i).image g.val = tetrad i
  calc
    _ = (tetrad i).image id := Finset.image_congr (fun p hp => by
      exact hg ⟨p,hp⟩)
    _ = tetrad i := Finset.image_id

theorem sextetAffine_fixes_tetrad (i : HexIndex) (x : SextetAffineGroup) :
    (∀ k : Fin 4, (sextetAffineEquiv x).val.val (i,k) = (i,k)) ↔
      x.right.val.perm i = i ∧ x.left.toAdd.val i = 0 ∧ x.right.val.localMap i = 1 := by
  constructor
  · intro hx
    have hp : x.right.val.perm i = i := congrArg Prod.fst (hx 0)
    have h0 : rowLabel 0 = 0 := rfl
    have ht := congrArg (fun p : Omega => rowLabel p.2) (hx 0)
    rw [sextetAffineEquiv_coordinates,hp] at ht
    simp only [h0,map_zero,zero_add,rowLabel.apply_symm_apply] at ht
    refine ⟨hp,ht,?_⟩
    apply LinearEquiv.ext
    intro u
    obtain ⟨k,rfl⟩ := rowLabel.surjective u
    have hk := congrArg (fun p : Omega => rowLabel p.2) (hx k)
    rw [sextetAffineEquiv_coordinates,hp] at hk
    simpa only [ht,add_zero,rowLabel.apply_symm_apply,LinearEquiv.coe_one,id_eq] using hk
  · rintro ⟨hp,ht,hL⟩ k
    rw [sextetAffineEquiv_coordinates,hp,ht,hL]
    simp

def tetradPointAffineHom (i : HexIndex) : TetradPointAffine i →* TetradPointStabilizer i where
  toFun x := ⟨(sextetAffineEquiv (tetradPointAffineInclusion i x)).val,
    (tetradPointStabilizer_mem i _).mpr ((sextetAffine_fixes_tetrad i _).mpr
      ⟨x.right.val.prop,x.left.toAdd.prop,x.right.prop⟩)⟩
  map_one' := by apply Subtype.ext; exact congrArg Subtype.val (by simp)
  map_mul' x y := by apply Subtype.ext; exact congrArg Subtype.val (by simp)

theorem tetradPointAffineHom_bijective (i : HexIndex) : Function.Bijective (tetradPointAffineHom i) := by
  constructor
  · intro x y he
    have hs : sextetAffineEquiv (tetradPointAffineInclusion i x) =
        sextetAffineEquiv (tetradPointAffineInclusion i y) := Subtype.ext (congrArg (fun z : TetradPointStabilizer i => z.val) he)
    have hh := sextetAffineEquiv.injective hs
    apply SemidirectProduct.ext
    · exact Subtype.ext (congrArg (fun z : SextetAffineGroup => z.left.toAdd) hh)
    · exact Subtype.ext (Subtype.ext (congrArg SemidirectProduct.right hh))
  · intro g
    let s : SextetStabilizer := ⟨g.val,tetradPointStabilizer_le_sextet i g.prop⟩
    obtain ⟨x,hx⟩ := sextetAffineEquiv.surjective s
    have hf : ∀ k, (sextetAffineEquiv x).val.val (i,k) = (i,k) := by
      rw [hx]
      exact (tetradPointStabilizer_mem i g.val).mp g.prop
    obtain ⟨hp,ht,hL⟩ := (sextetAffine_fixes_tetrad i x).mp hf
    let y : TetradPointAffine i := ⟨Multiplicative.ofAdd ⟨x.left.toAdd,ht⟩,⟨⟨x.right,hp⟩,hL⟩⟩
    refine ⟨y,?_⟩
    apply Subtype.ext
    change (sextetAffineEquiv (tetradPointAffineInclusion i y)).val = g.val
    have hy : tetradPointAffineInclusion i y = x := by cases x; rfl
    rw [hy,hx]

/-- The actual pointwise tetrad stabilizer, with the restricted affine multiplication. -/
def tetradPointStabilizerEquiv (i : HexIndex) : TetradPointAffine i ≃* TetradPointStabilizer i :=
  MulEquiv.ofBijective _ (tetradPointAffineHom_bijective i)

theorem tetradPointStabilizer_card (i : HexIndex) : Nat.card (TetradPointStabilizer i) = 960 := by
  rw [← Nat.card_congr (tetradPointStabilizerEquiv i).toEquiv,tetradPointAffine_card]

end Atlas.Codes
