/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu21PointStabilizer
public import Theory.AtlasPort.OtherSporadic.Mathieu.TetradEightObstruction
public import Theory.AtlasPort.OtherSporadic.GroupTheory.OrderedFixingConjugacy

/-!
# Mathieu21LocalStabilizer

A point stabilizer in the degree-twenty-one action is multiplicatively equivalent to a
tetrad pointwise stabilizer. Flattening the nested stabilizers gives a four-coordinate
fixing subgroup, which coordinate transitivity conjugates to the standard tetrad.

Source: `Atlas/Mathieu/Mathieu21LocalStabilizer.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

def mathieu21FourEmbedding (a : Omega) (b : Mathieu23Points a) (c : Mathieu22Points a b)
    (d : Mathieu21Points a b c) : Fin 4 ↪ Omega where
  toFun := ![a,b.val,c.val.val,d.val.val.val]
  inj' := by
    have hba : b.val ≠ a := b.prop
    have hca : c.val.val ≠ a := c.val.prop
    have hcb : c.val.val ≠ b.val := fun h => c.prop (Subtype.ext h)
    have hda : d.val.val.val ≠ a := d.val.val.prop
    have hdb : d.val.val.val ≠ b.val := fun h => d.val.prop (Subtype.ext h)
    have hdc : d.val.val.val ≠ c.val.val := fun h => d.prop (Subtype.ext (Subtype.ext h))
    intro i j h
    fin_cases i <;> fin_cases j <;> dsimp at h <;> first
      | rfl
      | exact False.elim (hba h)
      | exact False.elim (hba h.symm)
      | exact False.elim (hca h)
      | exact False.elim (hca h.symm)
      | exact False.elim (hcb h)
      | exact False.elim (hcb h.symm)
      | exact False.elim (hda h)
      | exact False.elim (hda h.symm)
      | exact False.elim (hdb h)
      | exact False.elim (hdb h.symm)
      | exact False.elim (hdc h)
      | exact False.elim (hdc h.symm)

def mathieu21FourFixingHom (a : Omega) (b : Mathieu23Points a) (c : Mathieu22Points a b)
    (d : Mathieu21Points a b c) : MulAction.stabilizer (Mathieu21PointModel a b c) d →*
      fixingSubgroup Mathieu24CodeModel (Set.range (mathieu21FourEmbedding a b c d)) where
  toFun t := ⟨mathieu21_embedding a b c t.val,by
    intro x
    obtain ⟨k,hk⟩ := x.prop
    rw [← hk]
    fin_cases k
    · exact t.val.val.val.prop
    · exact congrArg Subtype.val t.val.val.prop
    · exact congrArg (fun x : Mathieu22Points a b => x.val.val) t.val.prop
    · exact congrArg (fun x : Mathieu21Points a b c => x.val.val.val) t.prop⟩
  map_one' := by apply Subtype.ext; exact map_one (mathieu21_embedding a b c)
  map_mul' s t := by apply Subtype.ext; exact map_mul (mathieu21_embedding a b c) s.val t.val

theorem mathieu21FourFixingHom_bijective (a : Omega) (b : Mathieu23Points a)
    (c : Mathieu22Points a b) (d : Mathieu21Points a b c) :
    Function.Bijective (mathieu21FourFixingHom a b c d) := by
  constructor
  · intro s t h
    apply Subtype.ext
    exact mathieu21_embedding_injective a b c (congrArg
      (fun x : fixingSubgroup Mathieu24CodeModel
        (Set.range (mathieu21FourEmbedding a b c d)) => x.val) h)
  · intro g
    have hf (k : Fin 4) : g.val • mathieu21FourEmbedding a b c d k =
        mathieu21FourEmbedding a b c d k := g.prop ⟨_,⟨k,rfl⟩⟩
    have ha : g.val • a = a := hf 0
    let g23 : Mathieu23PointModel a := ⟨g.val,ha⟩
    have hb : g23 • b = b := Subtype.ext (hf 1)
    let g22 : Mathieu22PointModel a b := ⟨g23,hb⟩
    have hc : g22 • c = c := Subtype.ext (Subtype.ext (hf 2))
    let g21 : Mathieu21PointModel a b c := ⟨g22,hc⟩
    have hd : g21 • d = d := Subtype.ext (Subtype.ext (Subtype.ext (hf 3)))
    exact ⟨⟨g21,hd⟩,Subtype.ext rfl⟩

def mathieu21LocalEquiv (a : Omega) (b : Mathieu23Points a) (c : Mathieu22Points a b)
    (d : Mathieu21Points a b c) (i : HexIndex) :
    MulAction.stabilizer (Mathieu21PointModel a b c) d ≃* TetradPointStabilizer i := by
  let e := mathieu21FourEmbedding a b c d
  let g := Classical.choose (orderedFour_to_tetrad e i)
  have hg := Classical.choose_spec (orderedFour_to_tetrad e i)
  have hs : fixingSubgroup Mathieu24CodeModel (Set.range (tetradEmbedding i)) =
      TetradPointStabilizer i := by
    congr 1
    ext x
    simp [tetrad]
  exact (MulEquiv.ofBijective (mathieu21FourFixingHom a b c d)
    (mathieu21FourFixingHom_bijective a b c d)).trans
      ((Atlas.GroupTheory.orderedFixingConjugacy e (tetradEmbedding i) g hg).trans
        (MulEquiv.subgroupCongr hs))

end Atlas.Codes
