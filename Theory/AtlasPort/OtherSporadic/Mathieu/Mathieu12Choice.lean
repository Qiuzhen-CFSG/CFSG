/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu12Witt

/-!
# Mathieu12Choice

Transporting one dodecad to another conjugates their stabilizer groups and gives an
equivariant bijection of their coordinate sets and hexad blocks. Combining dodecad
transport with interior transitivity transports pointed dodecads.

Source: `Atlas/Mathieu/Mathieu12Choice.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

def mathieu12ChoiceEquiv {D E : Dodecad} {g : Mathieu24CodeModel} (hg : g • D = E) :
    Mathieu12DodecadModel D ≃* Mathieu12DodecadModel E :=
  MulAction.stabilizerEquivStabilizer hg.symm

theorem mathieu12Choice_embedding {D E : Dodecad} {g : Mathieu24CodeModel} (hg : g • D = E)
    (h : Mathieu12DodecadModel D) :
    (mathieu12ChoiceEquiv hg h).val = g*h.val*g⁻¹ := rfl

theorem mathieu12Choice_mem {D E : Dodecad} {g : Mathieu24CodeModel} (hg : g • D = E)
    (x : Omega) : x ∈ D.val ↔ g.val x ∈ E.val := by
  classical
  have he : permuteBlock g.val D.val = E.val := congrArg Subtype.val hg
  rw [← he]
  constructor
  · intro hx; exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  · intro hx
    obtain ⟨y,hy,hyx⟩ := Finset.mem_image.mp hx
    exact g.val.injective hyx ▸ hy

def mathieu12ChoicePoints {D E : Dodecad} {g : Mathieu24CodeModel} (hg : g • D = E) :
    Mathieu12Points D ≃ Mathieu12Points E :=
  g.val.subtypeEquiv (mathieu12Choice_mem hg)

theorem mathieu12ChoicePoints_coordinate {D E : Dodecad} {g : Mathieu24CodeModel} (hg : g • D = E)
    (x : Mathieu12Points D) : (mathieu12ChoicePoints hg x).val = g.val x.val := rfl

theorem mathieu12Choice_equivariant {D E : Dodecad} {g : Mathieu24CodeModel} (hg : g • D = E)
    (h : Mathieu12DodecadModel D) (x : Mathieu12Points D) :
    mathieu12ChoicePoints hg (h • x) = mathieu12ChoiceEquiv hg h • mathieu12ChoicePoints hg x := by
  apply Subtype.ext
  change g.val (h.val.val x.val) = (mathieu12ChoiceEquiv hg h).val.val (g.val x.val)
  rw [mathieu12Choice_embedding]
  change g.val (h.val.val x.val) = g.val (h.val.val (g.val⁻¹ (g.val x.val)))
  rw [Equiv.Perm.inv_def,Equiv.symm_apply_apply]

theorem dodecad_point_flags_transitive (D E : Dodecad) (a : Mathieu12Points D) (b : Mathieu12Points E) :
    ∃ g : Mathieu24CodeModel, g • D = E ∧ g.val a.val = b.val := by
  obtain ⟨g,hg⟩ := dodecad_transitive_explicit D E
  have hg' : g • D = E := Subtype.ext hg
  have := mathieu12_four_transitive E
  have : MulAction.IsMultiplyPretransitive (Mathieu12DodecadModel E) (Mathieu12Points E) 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 4)
      (by rw [mathieu12_degree]; decide)
  have : MulAction.IsPretransitive (Mathieu12DodecadModel E) (Mathieu12Points E) :=
    MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨h,hh⟩ := MulAction.exists_smul_eq (Mathieu12DodecadModel E) (mathieu12ChoicePoints hg' a) b
  refine ⟨h.val*g,?_,?_⟩
  · rw [mul_smul,hg']
    exact h.prop
  · exact congrArg Subtype.val hh

theorem dodecad_through_coordinate (a : Omega) : ∃ D : Dodecad, a ∈ D.val := by
  have hd : Nonempty Dodecad := (Nat.card_pos_iff.mp (show 0 < Nat.card Dodecad by
    rw [dodecad_type_card]; decide)).1
  let D := Classical.choice hd
  have hx : Nonempty (Mathieu12Points D) := (Nat.card_pos_iff.mp
    (show 0 < Nat.card (Mathieu12Points D) by rw [mathieu12_degree]; decide)).1
  let x := Classical.choice hx
  have := mathieu24_four_transitive
  have : MulAction.IsMultiplyPretransitive Mathieu24CodeModel Omega 2 :=
    MulAction.isMultiplyPretransitive_of_le (by decide : 2 ≤ 4) (by norm_num [Omega,HexIndex])
  have : MulAction.IsPretransitive Mathieu24CodeModel Omega := MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Mathieu24CodeModel x.val a
  exact ⟨g • D,Finset.mem_image.mpr ⟨x.val,x.prop,hg⟩⟩

theorem mathieu12Choice_trace {D E : Dodecad} {g : Mathieu24CodeModel} (hg : g • D = E)
    (O : Finset Omega) :
    (mathieu12OctadTrace D O).map (mathieu12ChoicePoints hg).toEmbedding =
      mathieu12OctadTrace E (permuteBlock g.val O) := by
  classical
  ext x
  simp only [Finset.mem_map,mathieu12OctadTrace,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact Finset.mem_image.mpr ⟨y.val,hy,rfl⟩
  · intro hx
    obtain ⟨y,hy,he⟩ := Finset.mem_image.mp hx
    let z := (mathieu12ChoicePoints hg).symm x
    have hp : g.val z.val = x.val :=
      congrArg Subtype.val ((mathieu12ChoicePoints hg).apply_symm_apply x)
    have hz : z.val = y := g.val.injective (hp.trans he.symm)
    exact ⟨z,hz.symm ▸ hy,(mathieu12ChoicePoints hg).apply_symm_apply x⟩

theorem mathieu12Choice_blocks {D E : Dodecad} {g : Mathieu24CodeModel} (hg : g • D = E)
    (B : Finset (Mathieu12Points D)) (hB : B ∈ mathieu12Blocks D) :
    B.map (mathieu12ChoicePoints hg).toEmbedding ∈ mathieu12Blocks E := by
  obtain ⟨O,hO,hc,rfl⟩ := (mathieu12Blocks_mem D B).mp hB
  refine (mathieu12Blocks_mem E _).mpr ⟨permuteBlock g.val O,
    codePreserving_octad_forward _ g.prop _ hO,?_,(mathieu12Choice_trace hg O).symm⟩
  rw [← mathieu12OctadTrace_card,← mathieu12Choice_trace hg,Finset.card_map,
    mathieu12OctadTrace_card,hc]

end Atlas.Codes
