/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.DodecadAction

/-!
# DodecadComplement

Adding the all-ones word complements dodecad supports. This gives a fixed-point-free
involution on dodecads commuting with coordinate automorphisms, so complementary
dodecads have the same setwise stabilizer.

Source: `Atlas/Mathieu/DodecadComplement.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes

theorem support_add_allOnes (w : BinaryWord) : support (w + allOnes) = (support w)ᶜ := by
  classical
  ext x
  simp only [support,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_compl,Pi.add_apply]
  change w x + 1 ≠ 0 ↔ ¬ w x ≠ 0
  have hb : ∀ b : Bit, b + 1 ≠ 0 ↔ ¬ b ≠ 0 := by decide
  exact hb _

theorem dodecad_complement (D : Finset Omega) (hD : D ∈ dodecads) : Dᶜ ∈ dodecads := by
  obtain ⟨w,hw,hs⟩ := (dodecads_mem D).mp hD
  have hc := complement_weight w.val
  rw [hw] at hc
  exact (dodecads_mem _).mpr ⟨⟨w.val+allOnes,golay.add_mem w.prop (C0_le_golay allOnes_mem_C0)⟩,
    by change hammingNorm (w.val+allOnes) = 12; omega,
    (support_add_allOnes w.val).trans (congrArg (fun D : Finset Omega => Dᶜ) hs)⟩

def dodecadComplement : Equiv.Perm Dodecad where
  toFun D := ⟨D.valᶜ,dodecad_complement D.val D.prop⟩
  invFun D := ⟨D.valᶜ,dodecad_complement D.val D.prop⟩
  left_inv D := Subtype.ext (compl_compl D.val)
  right_inv D := Subtype.ext (compl_compl D.val)

theorem dodecadComplement_ne (D : Dodecad) : dodecadComplement D ≠ D := by
  intro he
  have hs := congrArg Subtype.val he
  change D.valᶜ = D.val at hs
  have h := congrArg (fun S : Finset Omega => ((0,0),0) ∈ S) hs
  simp only [Finset.mem_compl] at h
  by_cases hm : ((0,0),0) ∈ D.val <;> simp_all

theorem permuteBlock_complement (σ : Equiv.Perm Omega) (D : Finset Omega) :
    permuteBlock σ Dᶜ = (permuteBlock σ D)ᶜ := by
  classical
  ext x
  have hm (D : Finset Omega) : x ∈ permuteBlock σ D ↔ σ.symm x ∈ D := by
    constructor
    · rintro hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      simpa using hy
    · intro hx
      exact Finset.mem_image.mpr ⟨σ.symm x,hx,σ.apply_symm_apply x⟩
  simp only [hm,Finset.mem_compl]

theorem dodecadComplement_equivariant (g : Mathieu24CodeModel) (D : Dodecad) :
    g • dodecadComplement D = dodecadComplement (g • D) :=
  Subtype.ext (permuteBlock_complement g.val D.val)

theorem mathieu12_complement_stabilizer (D : Dodecad) :
    Mathieu12DodecadModel (dodecadComplement D) = Mathieu12DodecadModel D := by
  ext g
  change (g • dodecadComplement D = dodecadComplement D) ↔ (g • D = D)
  rw [dodecadComplement_equivariant]
  exact dodecadComplement.injective.eq_iff

end Atlas.Codes
