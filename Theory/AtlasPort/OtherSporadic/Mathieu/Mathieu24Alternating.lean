/-
Copyright (c) 2026 ATLAS contributors. All rights reserved.
Released under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
Authors: Gerald Höhn, ATLAS contributors
-/
module

public import Theory.AtlasPort.OtherSporadic.Mathieu.Mathieu24NotSixTransitive

/-!
# Mathieu24Alternating

Every Golay coordinate automorphism is an even permutation. Explicit generators and
translations prove this for the sextet stabilizer, and its odd index excludes a
nontrivial sign character on the full group.

Source: `Atlas/Mathieu/Mathieu24Alternating.lean`, Gerald Höhn (ATLAS), revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module imports and exposed definitions
so that the original downstream coordinate reductions remain available.
Proof syntax and simplifier arguments are adapted without changing public statements.
-/

@[expose] public section

noncomputable section
namespace Atlas.Codes
open scoped BigOperators

def rowTranslation (t : K) : Equiv.Perm (Fin 4) :=
  (rowLabel.trans (Equiv.addRight t)).trans rowLabel.symm

/-- A translation of the affine plane of order four is an even permutation. -/
theorem rowTranslation_even : ∀ t : K, Equiv.Perm.sign (rowTranslation t) = 1 := by decide

theorem affineTranslation_even (t : HexWord) : Equiv.Perm.sign (affinePermutation t 1) = 1 := by
  have he : affinePermutation t 1 = Equiv.prodCongrRight (fun i => rowTranslation (t i)) := by
    apply Equiv.ext
    intro p
    rfl
  rw [he,Equiv.Perm.sign_prodCongrRight]
  simp [rowTranslation_even]

def sextetSign : SextetStabilizer →* ℤˣ where
  toFun s := Equiv.Perm.sign s.val.val
  map_one' := Equiv.Perm.sign.map_one
  map_mul' x y := Equiv.Perm.sign.map_mul x.val.val y.val.val

/-- Parity checks only for the retained local linear generators. -/
theorem sextetSection_Z_even : sextetSign (sextetSection hexZ) = 1 := by decide

theorem sextetSection_lift_even : ∀ k : Fin 5, sextetSign (sextetSection (hexLift k)) = 1 := by decide

theorem sextetSection_even (g : HexAutomorphisms) : sextetSign (sextetSection g) = 1 := by
  have hg : g ∈ Subgroup.closure hexGeneratingSet := by rw [hexAutomorphisms_generated]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | ⟨k,rfl⟩
    · exact sextetSection_Z_even
    · exact sextetSection_lift_even k
  | one => simp
  | mul x y hx hy ihx ihy => rw [map_mul,map_mul,ihx,ihy,one_mul]
  | inv x hx ih => rw [map_inv,map_inv,ih,inv_one]

theorem sextetTranslation_even (h : Multiplicative hexacode) : sextetSign (sextetTranslation h) = 1 :=
  affineTranslation_even h.toAdd.val

theorem sextetStabilizer_even (s : SextetStabilizer) : Equiv.Perm.sign s.val.val = 1 := by
  obtain ⟨x,rfl⟩ := sextetAffineEquiv.surjective s
  have he : sextetAffineEquiv x = sextetTranslation x.left * sextetSection x.right := by
    have hx : x = SemidirectProduct.inl x.left * SemidirectProduct.inr x.right :=
      SemidirectProduct.mk_eq_inl_mul_inr x.right x.left
    exact (congrArg sextetAffineEquiv hx).trans (map_mul _ _ _)
  change sextetSign (sextetAffineEquiv x) = 1
  rw [he,map_mul,sextetTranslation_even,sextetSection_even,one_mul]

def mathieu24Sign : Mathieu24CodeModel →* ℤˣ := Equiv.Perm.sign.comp Mathieu24CodeModel.subtype

theorem mathieu24_even (g : Mathieu24CodeModel) : Equiv.Perm.sign g.val = 1 := by
  classical
  by_contra hg
  have hm : mathieu24Sign g = -1 := (Int.units_eq_one_or (mathieu24Sign g)).resolve_left hg
  have hs : Function.Surjective mathieu24Sign := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1,map_one _⟩
    · exact ⟨g,hm⟩
  have hle : sextetStabilizer ≤ mathieu24Sign.ker := by
    intro s hs
    exact sextetStabilizer_even ⟨s,hs⟩
  have hi : mathieu24Sign.ker.index = 2 := by
    rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr hs,
      Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup ℤˣ) ≃* ℤˣ).toEquiv]
    rw [Nat.card_eq_fintype_card]
    decide
  have hd := Subgroup.index_dvd_of_le hle
  rw [hi,sextetStabilizer_index] at hd
  norm_num at hd

theorem mathieu24_le_alternating : Mathieu24CodeModel ≤ alternatingGroup Omega := by
  intro g hg
  exact mathieu24_even ⟨g,hg⟩

end Atlas.Codes
