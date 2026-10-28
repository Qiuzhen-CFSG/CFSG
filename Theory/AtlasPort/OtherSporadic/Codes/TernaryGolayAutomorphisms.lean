/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Codes/TernaryGolayAutomorphisms.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Codes.TernaryGolayLocalColumns
public import Theory.AtlasPort.OtherSporadic.Codes.TernaryGolaySigned
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.Embedding
public import Mathlib.Data.Fintype.CardEmbedding

/-!
# TernaryGolayAutomorphisms

Pure coordinate automorphisms of the concrete ternary Golay code have order at most 7920.
The proof bounds the stabilizer of three coordinates using admissible column triples.

Source: Gerald Höhn, ATLAS, `Atlas/Codes/TernaryGolayAutomorphisms.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed computational definitions.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Codes

/-- The full pure-coordinate automorphism group of the actual ternary code. -/
def ternaryPureAutomorphism : Subgroup (Equiv.Perm (Fin 12)) where
  carrier := TernaryCoordinatePreserves
  one_mem' := by intro w hw; exact hw
  mul_mem' := by
    intro σ τ hσ hτ w hw
    exact hσ _ (hτ w hw)
  inv_mem' := by
    intro σ hσ w hw
    have hs : TernarySignedPreserves (fun _ => 1) σ.symm :=
      ⟨by intro i; exact one_ne_zero, fun v hv => by
        have he : ternarySignedMap (fun _ => 1) σ.symm v = fun i => v (σ.symm i) := by
          funext i; simp [ternarySignedMap]
        rw [he]; exact hσ v hv⟩
    obtain ⟨v,hv,he⟩ := ternarySignedMap_surjective_code _ _ hs w hw
    have heq : (fun i => w ((σ⁻¹).symm i)) = v := by
      funext i
      have hi := congrFun he (σ i)
      change w (σ i) = v i
      simpa [ternarySignedMap] using hi.symm
    rw [heq]; exact hv

abbrev TernaryPureAutomorphism := ternaryPureAutomorphism

def ternaryThreeTuple : Fin 3 ↪ Fin 12 :=
  ⟨fun i => ⟨i.val,by omega⟩, fun i j h => Fin.ext (congrArg (fun x : Fin 12 => x.val) h)⟩

abbrev ternaryPureThreeStabilizer :=
  MulAction.stabilizer TernaryPureAutomorphism ternaryThreeTuple

theorem ternaryPureThree_fixed (g : ternaryPureThreeStabilizer) :
    TernaryFixFirstThree g.val.val := by
  have h := g.prop
  have hh (i : Fin 3) : g.val.val (ternaryThreeTuple i) = ternaryThreeTuple i :=
    congrArg (fun e : Fin 3 ↪ Fin 12 => e i) h
  exact ⟨hh 0,hh 1,hh 2⟩

theorem ternaryPureThree_order_le : Nat.card ternaryPureThreeStabilizer ≤ 6 := by
  let f : ternaryPureThreeStabilizer → {t : TernaryInformationTriple // TernaryAdmissibleTriple t} :=
    fun g => ⟨ternaryPermutationTriple g.val.val,
      ternaryPermutationTriple_admissible _ (ternaryPureThree_fixed g) g.val.prop⟩
  have hf : Function.Injective f := by
    intro g h he
    apply Subtype.ext
    apply Subtype.ext
    exact ternaryPermutationTriple_injective _ _ (ternaryPureThree_fixed g)
      (ternaryPureThree_fixed h) g.val.prop h.val.prop (congrArg Subtype.val he)
  have hc := Nat.card_le_card_of_injective f hf
  have ht : Nat.card {t : TernaryInformationTriple // TernaryAdmissibleTriple t} = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact ternaryAdmissibleTriple_count
  exact hc.trans_eq ht

theorem ternaryPureAutomorphism_order_le : Nat.card TernaryPureAutomorphism ≤ 7920 := by
  have hi : ternaryPureThreeStabilizer.index ≤ 1320 := by
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
    have h := Nat.card_le_card_of_injective
      (Subtype.val : MulAction.orbit TernaryPureAutomorphism ternaryThreeTuple → (Fin 3 ↪ Fin 12))
      Subtype.val_injective
    have hc : Nat.card (Fin 3 ↪ Fin 12) = 1320 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
      decide
    exact h.trans_eq hc
  have hc := ternaryPureThreeStabilizer.card_mul_index
  have hb := Nat.mul_le_mul ternaryPureThree_order_le hi
  rw [hc] at hb
  exact hb

end Atlas.Codes
