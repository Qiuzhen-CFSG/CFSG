module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne.FiniteConditions

/-!
# Checking generator images in the J₁ matrix model

A literal vector trajectory certifies that a matrix power is not the identity.
For a surviving row, an actual model word with matrix image `C` suffices once
`C * A = X * C` and `C * B = B * C` have been checked. These intertwining
identities imply both required conjugation statements, using faithfulness.

This is the finite calculation used for GLS3, Table 5.3f. Matrix conventions
and the ATLAS source are those of `Theory.SpecificGroups.Janko1.Model.Basic`.
-/

namespace Janko1.OuterCertificate.GeneratorImages
open OrderCertificate Matrix
set_option maxRecDepth 10000

private theorem pow_mulVec_chain {n : ℕ} (M : Mat) (v : Fin (n+1) → Fin 7 → ZMod 11)
    (hs : ∀ k : Fin n, M *ᵥ v k.castSucc = v k.succ) :
    M ^ n *ᵥ v 0 = v (Fin.last n) := by
  have step (k : ℕ) (hk : k ≤ n) : M ^ k *ᵥ v 0 = v ⟨k, by omega⟩ := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← mulVec_mulVec, ih (by omega)]
      exact hs ⟨k, by omega⟩
  exact step n le_rfl

/-- A moved vector certifies failure of the proposed power relation. -/
public theorem pow_ne_one_of_chain {n : ℕ} (M : Mat) (v : Fin (n+1) → Fin 7 → ZMod 11)
    (hs : ∀ k : Fin n, M *ᵥ v k.castSucc = v k.succ)
    (hn : v (Fin.last n) ≠ v 0) : M ^ n ≠ 1 := by
  intro h
  apply hn
  have hv := pow_mulVec_chain M v hs
  simpa only [h, one_mulVec] using hv.symm

/-- Intertwining identities for the image of an actual word give its conjugation action. -/
public theorem conjugates_of_intertwining (g : Model) (C X : Mat)
    (hg : matrixValue g = C) (ha : C * matrixA = X * C)
    (hb : C * matrixB = matrixB * C) :
    matrixValue (g * a * g⁻¹) = X ∧ g * b * g⁻¹ = b := by
  constructor
  · calc
      matrixValue (g * a * g⁻¹) =
          (C * matrixA) * matrixValue g⁻¹ := by
            rw [map_mul, map_mul, hg, show matrixValue a = matrixA from rfl]
      _ = (X * C) * matrixValue g⁻¹ := by rw [ha]
      _ = X * matrixValue (g * g⁻¹) := by rw [map_mul, hg, mul_assoc]
      _ = X := by rw [mul_inv_cancel, map_one, mul_one]
  · have h : g * b = b * g := by
      apply matrixValue_injective
      simpa only [map_mul, hg, show matrixValue b = matrixB from rfl] using hb
    rw [h, mul_inv_cancel_right]

/-- The generator-image conclusion for one literal row, with exactly the two relators. -/
@[expose] public def RowRigid (i : Fin 1463) : Prop :=
  (orbitMatrix i * matrixB) ^ 7 = 1 →
  (orbitMatrix i * matrixB * orbitMatrix i * matrixB ^ 2) ^ 19 = 1 →
  ∃ g : Model, matrixValue (g * a * g⁻¹) = orbitMatrix i ∧ g * b * g⁻¹ = b

end Janko1.OuterCertificate.GeneratorImages
