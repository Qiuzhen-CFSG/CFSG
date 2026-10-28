module
public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.ExtraExtensions.Cohomology.Coordinates

/-!
# From binary row certificates to changes of section

Evaluate the cochain matrix on a factor set and multiply by its coboundary.
The resulting factor set has exactly the coordinates of the checked defect
matrix. Triangular elimination reduces its vanishing to the free coordinates.
A zero residual yields the explicit cochain in `FactorSet.Cohomologous`.

This is the mathematical bridge used by the finite cohomology calculations
for Huppert--Blackburn III, XII.1.18(b), p.314.
-/

@[expose] public section
namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions.Cohomology
open LocalModelDichotomy
-- Keep the 2304-term evaluation sum behind its proved linearity interface.
attribute [local irreducible] ev
variable {α : SymmetricFour →* MulAut BinaryFour}

def correctingCochain (b : Fin 24 → Fin 4 → ℕ) (c : FactorSet α)
    (s : SymmetricFour) : BinaryFour :=
  Multiplicative.ofAdd (fun i => ev (coordinates c) (b (index s) i))

lemma correctingCochain_one (b : Fin 24 → Fin 4 → ℕ) (hb : ∀ i, b 0 i = 0)
    (c : FactorSet α) : correctingCochain b c 1 = 1 := by
  unfold correctingCochain
  simp only [index_one, hb, ev_zero]
  rfl

def residual (b : Fin 24 → Fin 4 → ℕ) (hb : ∀ i, b 0 i = 0)
    (c : FactorSet α) : FactorSet α :=
  times c (cob (correctingCochain b c) (correctingCochain_one b hb c))

lemma coordinates_residual (cols : SymmetricFour → Fin 4 → Fin 16)
    (ha : ∀ s v, α s v = matrixActionFun cols s v)
    (b : Fin 24 → Fin 4 → ℕ) (hb : ∀ i, b 0 i = 0)
    (c : FactorSet α) (p : Fin 2304) :
    coordinates (residual b hb c) p = ev (coordinates c) (defectMask cols b p) := by
  simp only [defectMask, ev_xor, ev_variable, ev_actMask]
  unfold coordinates residual times cob
  simp only [binary_inv, toAdd_mul, Pi.add_apply, correctingCochain,
    ← element_product, index_element, ha, add_assoc]
  simp only [toAdd_ofAdd]
  rfl

lemma coboundary_of_residual_zero (b : Fin 24 → Fin 4 → ℕ)
    (hb : ∀ i, b 0 i = 0) (c : FactorSet α)
    (hz : coordinates (residual b hb c) = 0) : c.IsCoboundary := by
  let f := correctingCochain b c
  refine ⟨f, correctingCochain_one b hb c, ?_⟩
  intro s t
  have hres : (residual b hb c).value s t = 1 := by
    change ((residual b hb c).value s t).toAdd = (0 : Fin 4 → ZMod 2)
    funext i
    have h := congrFun hz (slot (index s) (index t) i)
    simpa only [coordinates, left_slot, right_slot, bit_slot, element_index, Pi.zero_apply] using h
  change c.value s t * (f s * α s (f t) * (f (s * t))⁻¹) = 1 at hres
  have he : c.value s t = f s * α s (f t) * f (s * t) := by
    simpa only [binary_inv] using mul_eq_one_iff_eq_inv.mp hres
  change c.value s t * f (s * t) = f s * α s (f t) * 1
  rw [he, mul_assoc, binary_mul_self]

/-- A checked elimination and cochain matrix reduce splitting to one scalar obstruction. -/
lemma coboundary_of_certificate (cols : SymmetricFour → Fin 4 → Fin 16)
    (ha : ∀ s v, α s v = matrixActionFun cols s v)
    (ss : StepTable) (hv : Valid ss (rawRow cols))
    (piv : Fin 2304 → ℕ) (hc : Covers ss piv)
    (b : Fin 24 → Fin 4 → ℕ) (hb : ∀ i, b 0 i = 0) (obstruction : ℕ)
    (hf : ∀ p, piv p = 0 → defectMask cols b p = 0 ∨ defectMask cols b p = obstruction)
    (c : FactorSet α) (ho : ev (coordinates c) obstruction = 0) : c.IsCoboundary := by
  apply coboundary_of_residual_zero b hb c
  apply kernel_zero _ ss (rawRow cols) hv (rawRow_zero cols ha _) piv hc
  intro p hp
  rw [coordinates_residual cols ha]
  rcases hf p hp with h | h
  · rw [h, ev_zero]
  · rw [h, ho]

lemma coordinates_times (c d : FactorSet α) :
    coordinates (times c d) = coordinates c + coordinates d := rfl

lemma cohomologous_of_times_isCoboundary (c d : FactorSet α)
    (h : (times c d).IsCoboundary) : c.Cohomologous d := by
  obtain ⟨b, hb, he⟩ := h
  refine ⟨b, hb, ?_⟩
  intro s t
  have hst : (c.value s t * d.value s t) * b (s * t) = b s * α s (b t) := by
    simpa only [times, FactorSet.trivial, mul_one] using he s t
  calc
    c.value s t * b (s * t) = c.value s t * b (s * t) * (d.value s t * d.value s t) := by
      rw [binary_mul_self, mul_one]
    _ = ((c.value s t * d.value s t) * b (s * t)) * d.value s t := by ac_rfl
    _ = b s * α s (b t) * d.value s t := congrArg (· * d.value s t) hst

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.ExtraExtensions.Cohomology
