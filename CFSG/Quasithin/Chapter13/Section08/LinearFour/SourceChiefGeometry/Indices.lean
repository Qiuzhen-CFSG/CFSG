module

public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceApplication

/-!
# The intersection argument in 13.8.32(1)–(2)

On the literal quotient V_H/U_H, the orthogonal module calculation gives
an intersection image of order at least four. Equality forces the actor
image to have order two. The intersection with U_H is nontrivial, and
|Uγ| = 32. Multiplication of actual subgroup indices then proves both
|Uγ : Uγ ∩ Q_H| = 2 and |Uγ ∩ V_H| ≥ 8.

The final application feeds these conclusions directly to the existing
faithful-section G.6.4 consumer. The orthogonal displacement assertion,
its equality case, and the critical-pair commutator containment remain
explicit inputs; this is the arithmetic and quotient part of the source
argument, not a proof that the source supplies those inputs.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), 13.8.32, printed p.965.
-/

public section
open Subgroup Representation
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open ChapterG.Section06 BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G]

/-- Multiplying the actual intersection indices proves both conclusions of
the first paragraph of 13.8.32. No rank or intersection-order conclusion is
assumed. -/
theorem source_critical_intersection_indices
    (Uγ UH VH QH : Subgroup G) (hUV : UH ≤ VH) (hVQ : VH ≤ QH)
    (hU : Nat.card Uγ = 32) (houtside : ¬ Uγ ≤ QH)
    (hmeet : Uγ ⊓ UH ≠ ⊥)
    (himage : 4 ≤ UH.relIndex (Uγ ⊓ VH))
    (hequality : UH.relIndex (Uγ ⊓ VH) = 4 → QH.relIndex Uγ = 2) :
    QH.relIndex Uγ = 2 ∧ 8 ≤ Nat.card (Uγ ⊓ VH : Subgroup G) := by
  have hsmall : 2 ≤ Nat.card (Uγ ⊓ UH : Subgroup G) := by
    have hp : 0 < Nat.card (Uγ ⊓ UH : Subgroup G) := Nat.card_pos
    have hn : Nat.card (Uγ ⊓ UH : Subgroup G) ≠ 1 := by
      intro h
      exact hmeet (Subgroup.card_eq_one.mp h)
    omega
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup G)
    (Uγ ⊓ UH) (Uγ ⊓ VH) bot_le (inf_le_inf_left Uγ hUV)
  rw [relIndex_bot_left, relIndex_bot_left] at hmul
  have he : (Uγ ⊓ UH).relIndex (Uγ ⊓ VH) = UH.relIndex (Uγ ⊓ VH) := by
    rw [← inf_relIndex_right (Uγ ⊓ UH) (Uγ ⊓ VH),
      ← inf_relIndex_right UH (Uγ ⊓ VH)]
    congr 1
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_right) inf_le_right
    · exact le_inf (le_inf (inf_le_right.trans inf_le_left) inf_le_left) inf_le_right
  rw [he] at hmul
  have hlarge : 8 ≤ Nat.card (Uγ ⊓ VH : Subgroup G) := by nlinarith
  refine ⟨?_, hlarge⟩
  by_cases hfour : UH.relIndex (Uγ ⊓ VH) = 4
  · exact hequality hfour
  have himage' : 4 < UH.relIndex (Uγ ⊓ VH) := by omega
  have hlarge' : 8 < Nat.card (Uγ ⊓ VH : Subgroup G) := by nlinarith
  have hcardQ := relIndex_mul_relIndex (⊥ : Subgroup G) (Uγ ⊓ QH) Uγ
    bot_le inf_le_left
  rw [relIndex_bot_left, relIndex_bot_left, inf_relIndex_left, hU] at hcardQ
  have hle : Nat.card (Uγ ⊓ VH : Subgroup G) ≤ Nat.card (Uγ ⊓ QH : Subgroup G) :=
    Nat.card_le_card_of_injective (inclusion (inf_le_inf_left Uγ hVQ))
      (inclusion_injective _)
  have hpositive : QH.relIndex Uγ ≠ 0 := (QH.subgroupOf Uγ).index_ne_zero_of_finite
  have hnotone : QH.relIndex Uγ ≠ 1 := fun h => houtside (relIndex_eq_one.mp h)
  have hdiv : QH.relIndex Uγ ∣ 32 := hU ▸ relIndex_dvd_card QH Uγ
  have hbound : QH.relIndex Uγ < 4 := by nlinarith
  have hcases : QH.relIndex Uγ = 2 ∨ QH.relIndex Uγ = 3 := by omega
  rcases hcases with htwo | hthree
  · exact htwo
  · rw [hthree] at hdiv
    norm_num at hdiv

/-- The index calculation supplies the literal inputs to the existing G.6.4
application on any faithful irreducible H/O₂(H)-section in H_C/V_H. -/
theorem source_section_model_of_intersection_image
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (H QH HC VH UH Uγ S E : Subgroup G) [IsElementaryAbelian 2 Uγ]
    (hQH : QH = H.pCoreIn 2)
    (σ : Representation (ZMod 2) (H ⧸ pCore 2 H) W)
    [IsIrreducible σ] (hf : Function.Injective σ)
    (d : BinaryConjugationSection H S E (σ.comp (QuotientGroup.mk' (pCore 2 H))))
    (hVE : VH ≤ E) (hSC : S ≤ HC) (hCQ : HC ≤ QH)
    (hUV : UH ≤ VH) (hU : Nat.card Uγ = 32) (houtside : ¬ Uγ ≤ QH)
    (hmeet : Uγ ⊓ UH ≠ ⊥)
    (himage : 4 ≤ UH.relIndex (Uγ ⊓ VH))
    (hequality : UH.relIndex (Uγ ⊓ VH) = 4 → QH.relIndex Uγ = 2)
    (hcomm : ⁅HC, Uγ⁆ ≤ HC ⊓ Uγ) (hUH : Uγ ≤ H)
    (hcover : IsSQTK KnownSimple.IsKnownSimple H)
    (e : (H ⧸ pCore 2 H) ≃* BinaryLinear.OuterCyclic.LinearGroup 4) :
    HasModelOn σ ⊤ ⊤ (binaryLinearAction 4) ∧
      Module.finrank (ZMod 2) W = 4 := by
  obtain ⟨hi, hc⟩ := source_critical_intersection_indices Uγ UH VH QH hUV
    (hVE.trans (d.kernel_le.trans (hSC.trans hCQ))) hU houtside hmeet himage hequality
  exact section_four_model H QH HC VH Uγ S E hQH σ hf d hVE hSC hCQ
    hU hi hc hcomm hUH hcover e

end CFSG.Quasithin.Chapter13.Section08.LinearFour
