module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.FAction.Identification.Certificate
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.FAction.Identification.FivePoints
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.FAction.Orbits

/-!
# Identification of the transitive F-automizer of order 120

Orbit–stabilizer makes the given local subgroup the exact stabilizer of z.
Choose an automorphism sending z to d. A checked word in it and the local
actors produces a canonical generator: the alternative would give a larger
stabilizer of z. The canonical generator supplies 120 distinct words whose
faithful action on five triples identifies the whole group with S5.

This proves the finite conditional contract used in the normalizer-quotient
assembly. No global recognition or involution-fusion theorem is assumed.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 2, proof of Lemma 2, printed pp.4–5.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.FAction
open Identification

local instance : Finite modelF := Nat.finite_of_card_ne_zero (modelF_card ▸ (by decide))
local instance : Finite (MulAut modelF) := Finite.of_injective
  (fun a : MulAut modelF => (a : modelF → modelF)) DFunLike.coe_injective

private theorem exact_stabilizer (H : Subgroup (MulAut modelF))
    (hlocal : localAutomizer ≤ H) (hcard : Nat.card H = 120)
    (htrans : ∀ x y : modelF, x ≠ 1 → y ≠ 1 → ∃ a : H, (a : MulAut modelF) x = y)
    (a : MulAut modelF) (ha : a ∈ H) (hfix : a pointZ = pointZ) : a ∈ localAutomizer := by
  have ho : MulAction.orbit H pointZ = ({1} : Set modelF)ᶜ := by
    ext x
    constructor
    · rintro ⟨g, rfl⟩ hx
      exact pointZ_ne_one ((g : MulAut modelF).injective (hx.trans (map_one _).symm))
    · intro hx
      exact htrans pointZ x pointZ_ne_one hx
  have hn : (({1} : Set modelF)ᶜ).ncard = 15 := by
    rw [Set.ncard_compl, Set.ncard_singleton, modelF_card]
  have hc := (MulAction.stabilizer H pointZ).card_mul_index
  rw [MulAction.index_stabilizer, ho, hn, hcard] at hc
  have hs : Nat.card (MulAction.stabilizer H pointZ) = 8 := by omega
  have hle : localAutomizer.subgroupOf H ≤ MulAction.stabilizer H pointZ := by
    intro g hg
    exact local_fixes_pointZ g hg
  have he : localAutomizer.subgroupOf H = MulAction.stabilizer H pointZ :=
    eq_of_le_of_card_ge hle (by
      rw [hs, Nat.card_congr (subgroupOfEquivOfLe hlocal).toEquiv, localAutomizer_card])
  have hmem : (⟨a, ha⟩ : H) ∈ MulAction.stabilizer H pointZ := hfix
  rw [← he] at hmem
  exact hmem

/-- The actual transitive order-120 overgroup of the local F-action is S5. -/
public theorem finite_identification (H : Subgroup (MulAut modelF))
    (hlocal : localAutomizer ≤ H) (hcard : Nat.card H = 120)
    (htrans : ∀ x y : modelF, x ≠ 1 → y ≠ 1 →
      ∃ a : H, (a : MulAut modelF) x = y) :
    Nonempty (H ≃* Equiv.Perm (Fin 5)) := by
  obtain ⟨f, hf⟩ := htrans pointZ pointD pointZ_ne_one pointD_ne_one
  have hcol : matrix f 0 = 8 := by
    apply word_injective
    have he := matrix_spec f 0
    change (f : MulAut modelF) (word 1) = word (matrix f 0) at he
    rw [word_one, hf] at he
    exact he.symm.trans word_eight.symm
  obtain ⟨w, hw⟩ := matrix_certificate (matrix f) hcol (matrix_nonsingular f)
  have hmem : evalAut f w ∈ H := evalAut_mem H hlocal f f.property w
  rcases hw with ⟨k, hk⟩ | ⟨hfix, hout⟩
  · exact identification_of_seed H hlocal hcard (evalAut f w) hmem k
      ((matrix_evalAut f w).trans hk)
  · have he := matrix_spec (evalAut f w) 0
    change evalAut f w (word 1) = word (matrix (evalAut f w) 0) at he
    rw [matrix_evalAut, hfix, word_one] at he
    obtain ⟨j, hj⟩ := matrix_of_mem_local (evalAut f w)
      (exact_stabilizer H hlocal hcard htrans _ hmem he)
    exact False.elim (hout j ((matrix_evalAut f w).symm.trans hj))

end Theory.GroupTheory.HeldM22A10.M22Identification.CaseII.FAction
