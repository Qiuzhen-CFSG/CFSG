module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22TransvectionComparison.Generation.Seeds
/-!
# Cancellation of Fi22 BFS tree edges

If the actual transporter letter list differs by one generator prefix, the
Schreier edge cancels to the identity. For A the reversed tree edge also
cancels, using its already proved involution equation. These inexpensive word
checks discharge most edges before any 48-coordinate comparison is needed.

The remaining edges are checked against certified subgroup products in Data.
Source: the fixed ATLAS BFS words in RootWords and the conjugation action
following GLS3 Table 5.3t, `refs/KGroup/GLS3/Chapter5(sec3-).tex`.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
open KernelCertificate

def transportLetters (x : Fin 3510) : List Bool := (rootWordCode x).bits.dropLast

theorem pointTransport_prefix (b : Bool) (x y : Fin 3510)
    (h : transportLetters x = b :: transportLetters y) :
    pointTransport x = inverseLetter b * pointTransport y := by
  change ((transportLetters x).map inverseLetter).prod = _
  rw [h, List.map_cons, List.prod_cons]
  rfl

def treeCheck (b : Bool) (x : Fin 3510) : Bool :=
  let y := forwardLetter b x
  decide (transportLetters x = b :: transportLetters y) ||
    (!b && decide (transportLetters y = false :: transportLetters x))

theorem generator_eq_forwardLetter (b : Bool) (x : Fin 3510) :
    inclusion (if b then atlasB else atlasA) x = forwardLetter b x := by
  cases b
  · exact generatorA_apply_eq_fastA x
  · exact generatorB_apply_eq_fastB x

theorem treeCheck_mem (b : Bool) (x : Fin 3510) (h : treeCheck b x = true) :
    (pointTransport (inclusion (if b then atlasB else atlasA) x))⁻¹ *
      (if b then atlasB else atlasA) * pointTransport x ∈ commutingConjugateSubgroup := by
  rw [generator_eq_forwardLetter]
  have hid : (pointTransport (forwardLetter b x))⁻¹ *
      (if b then atlasB else atlasA) * pointTransport x = 1 := by
    simp only [treeCheck, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨hb, h⟩
    · rw [pointTransport_prefix b _ _ h]
      cases b <;> simp [inverseLetter, mul_assoc]
    · have hb : b = false := by cases b <;> simp_all
      subst b
      rw [pointTransport_prefix false _ _ h]
      have hA : atlasA * atlasA = 1 := by
        apply inclusion_injective
        simpa only [map_mul, map_one, inclusion_atlasA, pow_two] using generatorA_sq
      simp only [inverseLetter, Bool.false_eq_true, if_false, mul_inv_rev, inv_inv]
      rw [mul_assoc (pointTransport x)⁻¹ atlasA atlasA, hA]
      simp
  rw [hid]
  exact Subgroup.one_mem _
end Sporadic.Fischer.Fi22.TransvectionComparison.Generation.Edges
