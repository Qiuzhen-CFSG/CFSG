module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Rudvalis.Coverage.TwoCore.Generation.Words

/-!
# Pointwise checking of Rudvalis recovery words

The fourteen fixed generators already have certified point maps. Their
fourth powers are one, so three iterations of each map give the inverse
letter. Together with supplied point maps for an adjoined element and its
inverse, these tables evaluate recovery words on all 4060 points.

Every table is linked to the action of the original model element. Hence
faithfulness can turn kernel-checked pointwise identities into group-word
equalities, without trusting the program which discovered the words.
The generator tables and ATLAS sources are those of
`SylowCertificate.LocalOrder`; the source application is the Sylow-overgroup
argument cited in Aschbacher--Smith, printed p.511 (PDF p.528).
-/

namespace Rudvalis.SylowOvergroups.TwoCore.Generation
open RadicalCoverage.SylowCertificate Theory.GroupTheory.SubgroupEnumeration
open Theory.GroupTheory

/-- Positive letters followed by inverse letters, using the certified Sylow maps. -/
@[expose] public def extensionLetterMap (f fi : Fin 4060 → Fin 4060) (i : Fin 30) : Fin 4060 → Fin 4060 :=
  Fin.addCases (fun j : Fin 15 => Fin.lastCases f LocalOrder.generatorMap j)
    (fun j : Fin 15 => Fin.lastCases fi (fun k : Fin 14 => (LocalOrder.generatorMap k)^[3]) j) i

/-- The certified fourth-power relation determines each inverse point map. -/
public theorem generator_inv_smul (i : Fin 14) (x : Fin 4060) :
    (candidateGenerator i)⁻¹ • x = (LocalOrder.generatorMap i)^[3] x := by
  apply inv_smul_eq_iff.mpr
  rw [LocalOrder.generator_smul]
  have h := LocalOrder.generator_pow_smul i 4 x
  rw [LocalOrder.generator_fourth, one_smul] at h
  simpa only [Function.iterate_succ_apply', Function.iterate_zero, id_eq] using h

/-- The complete letter table describes the actual model action. -/
public theorem extensionLetters_smul (g : Model) (f fi : Fin 4060 → Fin 4060)
    (hf : ∀ x, g • x = f x) (hfi : ∀ x, g⁻¹ • x = fi x)
    (i : Fin 30) (x : Fin 4060) :
    symmGen (extensionGenerators g) i • x = extensionLetterMap f fi i x := by
  refine Fin.addCases (m := 15) (n := 15) (fun j => ?_) (fun j => ?_) i
  · simp only [symmGen, extensionLetterMap, Fin.addCases_left]
    refine Fin.lastCases ?_ (fun k => ?_) j
    · exact hf x
    · simpa only [extensionGenerators, Fin.lastCases_castSucc] using LocalOrder.generator_smul k x
  · simp only [symmGen, extensionLetterMap, Fin.addCases_right]
    refine Fin.lastCases ?_ (fun k => ?_) j
    · exact hfi x
    · simpa only [extensionGenerators, Fin.lastCases_castSucc] using generator_inv_smul k x

/-- Pure point-map evaluation agrees with evaluation in Rudvalis.Model. -/
public theorem extensionWord_smul (g : Model) (f fi : Fin 4060 → Fin 4060)
    (hf : ∀ x, g • x = f x) (hfi : ∀ x, g⁻¹ • x = fi x)
    (w : List (Fin 30)) (x : Fin 4060) :
    extensionWord g w • x = LocalOrder.evalWord (extensionLetterMap f fi) w x := by
  induction w generalizing x with
  | nil => exact one_smul Model x
  | cons i w ih =>
    change (symmGen (extensionGenerators g) i * extensionWord g w) • x = _
    rw [mul_smul, ih, extensionLetters_smul g f fi hf hfi]
    rfl
end Rudvalis.SylowOvergroups.TwoCore.Generation
