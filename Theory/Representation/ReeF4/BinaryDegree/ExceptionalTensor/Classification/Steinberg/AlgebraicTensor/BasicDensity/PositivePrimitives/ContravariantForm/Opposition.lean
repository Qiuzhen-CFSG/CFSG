module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.WeylTransport

/-!
# An actual representative of root negation in F₄

The sixth power of the Coxeter word `(0,1,2,3)` acts as minus the identity on
both roots and integral coroot weights. We check its coordinate action in
blocks of four and twelve reflections. The actual normalizer-word conjugation
identity then gives root negation inside the algebraic carrier, with unchanged
parameters in characteristic two.

The coordinate reflection formulas use the fixed realization from
`EndNode.WeylTransport.RootTransport`. The resulting carrier identity is the
Weyl-transport step in the rational contravariant-form construction underlying
the primitive-vector argument of Steinberg, *Representations of Algebraic
Groups*, Nagoya Math. J. 22 (1963), §§2, 4, and 11.1,
DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.ContravariantForm
noncomputable section
variable {F : Type*} [Field F] [IsAlgClosed F]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

private def reflectedVector : Fin 4 → Vec 4 → Vec 4
  | 0, v => ![v 0, v 2, v 1, v 3]
  | 1, v => ![v 0, v 1, v 3, v 2]
  | 2, v => ![v 0, v 1, v 2, -v 3]
  | 3, v => ![(v 0 + v 1 + v 2 + v 3) / 2,
      (v 0 + v 1 - v 2 - v 3) / 2,
      (v 0 - v 1 + v 2 - v 3) / 2,
      (v 0 - v 1 - v 2 + v 3) / 2]

private theorem reflection_val (i : Fin 4) (r : F4Chevalley.Root) :
    (typeF4RootPairing.reflectionPerm (typeF4SimpleRootIndex i) r).val =
      reflectedVector i r.val := by
  change typeF4RootPairing.root (typeF4RootPairing.reflectionPerm _ r) = _
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root,
    typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [reflectedVector, typeF4SimpleRoot, dot, Fin.sum_univ_four] <;> ring

private def coxeterWord : List (Fin 4) := [0, 1, 2, 3]
private def halfWord : List (Fin 4) := coxeterWord ++ coxeterWord ++ coxeterWord

/-- Six Coxeter words, whose root and weight actions are negation. -/
def oppositionWord : List (Fin 4) := halfWord ++ halfWord

private theorem inverseRootWord_append (a b : List (Fin 4)) (r : F4Chevalley.Root) :
    EndNode.inverseRootWord (a ++ b) r =
      EndNode.inverseRootWord a (EndNode.inverseRootWord b r) := by
  induction a with
  | nil => rfl
  | cons i a ih => simp only [List.cons_append, EndNode.inverseRootWord, ih]

private theorem coxeterWord_val (r : F4Chevalley.Root) :
    (EndNode.inverseRootWord coxeterWord r).val =
      ![(r.val 0 + r.val 1 + r.val 2 + r.val 3) / 2,
        (-r.val 0 + r.val 1 + r.val 2 - r.val 3) / 2,
        (r.val 0 + r.val 1 - r.val 2 - r.val 3) / 2,
        (r.val 0 - r.val 1 + r.val 2 - r.val 3) / 2] := by
  simp only [coxeterWord, EndNode.inverseRootWord, reflection_val]
  ext k
  fin_cases k <;> simp [reflectedVector, Matrix.cons_val_two, Matrix.cons_val_three]
  ring

private theorem halfWord_val (r : F4Chevalley.Root) :
    (EndNode.inverseRootWord halfWord r).val = ![r.val 1, -r.val 0, -r.val 3, r.val 2] := by
  simp only [halfWord, inverseRootWord_append, coxeterWord_val]
  ext k
  fin_cases k <;> simp [Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

/-- The inverse word sends every actual root index to its opposite. -/
theorem inverseRootWord_opposition (r : F4Chevalley.Root) :
    EndNode.inverseRootWord oppositionWord r = -r := by
  apply Subtype.ext
  rw [oppositionWord, inverseRootWord_append, halfWord_val, halfWord_val]
  have hn : (-r).val = -r.val := by
    change typeF4RootPairing.root (-r) = -typeF4RootPairing.root r
    simp only [RootPairing.indexNeg_neg, RootPairing.root_reflectionPerm,
      RootPairing.reflection_apply_self]
  rw [hn]
  ext k
  fin_cases k <;> simp [Matrix.cons_val_two, Matrix.cons_val_three]

private theorem coxeterWord_weight (μ : EndNode.Weight) :
    coxeterWord.foldl (fun ν i => EndNode.reflectWeight i ν) μ =
      ![μ 1, μ 0 + μ 1 + μ 2, μ 3, -2 * μ 0 - 2 * μ 1 - μ 2 - μ 3] := by
  funext i
  fin_cases i <;>
    simp [coxeterWord, EndNode.reflectWeight, typeF4CartanMatrix, Fin.ext_iff,
      Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

private theorem halfWord_weight (μ : EndNode.Weight) :
    halfWord.foldl (fun ν i => EndNode.reflectWeight i ν) μ =
      ![μ 0 + 2 * μ 1 + μ 2 + μ 3, μ 1 + μ 2, -2 * μ 1 - μ 2,
        -2 * μ 0 - 2 * μ 1 - 2 * μ 2 - μ 3] := by
  simp only [halfWord, List.foldl_append, coxeterWord_weight]
  funext i
  fin_cases i <;> simp [Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

/-- The same word negates every integral coroot weight. -/
theorem oppositionWord_weight (μ : EndNode.Weight) :
    oppositionWord.foldl (fun ν i => EndNode.reflectWeight i ν) μ = -μ := by
  simp only [oppositionWord, List.foldl_append, halfWord_weight]
  funext i
  fin_cases i <;> simp [Matrix.cons_val_two, Matrix.cons_val_three] <;> ring

/-- An actual F₄ carrier representative of root negation. -/
def oppositionElement : Variety.Point (F4Chevalley.Carrier (k := F)) :=
  EndNode.normalizerWord oppositionWord

/-- Moving a root element past opposition negates its root. In characteristic
two the parameter is unchanged. -/
theorem root_opposition_commute [CharP F 2] (r : F4Chevalley.Root) (t : F) :
    algebraicRootElement r t * oppositionElement =
      oppositionElement * algebraicRootElement (-r) t := by
  exact (EndNode.root_normalizerWord_commute oppositionWord r t).trans
    (by rw [inverseRootWord_opposition]; rfl)

/-- Opposition carries a weight vector to the opposite integral weight. -/
theorem opposition_mem_neg_weight (B : AlgebraicFactor F)
    {μ : EndNode.Weight} {v : B.Space} (hv : v ∈ EndNode.corootWeightSpace B μ) :
    (B.action.action oppositionElement : Module.End F B.Space) v ∈
      EndNode.corootWeightSpace B (-μ) := by
  simpa only [oppositionWord_weight, oppositionElement] using
    EndNode.normalizerWord_mem_weight B oppositionWord hv

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.ContravariantForm
