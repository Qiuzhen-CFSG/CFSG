module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.Actions
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.CentralizerModels
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.RepresentativeKernel.Enumeration
public import Mathlib.Data.Fin.VecNotation

/-!
# The parity-twisted model is the involution centralizer in M22

Seven explicit permutations in the genuine degree-22 Mathieu group give four
binary translations and lifts of the three adjacent transpositions of S4.
Words in the Atlas generators certify membership. Finite identities checked
by Lean's kernel establish the two homomorphisms and their conjugation law:
an odd permutation adds the coordinate sum after permuting the four coordinates.
The complement is faithful on the fixed hexad, whereas the binary subgroup
fixes it pointwise; this proves injectivity of the semidirect-product map.

The geometric upper bound 384 from `RepresentativeKernel.Enumeration` proves
surjectivity. That bound uses the actual hexad stabilizer of order 5760 and
fifteen distinct conjugates, through `HexadExtension` and `KernelGeometry`.
It does not use centralizer-order metadata or a group-recognition theorem.

This is the Mathieu local model in the remark on printed p.224 of D. Held,
"A Characterization of some multiply transitive permutation groups, I",
Illinois J. Math. 13 (1969), 224–240, DOI 10.1215/ijm/1256053756.
The explicit witnesses were found using GAP; only their kernel-checked
permutation identities enter the proof. Tables use the project's degree-22
labels and function composition, so the rightmost letter acts first.
-/

open Sporadic.Mathieu Subgroup
namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
set_option maxRecDepth 100000
-- The first four permutations are the images of the binary basis vectors;
-- the final three lift the adjacent transpositions of S4.
private def generatorCode : Fin 7 → Nat :=
  ![877989290924446570944893155836258,
    877989641504456781631586663990347,
    877989709217092295636861487326724,
    877989251024793169490195304695171,
    838137768167481114934586504228262,
    875456630847756300122015346559302,
    227724423933342971724764080638374]

private def generatorTable (i : Fin 7) : Fin 22 → Fin 22 :=
  M22RepresentativeKernel.tableApply (generatorCode i)

private theorem generator_involutive : ∀ i : Fin 7, Function.Involutive (generatorTable i) := by
  change ∀ i x, generatorTable i (generatorTable i x) = x
  decide +kernel
private def generator (i : Fin 7) : Equiv.Perm (Fin 22) where
  toFun := generatorTable i
  invFun := generatorTable i
  left_inv := generator_involutive i
  right_inv := generator_involutive i
private def atlasWord : Fin 7 → List (Fin 3) :=
  ![[1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2],
    [0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 1, 0, 2, 0, 1],
    [0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2],
    [0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1],
    [2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0, 1],
    [2, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 1, 0, 1],
    [1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2]]
private theorem generator_word_apply : ∀ (i : Fin 7) (x : Fin 22),
    generatorTable i x = M22RepresentativeKernel.wordAction (atlasWord i) x := by
  decide +kernel
private theorem generator_word (i : Fin 7) :
    generator i = (M22RepresentativeKernel.wordElement (atlasWord i)).val := by
  apply Equiv.ext
  intro x
  rw [M22RepresentativeKernel.wordElement_apply]
  exact generator_word_apply i x
private theorem generator_mem (i : Fin 7) : generator i ∈ M22 := by
  rw [generator_word]
  exact (M22RepresentativeKernel.wordElement (atlasWord i)).property
private theorem generator_commutes : ∀ i : Fin 7,
    generator i * m22GeneratorA = m22GeneratorA * generator i := by
  decide +kernel
private noncomputable def generatorElement (i : Fin 7) : CentralizerModels.m22Centralizer :=
  ⟨⟨generator i, generator_mem i⟩, mem_centralizer_singleton_iff.mpr
    (Subtype.ext (generator_commutes i))⟩

private def symmetricWord (s : SymmetricFour) : List (Fin 3) :=
  match 16 * (s 0).val + 4 * (s 1).val + (s 2).val with
  | 6 => []
  | 7 => [2]
  | 9 => [1]
  | 11 => [1, 2]
  | 13 => [2, 1]
  | 14 => [1, 2, 1]
  | 18 => [0]
  | 19 => [0, 2]
  | 24 => [0, 1]
  | 27 => [0, 1, 2]
  | 28 => [0, 2, 1]
  | 30 => [0, 1, 2, 1]
  | 33 => [1, 0]
  | 35 => [1, 0, 2]
  | 36 => [0, 1, 0]
  | 39 => [0, 1, 0, 2]
  | 44 => [1, 0, 2, 1]
  | 45 => [0, 1, 0, 2, 1]
  | 49 => [2, 1, 0]
  | 50 => [1, 2, 1, 0]
  | 52 => [0, 2, 1, 0]
  | 54 => [0, 1, 2, 1, 0]
  | 56 => [1, 0, 2, 1, 0]
  | 57 => [0, 1, 0, 2, 1, 0]
  | _ => []

private def binaryPermutation (v : BinaryFour) : Equiv.Perm (Fin 22) :=
  (if v.toAdd 0 = 1 then generator 0 else 1) *
  (if v.toAdd 1 = 1 then generator 1 else 1) *
  (if v.toAdd 2 = 1 then generator 2 else 1) *
  (if v.toAdd 3 = 1 then generator 3 else 1)
private def complementPermutation (s : SymmetricFour) : Equiv.Perm (Fin 22) :=
  ((symmetricWord s).map (fun i => generator ⟨i.val + 4, by omega⟩)).prod
private noncomputable def binaryElement (v : BinaryFour) : CentralizerModels.m22Centralizer :=
  (if v.toAdd 0 = 1 then generatorElement 0 else 1) *
  (if v.toAdd 1 = 1 then generatorElement 1 else 1) *
  (if v.toAdd 2 = 1 then generatorElement 2 else 1) *
  (if v.toAdd 3 = 1 then generatorElement 3 else 1)
private noncomputable def complementElement (s : SymmetricFour) : CentralizerModels.m22Centralizer :=
  ((symmetricWord s).map (fun i => generatorElement ⟨i.val + 4, by omega⟩)).prod
private theorem binaryElement_coe (v : BinaryFour) :
    (binaryElement v).val.val = binaryPermutation v := by
  dsimp only [binaryElement, binaryPermutation]
  split_ifs <;> rfl
private theorem complementElement_coe (s : SymmetricFour) :
    (complementElement s).val.val = complementPermutation s := by
  change (M22.subtype.comp CentralizerModels.m22Centralizer.subtype)
    (((symmetricWord s).map (fun i => generatorElement ⟨i.val + 4, by omega⟩)).prod) = _
  simp only [map_list_prod, List.map_map]
  rfl
private theorem binary_one : binaryPermutation 1 = 1 := by decide +kernel
private theorem binary_mul : ∀ v w : BinaryFour,
    binaryPermutation (v * w) = binaryPermutation v * binaryPermutation w := by
  decide +kernel
private theorem complement_one : complementPermutation 1 = 1 := by decide +kernel
private theorem complement_mul : ∀ s t : SymmetricFour,
    complementPermutation (s * t) = complementPermutation s * complementPermutation t := by
  decide +kernel

private theorem binary_conjugate : ∀ (s : SymmetricFour) (v : BinaryFour),
    binaryPermutation (twistedAction s v) =
      complementPermutation s * binaryPermutation v * (complementPermutation s)⁻¹ := by
  decide +kernel
private noncomputable def binaryHom : BinaryFour →* CentralizerModels.m22Centralizer where
  toFun := binaryElement
  map_one' := by
    apply Subtype.ext; apply Subtype.ext
    rw [binaryElement_coe]
    exact binary_one
  map_mul' v w := by
    apply Subtype.ext; apply Subtype.ext
    simp only [Subgroup.coe_mul, binaryElement_coe]
    exact binary_mul v w
private noncomputable def complementHom : SymmetricFour →* CentralizerModels.m22Centralizer where
  toFun := complementElement
  map_one' := by
    apply Subtype.ext; apply Subtype.ext
    rw [complementElement_coe]
    exact complement_one
  map_mul' s t := by
    apply Subtype.ext; apply Subtype.ext
    simp only [Subgroup.coe_mul, complementElement_coe]
    exact complement_mul s t

private noncomputable def twistedCentralizerHom : TwistedModel →* CentralizerModels.m22Centralizer :=
  SemidirectProduct.lift binaryHom complementHom (by
    intro s
    apply MonoidHom.ext
    intro v
    apply Subtype.ext; apply Subtype.ext
    change (binaryElement (twistedAction s v)).val.val =
      (complementElement s).val.val * (binaryElement v).val.val *
        ((complementElement s).val.val)⁻¹
    rw [binaryElement_coe, binaryElement_coe, complementElement_coe]
    exact binary_conjugate s v)
private theorem twistedCentralizerHom_coe (x : TwistedModel) :
    (twistedCentralizerHom x).val.val =
      binaryPermutation x.left * complementPermutation x.right := by
  change (binaryElement x.left * complementElement x.right).val.val = _
  simp only [Subgroup.coe_mul, binaryElement_coe, complementElement_coe]

private theorem binary_injective : Function.Injective binaryPermutation := by decide +kernel
private theorem complement_separated : ∀ s t : SymmetricFour,
    (∀ a : Fin 22, m22GeneratorA a = a → complementPermutation s a = complementPermutation t a) →
      s = t := by decide +kernel
private theorem binary_fix : ∀ (v : BinaryFour) (a : Fin 22),
    m22GeneratorA a = a → binaryPermutation v a = a := by decide +kernel
private theorem complement_fix : ∀ (s : SymmetricFour) (a : Fin 22),
    m22GeneratorA a = a → m22GeneratorA (complementPermutation s a) = complementPermutation s a := by
  decide +kernel

private theorem twistedCentralizerHom_injective : Function.Injective twistedCentralizerHom := by
  intro x y h
  have he := congrArg (fun c : CentralizerModels.m22Centralizer => c.val.val) h
  rw [twistedCentralizerHom_coe, twistedCentralizerHom_coe] at he
  have hs : x.right = y.right := by
    apply complement_separated
    intro a ha
    have h' := Equiv.congr_fun he a
    simpa only [Equiv.Perm.mul_apply,
      binary_fix _ _ (complement_fix _ _ ha)] using h'
  have hv : x.left = y.left := by
    apply binary_injective
    rw [hs] at he
    exact mul_right_cancel he
  exact SemidirectProduct.ext hv hs
private theorem twistedModel_card : Nat.card TwistedModel = 384 := by
  rw [SemidirectProduct.card]
  norm_num [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_perm, Nat.factorial]

private theorem twistedCentralizerHom_bijective : Function.Bijective twistedCentralizerHom :=
  twistedCentralizerHom_injective.bijective_of_nat_card_le (by
    rw [twistedModel_card]
    exact M22RepresentativeKernel.centralizer_card_le)

/-- The parity-twisted binary semidirect product is the actual centralizer of
the first Atlas involution in the genuine degree-22 Mathieu group. -/
public noncomputable def twistedModelEquivM22Centralizer :
    TwistedModel ≃* CentralizerModels.m22Centralizer :=
  MulEquiv.ofBijective twistedCentralizerHom twistedCentralizerHom_bijective

end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
