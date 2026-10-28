module

public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.Normalizer.FiniteChecks
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.EvenImage.PairCertificate.Interpretation

/-!
# The field-linear normalizer of the literal even image

The checked word table covers the actual even group by its two generators.
Every order-four element in that image has a checked internal conjugator to
the first generator. After this conjugation, an arbitrary field-linear
normalizer commutes with that generator. Its nine matrix entries then depend
on three field elements, and the 64-case certificate identifies it with a
literal word whenever it also preserves the second generator's image.

All matrices are interpreted through the existing `fieldCoordinates` and
`PairCertificate.Interpretation` on the original hexacode. The conclusion
requires only that the conjugates of the two actual generators belong to
the actual image; no automorphism-realization or order-identification premise
is assumed. The binary consumer is `SixDimensionalRecognition.Normalizer`.

Source: Aschbacher–Smith, K.1.3, printed p.453 (PDF p.464). The generator
attribution and license are retained in `EvenImage/Generators.lean` and
`LICENSES/ATLAS.txt`. See `Normalizer/source/README.md` for reconstruction and
kernel-check measurements.
-/

@[expose] public section

open Atlas.Codes Subgroup
namespace Representation.Hexacode.SixDimensional
open EvenImage EvenImage.PairData NormalizerData
private theorem decode_cube (m : M) : decode (cube m) = decode m ^ 3 := by
  simp [cube, decode_mm, pow_succ]
private theorem decode_fourth (m : M) : decode (fourth m) = decode m ^ 4 := by
  simp [fourth, decode_mm, pow_succ, mul_assoc]
private theorem decode_zero : decode NormalizerData.zero = 0 := by decide +kernel
private theorem generatorA_inv : generatorA⁻¹ = generatorA ^ 3 := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [← pow_succ'] using generatorA_four
private theorem generatorB_inv : generatorB⁻¹ = generatorB ^ 2 := by
  apply inv_eq_of_mul_eq_one_right
  simpa only [← pow_succ'] using generatorB_three
private def modelLetter : Fin 4 → HexEvenAutomorphisms :=
  ![generatorA, generatorB, generatorA⁻¹, generatorB⁻¹]
private theorem modelLetter_zero : modelLetter 0 = generatorA := by
  simp only [modelLetter, Matrix.cons_val_zero]
private theorem modelLetter_one : modelLetter 1 = generatorB := by
  simp only [modelLetter, Matrix.cons_val_one, Matrix.cons_val_zero]
private def modelWord (w : List (Fin 4)) : HexEvenAutomorphisms :=
  (w.map modelLetter).prod
private theorem matrix_modelLetter (k : Fin 4) :
    matrix (evenFieldAction (modelLetter k)) = decode (letter k) := by
  have ha : matrix (evenFieldAction generatorA) = decode first := matrix_first
  fin_cases k <;>
    simp [modelLetter, letter, generatorA_inv, generatorB_inv, map_pow, ha, matrix_second, decode_cube, decode_mm, pow_two]
private theorem matrix_modelWord (w : List (Fin 4)) :
    matrix (evenFieldAction (modelWord w)) = decode (word w) := by
  induction w with
  | nil => simp [modelWord, word, decode_ident]
  | cons k w ih =>
    change matrix (evenFieldAction (modelLetter k * modelWord w)) =
      decode (mm (letter k) (word w))
    rw [map_mul, map_mul, matrix_modelLetter, ih, decode_mm]
private theorem entry_mem (k : Fin 1080) :
    ∃ g : HexEvenAutomorphisms, matrix (evenFieldAction g) = decode (entry k) := by
  refine ⟨modelWord (entryWord k), ?_⟩
  rw [matrix_modelWord, (entry_checks k).1]
private theorem generated_pair_induction {G : Type*} [Group G] (a b : G)
    (hgen : closure ({a,b} : Set G) = ⊤) (P : G → Prop) (h1 : P 1)
    (hs : ∀ x, P x → P (a*x) ∧ P (b*x) ∧ P (a⁻¹*x) ∧ P (b⁻¹*x)) (g : G) : P g := by
  have hg : g ∈ closure ({a,b} : Set G) := by rw [hgen]; trivial
  induction hg using Subgroup.closure_induction_left with
  | one => exact h1
  | mul_left x hx y _ ih =>
    rcases hx with rfl | rfl
    · exact (hs y ih).1
    · exact (hs y ih).2.1
  | inv_mul_cancel x hx y _ ih =>
    rcases hx with rfl | rfl
    · exact (hs y ih).2.2.1
    · exact (hs y ih).2.2.2
private theorem generated_pair_induction_positive {G : Type*} [Group G] (a b : G)
    (hgen : closure ({a,b} : Set G) = ⊤) (ha : a ^ 4 = 1) (hb : b ^ 3 = 1)
    (P : G → Prop) (h1 : P 1)
    (hA : ∀ x, P x → P (a*x)) (hB : ∀ x, P x → P (b*x)) (g : G) : P g := by
  have hai : a⁻¹ = a ^ 3 := inv_eq_of_mul_eq_one_right (by simpa only [← pow_succ'] using ha)
  have hbi : b⁻¹ = b ^ 2 := inv_eq_of_mul_eq_one_right (by simpa only [← pow_succ'] using hb)
  apply generated_pair_induction a b hgen P h1 _ g
  intro x hx
  refine ⟨hA x hx, hB x hx, ?_, ?_⟩
  · have hh := hA _ (hA _ (hA _ hx))
    have he : a * (a * (a * x)) = a⁻¹ * x := by rw [hai]; simp [pow_succ, mul_assoc]
    exact he ▸ hh
  · have hh := hB _ (hB _ hx)
    have he : b * (b * x) = b⁻¹ * x := by rw [hbi]; simp [pow_succ, mul_assoc]
    exact he ▸ hh
private theorem image_covered (g : HexEvenAutomorphisms) :
    ∃ k : Fin 1080, matrix (evenFieldAction g) = decode (entry k) := by
  have step_mem (j : Fin 4) (y : HexEvenAutomorphisms)
      (hy : ∃ k : Fin 1080, matrix (evenFieldAction y) = decode (entry k)) :
      ∃ k : Fin 1080, matrix (evenFieldAction (modelLetter j * y)) = decode (entry k) := by
    obtain ⟨k, hk⟩ := hy
    refine ⟨step k j, ?_⟩
    rw [map_mul, map_mul, matrix_modelLetter, hk, ← decode_mm, (entry_checks k).2.2.1]
  have step_letter (x : HexEvenAutomorphisms) (j : Fin 4) (hx : modelLetter j = x)
      (y : HexEvenAutomorphisms)
      (hy : ∃ k : Fin 1080, matrix (evenFieldAction y) = decode (entry k)) :
      ∃ k : Fin 1080, matrix (evenFieldAction (x * y)) = decode (entry k) := by
    cases hx
    exact step_mem j y hy
  exact generated_pair_induction_positive generatorA generatorB generators_closure
    generatorA_four generatorB_three
    (fun g => ∃ k : Fin 1080, matrix (evenFieldAction g) = decode (entry k))
    ⟨0, by rw [map_one, map_one]; exact decode_ident.symm⟩
    (fun y hy => step_letter generatorA 0 modelLetter_zero y hy)
    (fun y hy => step_letter generatorB 1 modelLetter_one y hy) g

private theorem order_four_conjugate (v : FieldGL) (hv : v ∈ evenFieldAction.range)
    (h4 : v ^ 4 = 1) (h2 : v ^ 2 ≠ 1) :
    ∃ c : FieldGL, c ∈ evenFieldAction.range ∧ c * fieldGenerator = v * c := by
  obtain ⟨g, rfl⟩ := hv
  obtain ⟨k, hk⟩ := image_covered g
  have hf : fourth (entry k) = ident := by
    apply decode_injective
    rw [decode_fourth, ← hk, ← map_pow, h4, map_one, decode_ident]
  have hs : mm (entry k) (entry k) ≠ ident := by
    intro he
    apply h2
    apply matrix_injective
    rw [map_pow, map_one, pow_two, hk, ← decode_mm, he, decode_ident]
  obtain ⟨c, hc⟩ := entry_mem (conjugating k)
  refine ⟨evenFieldAction c, ⟨c, rfl⟩, ?_⟩
  apply matrix_injective
  rw [map_mul, map_mul, hc, hk, matrix_first, ← decode_mm, ← decode_mm,
    (entry_checks k).2.2.2 hf hs]

private theorem central_form (m : Mat) (hm : m * decode first = decode first * m) :
    ∃ g h i : Q, m = decode (central g h i) := by
  have he (i j : Fin 3) := congrFun (congrFun hm i) j
  have h20 := he 2 0
  have h21 := he 2 1
  have h22 := he 2 2
  have h10 := he 1 0
  have h11 := he 1 1
  have h12 := he 1 2
  simp [Matrix.mul_apply, Fin.sum_univ_succ, decode, first, value] at h20 h21 h22 h10 h11 h12
  refine ⟨symbol (m 2 0), symbol (m 2 1), symbol (m 2 2), ?_⟩
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [decode, central, value_add, value_symbol]
  · rw [← h10, ← h20, ← h21]
    rw [add_add_add_comm, CharTwo.add_self_eq_zero, zero_add]
  · rw [← h11, ← h20, ← h22]
    rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  · exact h12.symm.trans h20.symm
  · exact h20.symm
  · exact h21.symm
  · exact h22.symm

private theorem central_mem (v : FieldGL) (hv : v * fieldGenerator = fieldGenerator * v)
    (hB : v * evenFieldAction generatorB * v⁻¹ ∈ evenFieldAction.range) :
    v ∈ evenFieldAction.range := by
  obtain ⟨g,h,i,hvmat⟩ := central_form (matrix v)
    (by simpa only [map_mul, matrix_first] using congrArg matrix hv)
  let c := central g h i
  have hn : fourth c ≠ NormalizerData.zero := by
    intro hz
    have hh : matrix (v ^ 4) = 0 := by
      rw [map_pow, hvmat, ← decode_fourth, hz, decode_zero]
    have hu : IsUnit (matrix (v ^ 4)) := (Group.isUnit (v ^ 4)).map matrix
    exact hu.ne_zero hh
  have hcheck := central_checks g h i hn
  have hi : matrix v⁻¹ = decode (eleventh c) := by
    have he : matrix v * decode (eleventh c) = 1 := by
      rw [hvmat, ← decode_mm, hcheck.1, decode_ident]
    calc matrix v⁻¹ = matrix v⁻¹ * (matrix v * decode (eleventh c)) := by rw [he, mul_one]
         _ = decode (eleventh c) := by rw [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]
  obtain ⟨b,hb⟩ := hB
  obtain ⟨k,hk⟩ := image_covered b
  have hm : mm (mm c second) (eleventh c) = entry k := by
    apply decode_injective
    rw [decode_mm, decode_mm, ← hvmat, ← matrix_second, ← hi, ← map_mul, ← map_mul, ← hb, hk]
  have hc : c = entry (centralWord g h i) :=
    hcheck.2.2 (by rw [hm]; exact (entry_checks k).2.1)
  obtain ⟨a,ha⟩ := entry_mem (centralWord g h i)
  exact ⟨a, matrix_injective (ha.trans ((congrArg decode hc).symm.trans hvmat.symm))⟩

/-- Both literal generator conjugates suffice to recognize a field-linear normalizer. -/
theorem mem_evenFieldAction_of_conjugating_generators (v : FieldGL)
    (hA : v * evenFieldAction generatorA * v⁻¹ ∈ evenFieldAction.range)
    (hB : v * evenFieldAction generatorB * v⁻¹ ∈ evenFieldAction.range) :
    v ∈ evenFieldAction.range := by
  let u := MulAut.conj v fieldGenerator
  have h4 : u ^ 4 = 1 := by rw [← map_pow, fieldGenerator_four, map_one]
  have h2 : u ^ 2 ≠ 1 := by
    intro h
    apply fieldGenerator_sq_ne_one
    apply (MulAut.conj v).injective
    simpa only [map_pow, map_one] using h
  obtain ⟨c,hc,hcv⟩ := order_four_conjugate u hA h4 h2
  have hd : c⁻¹ * v * fieldGenerator = fieldGenerator * (c⁻¹ * v) := by
    dsimp [u, MulAut.conj_apply] at hcv
    calc c⁻¹ * v * fieldGenerator = c⁻¹ * (v * fieldGenerator * v⁻¹ * c) * (c⁻¹ * v) := by group
         _ = fieldGenerator * (c⁻¹ * v) := by rw [← hcv]; group
  have hdB : (c⁻¹ * v) * evenFieldAction generatorB * (c⁻¹ * v)⁻¹ ∈ evenFieldAction.range := by
    have he : (c⁻¹ * v) * evenFieldAction generatorB * (c⁻¹ * v)⁻¹ =
        c⁻¹ * (v * evenFieldAction generatorB * v⁻¹) * c := by group
    rw [he]
    exact evenFieldAction.range.mul_mem (evenFieldAction.range.mul_mem (evenFieldAction.range.inv_mem hc) hB) hc
  have hh := evenFieldAction.range.mul_mem hc (central_mem (c⁻¹ * v) hd hdB)
  simpa only [← mul_assoc, mul_inv_cancel, one_mul] using hh
end Representation.Hexacode.SixDimensional
