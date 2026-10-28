module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer.Reduction
import Mathlib.Tactic.Group

/-!
# Involutory isometry lifts of normalized adjoint actors

Multiply each graph-form actor by the marked Gram-transpose actor to obtain an
inner operator in the same elementary group. The checked determinant correction
supplies an involutory matrix representing it. Two involutory matrices with the
same trace-zero conjugation operator differ by a scalar whose square is one;
in characteristic two that scalar is one. This proves that the selected lifts
commute exactly and preserve the literal Gram matrix, removing all projective
ambiguity without an intertwining assertion about the original SL₃ marking.

`exists_lifted_actors` is consumed by `GraphCentralizer.root_placement`. Its
conclusion retains the exact normalized linear equivalence and the graph bit.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.8,
step 3A, author manuscript p.27; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

@[expose] public noncomputable section

open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer.RootPlacement
open Matrix
variable {F : Type*} [Field F] [CharP F 2]

private lemma sq_one (a : F) (ha : a ^ 2 = 1) : a = 1 := by
  rcases sq_eq_one_iff.mp ha with h | h
  · exact h
  · simpa only [CharTwo.neg_eq] using h

private lemma inner_involution_injective (g h : GL (Fin 3) F)
    (hg : g ^ 2 = 1) (hh : h ^ 2 = 1)
    (he : ∀ X : Mat (F := F), X.trace = 0 → inner g X = inner h X) : g = h := by
  obtain ⟨c, hc⟩ := scalar_of_inner_eq_id (h⁻¹ * g) (by
    intro X hX
    rw [inner_mul, he X hX, ← inner_mul, inv_mul_cancel]
    simp [inner])
  have hgh : g.val = c • h.val := by
    have heq := congrArg (fun M => h.val * M) hc
    change h.val * ((h⁻¹).val * g.val) = _ at heq
    simpa only [← Matrix.mul_assoc, h.mul_inv, Matrix.one_mul, Matrix.scalar_apply,
      ← Matrix.smul_eq_mul_diagonal] using heq
  have hg2 : g.val * g.val = 1 := by simpa [pow_two] using congrArg Units.val hg
  have hh2 : h.val * h.val = 1 := by simpa [pow_two] using congrArg Units.val hh
  rw [hgh, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hh2] at hg2
  have hc2 : c ^ 2 = 1 := by
    simpa [pow_two] using congrArg (fun M : Mat (F := F) => M 0 0) hg2
  apply Units.ext
  simpa [sq_one c hc2] using hgh

omit [CharP F 2] in
private lemma involution_inv (g : GL (Fin 3) F) (hg : g ^ 2 = 1) : g⁻¹ = g := by
  apply inv_eq_of_mul_eq_one_left
  simpa only [pow_two] using hg

private lemma inner_involutions_commute (g h : GL (Fin 3) F)
    (hg : g ^ 2 = 1) (hh : h ^ 2 = 1)
    (he : ∀ X : Mat (F := F), X.trace = 0 →
      inner g (inner h X) = inner h (inner g X)) : Commute g h := by
  have hconj : g * h * g⁻¹ = h := by
    refine inner_involution_injective _ _ ?_ hh ?_
    · simp only [pow_two] at hh ⊢
      calc
        g * h * g⁻¹ * (g * h * g⁻¹) = g * (h * h) * g⁻¹ := by group
        _ = 1 := by rw [hh]; group
    · intro X hX
      rw [inner_mul, inner_mul, involution_inv g hg, he]
      · rw [← inner_mul g g, ← pow_two, hg]
        simp [inner]
      · simpa [inner, Matrix.trace_mul_cycle] using hX
  exact mul_inv_eq_iff_eq_mul.mp hconj

/-- The literal Gram matrix, as an invertible matrix. -/
private def gramGL : GL (Fin 3) F := ⟨gram F, gram F, gram_sq F, gram_sq F⟩

omit [CharP F 2] in
private lemma gramGL_inv : (gramGL (F := F))⁻¹ = gramGL := by apply Units.ext; rfl

omit [CharP F 2] in
private lemma gramGL_square : (gramGL (F := F)) * gramGL = 1 := by
  apply Units.ext
  exact gram_sq F

omit [CharP F 2] in
private lemma gram_transpose : (gram F).transpose = gram F := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [CharP F 2] in
private lemma graph_gram_square (X : Mat (F := F)) :
    graph gramGL (graph gramGL X) = X := by
  change gram F * (gram F * X.transpose * gram F).transpose * gram F = X
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, gram_transpose]
  calc
    _ = (gram F * gram F) * X * (gram F * gram F) := by simp only [mul_assoc]
    _ = X := by rw [gram_sq, Matrix.one_mul, Matrix.mul_one]

omit [CharP F 2] in
private lemma graph_gram_inner (g : GL (Fin 3) F) (X : Mat (F := F)) :
    graph gramGL (inner g X) =
      inner (gramGL * (transposeGL g)⁻¹ * gramGL) (graph gramGL X) := by
  rw [graph, transpose_inner, graph]
  simp only [← inner_mul]
  congr 1
  rw [mul_assoc _ gramGL gramGL, gramGL_square, mul_one]

omit [CharP F 2] in
private lemma transposeGL_square (g : GL (Fin 3) F) (hg : g ^ 2 = 1) :
    (transposeGL g) ^ 2 = 1 := by
  have hm : g.val * g.val = 1 := by simpa [pow_two] using congrArg Units.val hg
  rw [pow_two]
  apply Units.ext
  change g.val.transpose * g.val.transpose = 1
  rw [← Matrix.transpose_mul, hm, Matrix.transpose_one]

private lemma inner_involution_isometry (g : GL (Fin 3) F) (hg : g ^ 2 = 1)
    (hc : ∀ X : Mat (F := F), X.trace = 0 →
      inner g (graph gramGL X) = graph gramGL (inner g X)) :
    g.val * gram F * g.val.transpose = gram F := by
  let d := gramGL * (transposeGL g)⁻¹ * gramGL
  have hd : d ^ 2 = 1 := by
    have ht := transposeGL_square g hg
    rw [pow_two] at ht
    dsimp [d]
    rw [pow_two]
    calc
      _ = gramGL * (transposeGL g)⁻¹ * (gramGL * gramGL) *
          (transposeGL g)⁻¹ * gramGL := by simp only [mul_assoc]
      _ = gramGL * ((transposeGL g)⁻¹ * (transposeGL g)⁻¹) * gramGL := by
        rw [gramGL_square, mul_one, mul_assoc gramGL]
      _ = 1 := by
        rw [← _root_.mul_inv_rev, ht, inv_one, mul_one, gramGL_square]
  have he : g = d := inner_involution_injective g d hg hd (by
    intro X hX
    have htr : (graph gramGL X).trace = 0 := by
      simpa [graph, inner, Matrix.trace_mul_cycle] using hX
    have hh := hc (graph gramGL X) htr
    rw [graph_gram_square, graph_gram_inner, graph_gram_square] at hh
    exact hh)
  have he' : g * gramGL * transposeGL g = gramGL := by
    calc
      _ = (gramGL * (transposeGL g)⁻¹ * gramGL) * gramGL * transposeGL g := by
        exact congrArg (fun k => k * gramGL * transposeGL g) he
      _ = gramGL := by
        rw [mul_assoc _ gramGL gramGL, gramGL_square, mul_one]
        simp only [mul_assoc, inv_mul_cancel, mul_one]
  exact congrArg Units.val he'

omit [CharP F 2] in
private lemma graph_mul_gram (g : GL (Fin 3) F) (X : Mat (F := F)) :
    graph g (graph gramGL X) = inner (g * gramGL) X := by
  change inner g (gram F * X.transpose * gram F).transpose = inner (g * gramGL) X
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
    gram_transpose]
  rw [← Matrix.mul_assoc (gram F) X (gram F)]
  change inner g (inner gramGL X) = inner (g * gramGL) X
  exact (inner_mul g gramGL X).symm

omit [CharP F 2] in
private lemma inner_mul_gram_graph (g : GL (Fin 3) F) (X : Mat (F := F)) :
    inner (g * gramGL) (graph gramGL X) = graph g X := by
  rw [inner_mul]
  change inner g (inner gramGL (inner gramGL X.transpose)) = _
  rw [← inner_mul gramGL gramGL, gramGL_square]
  simp [inner, graph]

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (N : NormalizedGraphAction B σ A)

include hA

private lemma lift_inner_actor (t : A) (g : GL (Fin 3) B.Carrier)
    (hi : ∀ v : V, matrix (N.equiv (t.val.val.val v)) = inner g (matrix (N.equiv v))) :
    ∃ s : GL (Fin 3) B.Carrier, s ^ 2 = 1 ∧
      ∀ X : Mat (F := B.Carrier), inner s X = inner g X := by
  let : IsElementaryAbelian 2 A := hA.2
  have ht2 : t.val ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t.val t.property
  obtain ⟨s, hs2, hs⟩ := det_one_involution_representative g (by
    intro X hX
    obtain ⟨x, rfl⟩ := matrix_surjective X hX
    obtain ⟨v, rfl⟩ := N.equiv.surjective x
    rw [← hi, ← hi, involution_apply B σ t.val ht2])
  refine ⟨SpecialLinearGroup.toGL s, ?_, hs⟩
  rw [← map_pow, hs2, map_one]

private lemma actor_decomposition (b : A)
    (hb : ∀ v : V, matrix (N.equiv (b.val.val.val v)) = graph gramGL (matrix (N.equiv v)))
    (t : A) :
    ∃ (u : A) (s : GL (Fin 3) B.Carrier) (bit : ZMod 2), s ^ 2 = 1 ∧
      (∀ v : V, matrix (N.equiv (u.val.val.val v)) = inner s (matrix (N.equiv v))) ∧
      ∀ v : V, matrix (N.equiv (t.val.val.val v)) =
        inner s (if bit = 0 then matrix (N.equiv v) else graph gramGL (matrix (N.equiv v))) := by
  obtain ⟨g, hi | hg⟩ := N.standard t
  · obtain ⟨s, hs2, hs⟩ := lift_inner_actor B σ A hA N t g hi
    refine ⟨t, s, 0, hs2, ?_, ?_⟩
    · intro v
      rw [hs]
      exact hi v
    · intro v
      simp only [ite_true, hs]
      exact hi v
  · have hi : ∀ v : V, matrix (N.equiv ((t*b).val.val.val v)) =
        inner (g * gramGL) (matrix (N.equiv v)) := by
      intro v
      change matrix (N.equiv (t.val.val.val (b.val.val.val v))) = _
      rw [hg, hb, graph_mul_gram]
    obtain ⟨s, hs2, hs⟩ := lift_inner_actor B σ A hA N (t*b) (g*gramGL) hi
    refine ⟨t*b, s, 1, hs2, ?_, ?_⟩
    · intro v
      rw [hs]
      exact hi v
    · intro v
      simp only [one_ne_zero, ite_false, hs, inner_mul_gram_graph]
      exact hg v

open scoped IsMulCommutative

private lemma actor_commute (t u : A) (v : V) :
    t.val.val.val (u.val.val.val v) = u.val.val.val (t.val.val.val v) := by
  let : IsElementaryAbelian 2 A := hA.2
  exact congrArg (fun k : A => k.val.val.val v) (mul_comm t u)

private lemma actor_lifts_commute (t u : A) (g h : GL (Fin 3) B.Carrier)
    (hg : g ^ 2 = 1) (hh : h ^ 2 = 1)
    (ht : ∀ v : V, matrix (N.equiv (t.val.val.val v)) = inner g (matrix (N.equiv v)))
    (hu : ∀ v : V, matrix (N.equiv (u.val.val.val v)) = inner h (matrix (N.equiv v))) :
    Commute g h := by
  apply inner_involutions_commute g h hg hh
  intro X hX
  obtain ⟨x, rfl⟩ := matrix_surjective X hX
  obtain ⟨v, rfl⟩ := N.equiv.surjective x
  rw [← hu, ← ht, actor_commute B σ A hA, hu, ht]

private lemma actor_lift_isometry (b t : A) (g : GL (Fin 3) B.Carrier) (hg : g ^ 2 = 1)
    (hb : ∀ v : V, matrix (N.equiv (b.val.val.val v)) = graph gramGL (matrix (N.equiv v)))
    (ht : ∀ v : V, matrix (N.equiv (t.val.val.val v)) = inner g (matrix (N.equiv v))) :
    g.val * gram B.Carrier * g.val.transpose = gram B.Carrier := by
  apply inner_involution_isometry g hg
  intro X hX
  obtain ⟨x, rfl⟩ := matrix_surjective X hX
  obtain ⟨v, rfl⟩ := N.equiv.surjective x
  rw [← hb, ← ht, actor_commute B σ A hA, hb, ht]

/-- Every actor is an actual involutory Gram isometry, optionally followed by
the marked graph operator; the selected isometries commute as matrices. -/
theorem exists_lifted_actors :
    ∃ (s : A → GL (Fin 3) B.Carrier) (bit : A → ZMod 2),
      (∀ t, s t ^ 2 = 1) ∧
      (∀ t, (s t).val * gram B.Carrier * (s t).val.transpose = gram B.Carrier) ∧
      (∀ t u, Commute (s t) (s u)) ∧
      ∀ (t : A) (v : V), matrix (N.equiv (t.val.val.val v)) =
        inner (s t) (if bit t = 0 then matrix (N.equiv v)
          else gram B.Carrier * (matrix (N.equiv v)).transpose * gram B.Carrier) := by
  classical
  obtain ⟨b, hb⟩ := N.graph_mem
  change ∀ v : V, matrix (N.equiv (b.val.val.val v)) =
    graph gramGL (matrix (N.equiv v)) at hb
  choose u s bit hs hu ht using actor_decomposition B σ A hA N b hb
  refine ⟨s, bit, hs, ?_, ?_, ht⟩
  · intro t
    exact actor_lift_isometry B σ A hA N b (u t) (s t) (hs t) hb (hu t)
  · intro t v
    exact actor_lifts_commute B σ A hA N (u t) (u v) (s t) (s v)
      (hs t) (hs v) (hu t) (hu v)

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer.RootPlacement
