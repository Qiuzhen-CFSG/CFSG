module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer.MatrixRigidity
import Mathlib.Tactic.Group

/-!
# Selecting and conjugating an actual outer graph actor

The matrix rigidity results are transported through the given equivalence with
the binary adjoint representation. An involution with an inner-diagonal matrix
form belongs to the literal component action image. Consequently the outer
hypothesis selects a graph actor, and symmetric ternary congruence normalizes
its matrix to the Gram matrix used in the fixed-space calculation.

`adjointConj` is an actual change of basis on trace-zero endomorphisms. The
conjugation formulas also retain the standard matrix forms of every other actor.
No faithful action of the SL₃ cover is assumed or substituted for its image.

Source: Guralnick–Malle, Classification of 2F-modules II, Proposition 4.8,
step 3A, author manuscript p.27; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer
open Matrix
variable {F : Type*} [Field F]

abbrev matrix (x : AdjointSpace F) : Mat (F := F) := LinearMap.toMatrix' x.val

lemma matrix_injective : Function.Injective (matrix (F := F)) :=
  LinearMap.toMatrix'.injective.comp Subtype.val_injective

lemma matrix_trace (x : AdjointSpace F) : (matrix x).trace = 0 := by
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
  exact x.property

lemma matrix_surjective (X : Mat (F := F)) (hX : X.trace = 0) :
    ∃ x : AdjointSpace F, matrix x = X := by
  refine ⟨⟨X.toLin', ?_⟩, LinearMap.toMatrix'_toLin' X⟩
  change LinearMap.trace F _ X.toLin' = 0
  rwa [Matrix.trace_toLin'_eq]

/-- Change of basis on the actual trace-zero endomorphism space. -/
def adjointConj (g : GL (Fin 3) F) : AdjointSpace F ≃ₗ[F] AdjointSpace F where
  toFun x := ⟨(GeneralLinearGroup.toLin g).toLinearEquiv.conj x.val, by
    change LinearMap.trace F _ ((GeneralLinearGroup.toLin g).toLinearEquiv.conj x.val) = 0
    rw [LinearMap.trace_conj']
    exact x.property⟩
  invFun x := ⟨(GeneralLinearGroup.toLin g).toLinearEquiv.symm.conj x.val, by
    change LinearMap.trace F _ ((GeneralLinearGroup.toLin g).toLinearEquiv.symm.conj x.val) = 0
    rw [LinearMap.trace_conj']
    exact x.property⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by apply Subtype.ext; simp
  map_add' x y := Subtype.ext (map_add _ _ _)
  map_smul' c x := Subtype.ext (map_smul _ _ _)

lemma matrix_adjointConj (g : GL (Fin 3) F) (x : AdjointSpace F) :
    matrix (adjointConj g x) = inner g (matrix x) := by
  change LinearMap.toMatrix' (g.val.toLin' ∘ₗ x.val ∘ₗ (g⁻¹).val.toLin') = _
  simp only [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', inner, matrix, mul_assoc]

def transposeGL (g : GL (Fin 3) F) : GL (Fin 3) F where
  val := g.val.transpose
  inv := (g⁻¹).val.transpose
  val_inv := by rw [← Matrix.transpose_mul, g.inv_mul, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, g.mul_inv, Matrix.transpose_one]

lemma transposeGL_inv (g : GL (Fin 3) F) : transposeGL g⁻¹ = (transposeGL g)⁻¹ := by
  apply Units.ext
  rfl

lemma transpose_inner (g : GL (Fin 3) F) (X : Mat (F := F)) :
    (inner g X).transpose = inner (transposeGL g)⁻¹ X.transpose := by
  change (g.val * X * (g⁻¹).val).transpose =
    (g⁻¹).val.transpose * X.transpose * g.val.transpose
  simp only [Matrix.transpose_mul, mul_assoc]

lemma inner_conj (C g : GL (Fin 3) F) (X : Mat (F := F)) :
    inner C (inner g X) = inner (C * g * C⁻¹) (inner C X) := by
  simp only [← inner_mul]
  congr 1
  group

lemma graph_conj (C g : GL (Fin 3) F) (X : Mat (F := F)) :
    inner C (graph g X) = graph (C * g * transposeGL C) (inner C X) := by
  rw [graph, graph, transpose_inner]
  simp only [← inner_mul]
  congr 1
  group

lemma gram_sq (F : Type*) [Field F] : gram F * gram F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gram, Matrix.mul_apply, Fin.sum_univ_three]

lemma graph_conj_gram (C g : GL (Fin 3) F)
    (hC : C.val * g.val * C.val.transpose = gram F) (X : Mat (F := F)) :
    inner C (graph g X) = gram F * (inner C X).transpose * gram F := by
  rw [graph_conj]
  let k := C * g * transposeGL C
  have hk : k.val = gram F := hC
  have hki : (k⁻¹).val = gram F := by
    have h := congrArg (fun Y => Y * gram F) k.inv_mul
    simpa only [hk, Matrix.mul_assoc, gram_sq, Matrix.mul_one, Matrix.one_mul] using h
  change k.val * (inner C X).transpose * (k⁻¹).val = _
  rw [hk, hki]

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V)

lemma matrix_binaryRep (s : SL(3,B.Carrier)) (x : AdjointSpace B.Carrier) :
    matrix (binaryRep B s x) = inner (SpecialLinearGroup.toGL s) (matrix x) := by
  change LinearMap.toMatrix' (natural (RingHom.id B.Carrier) s ∘ₗ x.val ∘ₗ
    natural (RingHom.id B.Carrier) s⁻¹) = _
  have hn (a : SL(3,B.Carrier)) : LinearMap.toMatrix' (natural (RingHom.id B.Carrier) a) = a.val := by
    change LinearMap.toMatrix' (a.val.map (RingHom.id B.Carrier)).toLin' = _
    rw [LinearMap.toMatrix'_toLin']
    rfl
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp, hn, hn]
  change s.val * (matrix x * (s⁻¹).val) = s.val * matrix x * (s⁻¹).val
  exact (mul_assoc _ _ _).symm

lemma involution_apply (t : linearNormalizer σ) (ht : t ^ 2 = 1) (v : V) :
    t.val.val (t.val.val v) = v := by
  have h := congrArg (fun a : linearNormalizer σ => a.val.val v) ht
  simpa only [pow_two, Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply,
    Subgroup.coe_one, Units.val_one, Module.End.one_apply] using h

/-- On the actual adjoint representation, an inner-diagonal involution is in
the actual component action image. No faithfulness on the SL₃ cover is used. -/
theorem inner_mem_actionImage (e : σ.Equiv (binaryRep B))
    (t : linearNormalizer σ) (ht : t ^ 2 = 1) (g : GL (Fin 3) B.Carrier)
    (hg : ∀ v : V, matrix (e (t.val.val v)) = inner g (matrix (e v))) :
    t.val ∈ actionImage σ := by
  have hinv : ∀ X : Mat (F := B.Carrier), X.trace = 0 → inner g (inner g X) = X := by
    intro X hX
    obtain ⟨x, rfl⟩ := matrix_surjective X hX
    obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective x
    change inner g (inner g (matrix (e v))) = matrix (e v)
    rw [← hg, ← hg, involution_apply B σ t ht]
  obtain ⟨s, hs⟩ := det_one_representative g hinv
  refine ⟨s, ?_⟩
  apply Units.ext
  apply LinearMap.ext
  intro v
  apply e.toLinearEquiv.injective
  apply matrix_injective
  have he := LinearMap.congr_fun (e.isIntertwining' s) v
  change e (σ s v) = binaryRep B s (e v) at he
  change matrix (e (σ s v)) = matrix (e (t.val.val v))
  rw [he, matrix_binaryRep, hs, hg]

/-- The outer condition selects an actual graph involution. The inner case
is excluded using the determinant correction above, including degree two. -/
theorem exists_graph_actor (e : σ.Equiv (binaryRep B))
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (houter : ¬ A.map (linearNormalizer σ).subtype ≤ actionImage σ)
    (hforms : ∀ t ∈ A, HasStandardAction B σ e t) :
    ∃ (t : A) (g : GL (Fin 3) B.Carrier),
      (∀ v : V, matrix (e (t.val.val.val v)) = graph g (matrix (e v))) ∧
      ∃ C : GL (Fin 3) B.Carrier, C.val * g.val * C.val.transpose = gram B.Carrier := by
  have hex : ∃ t ∈ A, t.val ∉ actionImage σ := by
    by_contra hn
    apply houter
    rintro _ ⟨t, ht, rfl⟩
    by_contra hx
    exact hn ⟨t, ht, hx⟩
  obtain ⟨t, ht, hout⟩ := hex
  let : IsElementaryAbelian 2 A := hA.2
  have ht2 : t ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian t ht
  obtain ⟨g, hi | hg⟩ := hforms t ht
  · exact (hout (inner_mem_actionImage B σ e t ht2 g hi)).elim
  · refine ⟨⟨t, ht⟩, g, hg, graph_gram g ?_⟩
    intro X hX
    obtain ⟨x, rfl⟩ := matrix_surjective X hX
    obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective x
    change graph g (graph g (matrix (e v))) = matrix (e v)
    change ∀ v : V, matrix (e (t.val.val v)) = graph g (matrix (e v)) at hg
    rw [← hg, ← hg, involution_apply B σ t ht2]

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Adjoint.GraphCentralizer
