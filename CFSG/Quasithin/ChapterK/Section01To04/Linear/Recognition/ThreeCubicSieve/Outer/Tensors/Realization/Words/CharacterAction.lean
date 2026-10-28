module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Character
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions


/-!
# Literal graph and field actions on the SL₃ tensor word

Inverse transpose exchanges the natural and dual factors and fixes the trivial
and adjoint characters. GL₃ conjugation preserves both matrix traces, so this
calculation retains arbitrary inner-diagonal twists and central characters.
The actual character-separation theorem then excludes every pure graph twist
on a natural-containing repeated model.

For a field or graph-field half-turn, the character formula identifies the
transformed word with its rotation. Taking its first half gives the exact
pairing of factors, and a natural-containing full word has a natural-containing
half. These are word identities, not yet tensor-coordinate equivalences.

Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.8,
steps 2--5, manuscript pp.26--28; Aschbacher--Smith K.3.2, printed pp.454--456.
-/

@[expose] public section
noncomputable section
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open Representation.SL3.BinaryDefiningFactors
open Representation.SL3.BinaryDefiningFactors.TensorSimplicity.CharacterSeparation
open Matrix.PSL3.OuterSolvable
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Words

def graphFactor : Factor → Factor
  | .trivial => .trivial
  | .natural => .dual
  | .dual => .natural
  | .adjoint => .adjoint

@[simp] theorem graphFactor_graphFactor (a : Factor) : graphFactor (graphFactor a) = a := by
  cases a <;> rfl

theorem naturalCount_eq_zero_of_graph_fixed (w : List Factor)
    (hw : w.map graphFactor = w) : naturalCount w = 0 := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    have h := List.cons.inj hw
    cases a <;> simp_all [graphFactor, naturalCount]

variable {F K : Type*} [Field F] [Field K] [CharP K 2]

private theorem graphSL_val (g : SL(3,F)) :
    (graphSL F g).val = g⁻¹.val.transpose := by
  change Matrix.adjugate (g.val.transpose) = (Matrix.adjugate g.val).transpose
  exact (Matrix.adjugate_transpose g.val).symm

private theorem trace_linearConj (m : GL (Fin 3) F) (g : SL(3,F)) :
    Matrix.trace (linearConjSL F m g).val = Matrix.trace g.val := by
  have he := congrArg (fun x : GL (Fin 3) F => x.val) (linearConjSL_toGL F m g)
  change (linearConjSL F m g).val = m.val * g.val * (m⁻¹).val at he
  rw [he]
  exact Matrix.trace_units_conj m g.val

/-- GL conjugation preserves the actual tensor-word character, including its
central character. -/
theorem word_character_linearConj (ι : F →+* K) (w : List Factor)
    (m : GL (Fin 3) F) (g : SL(3,F)) :
    (wordRep ι w).character (linearConjSL F m g) = (wordRep ι w).character g := by
  rw [wordRep_character_polynomial, wordRep_character_polynomial,
    ← map_inv (linearConjSL F m), trace_linearConj, trace_linearConj]

/-- The graph automorphism exchanges the two endpoint factors. -/
theorem factor_character_graph (ι : F →+* K) (a : Factor) (g : SL(3,F)) :
    (factorRep ι a).character (graphSL F g) = (factorRep ι (graphFactor a)).character g := by
  have hg : Matrix.trace (graphSL F g).val = Matrix.trace g⁻¹.val := by
    rw [graphSL_val, Matrix.trace_transpose]
  have hgi : Matrix.trace (graphSL F g)⁻¹.val = Matrix.trace g.val := by
    rw [← map_inv, graphSL_val, inv_inv, Matrix.trace_transpose]
  cases a with
  | trivial => rfl
  | natural =>
    change (natural ι).character (graphSL F g) = (natural ι).dual.character g
    rw [char_dual, natural_character_trace, natural_character_trace, hg]
  | dual =>
    change (natural ι).dual.character (graphSL F g) = (natural ι).character g
    rw [char_dual, natural_character_trace, natural_character_trace, hgi]
  | adjoint =>
    rw [show graphFactor Factor.adjoint = .adjoint from rfl,
      adjoint_character, adjoint_character, hg, hgi, mul_comm]

/-- Graph action applies the label exchange at every literal Frobenius position. -/
theorem word_character_graph (ι : F →+* K) (w : List Factor) (g : SL(3,F)) :
    (wordRep ι w).character (graphSL F g) =
      (wordRep ι (w.map graphFactor)).character g := by
  induction w generalizing ι with
  | nil => rfl
  | cons a w ih =>
    rw [List.map_cons, wordRep_character_cons, wordRep_character_cons,
      factor_character_graph, ih]

/-- Invariance under any inner-diagonal graph twist excludes endpoint factors. -/
theorem naturalCount_eq_zero_of_graph_character_fixed [Finite F]
    (ι : F →+* K) (w : List Factor) (hcard : Nat.card F = 2 ^ w.length)
    (m : GL (Fin 3) F)
    (hfix : ∀ g, (wordRep ι w).character ((linearConjSL F m * graphSL F) g) =
      (wordRep ι w).character g) : naturalCount w = 0 := by
  apply naturalCount_eq_zero_of_graph_fixed
  apply word_eq_of_character_eq ι w.length hcard _ _ (List.length_map ..) rfl
  funext g
  rw [← word_character_graph, ← word_character_linearConj ι w m]
  exact hfix g

/-- Entrywise field transport changes the coefficient embedding literally. -/
theorem factor_character_field (ι : F →+* K) (a : Factor)
    (e : F ≃+* F) (g : SL(3,F)) :
    (factorRep ι a).character (Atlas.fieldEquivSL 3 e g) =
      (factorRep (ι.comp e.toRingHom) a).character g := by
  have ht (x : SL(3,F)) : Matrix.trace (Atlas.fieldEquivSL 3 e x).val =
      e (Matrix.trace x.val) := by
    change (∑ i, e (x.val i i)) = e (∑ i, x.val i i)
    simp only [map_sum]
  rw [factorRep_character_polynomial, factorRep_character_polynomial,
    ← map_inv (Atlas.fieldEquivSL 3 e), ht, ht]
  cases a <;> simp [factorPolynomial]

/-- Field action on each Frobenius factor agrees with coefficient transport. -/
theorem word_character_field (ι : F →+* K) (w : List Factor)
    (e : F ≃+* F) (g : SL(3,F)) :
    (wordRep ι w).character (Atlas.fieldEquivSL 3 e g) =
      (wordRep (ι.comp e.toRingHom) w).character g := by
  induction w generalizing ι with
  | nil => rfl
  | cons a w ih =>
    rw [wordRep_character_cons, wordRep_character_cons, factor_character_field, ih]
    rfl

variable [Finite F] [CharP F 2] [IsAlgClosed K]

/-- Defining-field Frobenius and coefficient Frobenius have the same character,
without asserting defining-field linearity of the original actor. -/
theorem word_character_frobenius (ι : F →+* K) (w : List Factor)
    (r : ℕ) (g : SL(3,F)) :
    (wordRep ι w).character (Atlas.fieldEquivSL 3 (iterateFrobeniusEquiv F 2 r) g) =
      (wordRep ι w).character g ^ (2 ^ r) := by
  rw [word_character_field]
  have he : ι.comp (iterateFrobeniusEquiv F 2 r).toRingHom =
      (iterateFrobeniusEquiv K 2 r).toRingHom.comp ι := by
    ext x
    exact map_pow ι x (2 ^ r)
  rw [he]
  exact wordRep_character_frobenius_embedding ι w r g


/-- The endpoint exchange induced by the optional graph factor. -/
def actFactor (ε : Bool) (a : Factor) : Factor := if ε then graphFactor a else a

/-- The actual field or graph-field action on the central cover. -/
def fieldGraph (r : ℕ) (ε : Bool) : MulAut SL(3,F) :=
  Atlas.fieldEquivSL 3 (iterateFrobeniusEquiv F 2 r) * (if ε then graphSL F else 1)

/-- The standard actions have the literal graph/Frobenius character formula;
the GL twist disappears by trace invariance. -/
theorem word_character_standard (ι : F →+* K) (w : List Factor)
    (m : GL (Fin 3) F) (r : ℕ) (ε : Bool) (g : SL(3,F)) :
    (wordRep ι w).character ((linearConjSL F m * fieldGraph (F := F) r ε) g) =
      (wordRep ι (w.map (actFactor ε))).character g ^ (2 ^ r) := by
  rw [MulAut.mul_apply, word_character_linearConj]
  cases ε with
  | false =>
    have hmap : w.map (actFactor false) = w := by
      induction w with
      | nil => rfl
      | cons a w ih => exact congrArg (List.cons a) ih
    change (wordRep ι w).character
      (Atlas.fieldEquivSL 3 (iterateFrobeniusEquiv F 2 r) g) = _
    rw [word_character_frobenius]
    exact congrArg (fun v => (wordRep ι v).character g ^ (2 ^ r)) hmap.symm
  | true =>
    change (wordRep ι w).character
      (Atlas.fieldEquivSL 3 (iterateFrobeniusEquiv F 2 r) (graphSL F g)) = _
    rw [word_character_frobenius, word_character_graph]
    rfl

/-- Invariance under a field half-turn identifies the graph-transformed word
with the literal rotation, including all trivial and adjoint positions. -/
theorem map_actFactor_eq_rotate_of_character_fixed
    (ι : F →+* K) (w : List Factor) (hcard : Nat.card F = 2 ^ w.length)
    (m : GL (Fin 3) F) (r : ℕ) (ε : Bool)
    (hfix : ∀ g, (wordRep ι w).character ((linearConjSL F m * fieldGraph (F := F) r ε) g) =
      (wordRep ι w).character g) :
    w.map (actFactor ε) = w.rotate r := by
  apply word_eq_of_character_eq ι w.length hcard _ _ (List.length_map ..)
    (List.length_rotate ..)
  funext g
  apply (iterateFrobeniusEquiv K 2 r).injective
  change (wordRep ι (w.map (actFactor ε))).character g ^ (2 ^ r) =
    (wordRep ι (w.rotate r)).character g ^ (2 ^ r)
  rw [wordRep_character_rotate ι w hcard r g, ← word_character_standard ι w m r ε g]
  exact hfix g

/-- A half-turn invariant word consists of a half word and its graph transform. -/
theorem drop_eq_map_take_of_character_fixed
    (ι : F →+* K) (w : List Factor) (hcard : Nat.card F = 2 ^ w.length)
    (m : GL (Fin 3) F) (r : ℕ) (hlen : w.length = 2 * r) (ε : Bool)
    (hfix : ∀ g, (wordRep ι w).character ((linearConjSL F m * fieldGraph (F := F) r ε) g) =
      (wordRep ι w).character g) :
    w.drop r = (w.take r).map (actFactor ε) := by
  have he := congrArg (List.take r)
    (map_actFactor_eq_rotate_of_character_fixed ι w hcard m r ε hfix)
  rw [← List.map_take] at he
  have hd : (w.drop r).length = r := by rw [List.length_drop, hlen]; omega
  have hr : (w.rotate r).take r = w.drop r := by
    rw [List.rotate_eq_drop_append_take (by omega)]
    nth_rw 1 [← hd]
    exact List.take_left
  exact (he.trans hr).symm

/-- Optional graph action preserves the number of endpoint factors. -/
theorem naturalCount_map_actFactor (ε : Bool) (w : List Factor) :
    naturalCount (w.map (actFactor ε)) = naturalCount w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases ε <;> cases a <;> simp_all [actFactor, graphFactor, naturalCount]

/-- A natural-containing paired word has a natural-containing first half. -/
theorem naturalCount_take_pos (w : List Factor) (r : ℕ) (ε : Bool)
    (hpair : w.drop r = (w.take r).map (actFactor ε))
    (hn : 0 < naturalCount w) : 0 < naturalCount (w.take r) := by
  have he : naturalCount w = 2 * naturalCount (w.take r) := by
    calc
      _ = naturalCount (w.take r ++ w.drop r) := by rw [List.take_append_drop]
      _ = naturalCount (w.take r) + naturalCount (w.drop r) := List.countP_append
      _ = _ := by rw [hpair, naturalCount_map_actFactor]; omega
  omega

end Words

variable {B : BinaryField} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) SL(3,B.Carrier) V} [IsIrreducible σ]

/-- The repeated word has the literal defining-field length. -/
theorem repeated_word_length (M : RepeatedModel B σ) :
    (List.replicate M.repetitions M.block).flatten.length = B.degree := by
  simp [List.length_flatten, M.block_length, M.field_degree, Nat.mul_comm]

/-- A natural-containing actual repeated model excludes every pure graph action,
including its inner-diagonal twists. -/
theorem LiftedInvolution.not_linear_graph {t : linearNormalizer σ}
    (L : LiftedInvolution B σ t) (ht : IsSchurLinear σ t)
    (M : RepeatedModel B σ) (hn : 0 < naturalCount M.block)
    (m : GL (Fin 3) B.Carrier) :
    L.automorphism ≠ linearConjSL B.Carrier m * graphSL B.Carrier := by
  intro he
  have hz := Words.naturalCount_eq_zero_of_graph_character_fixed
    M.coefficientEmbedding (List.replicate M.repetitions M.block).flatten
    (by rw [repeated_word_length M]; exact B.card_eq) m (by
      intro g
      rw [← he]
      exact L.word_character_fixed ht M g)
  rw [naturalCount_repeat] at hz
  exact (Nat.ne_of_gt (Nat.mul_pos M.repetitions_pos hn)) hz

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization
