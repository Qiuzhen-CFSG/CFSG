module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Words.Inputs
public import Theory.Representation.SL3.BinaryDefiningFactors.SmallPatterns

/-!
# Adjoint half-word coordinates for field-containing outer actions

A half-degree field or graph-field action pairs the Frobenius positions in the
actual repeated word. Each half is irreducible: append trivial factors to field
length and use the checked word catalogue. The literal character formula and
irreducible trace equivalence identify the second half with the first half
precomposed with the lifted automorphism, including its GL₃ twist. Reassociation
and one basis then give the required tensor-square coordinates on the original
Schur extension. A positive adjoint count puts an adjoint factor in each half,
so the half dimension is at least eight.

This constructs component coordinates only; the checked absolute Schur
comparison recovers the outer operator as interchange in `OuterModels`.
Source: GM, Classification of 2F-modules II, Proposition 4.8 steps 2,4,5,
manuscript pp.26–28; Aschbacher–Smith K.3.2, printed pp.454–456.
-/

public noncomputable section
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open scoped MatrixGroups TensorProduct
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords.OuterModels
open Realization

variable {F K : Type*} [Field F] [Field K] [CharP K 2]

private theorem trivial_word_equiv (ι : F →+* K) (n : ℕ) :
    Nonempty ((wordRep ι (List.replicate n Factor.trivial)).Equiv
      (Representation.trivial K SL(3,F) K)) := by
  induction n generalizing ι with
  | zero => exact ⟨Representation.Equiv.refl _⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih ((frobenius K 2).comp ι)
    exact ⟨(Representation.TensorProduct.lid K _).trans e⟩

private theorem padded_word_equiv (ι : F →+* K) (w : List Factor) (n : ℕ) :
    Nonempty ((wordRep ι (w ++ List.replicate n Factor.trivial)).Equiv
      (wordRep ι w)) := by
  obtain ⟨e⟩ := wordRep_append_equiv ι w (List.replicate n Factor.trivial)
  obtain ⟨e'⟩ := trivial_word_equiv ((iterateFrobenius K 2 w.length).comp ι) n
  exact ⟨e.trans ((tensorRightEquiv e').trans (Representation.TensorProduct.rid K _))⟩

private theorem short_word_irreducible [Finite F] (ι : F →+* K)
    (n : ℕ) (hc : Nat.card F = 2 ^ n) (w : List Factor) (hw : w.length ≤ n) :
    IsIrreducible (wordRep ι w) := by
  obtain ⟨e⟩ := padded_word_equiv ι w (n - w.length)
  apply (RepEquiv.irreducible_euqiv (RepEquiv.ofRepresentationEquiv e)).mp
  exact wordRep_isIrreducible ι n hc _ (by simp; omega)

private theorem adjointCount_map (ε : Bool) (w : List Factor) :
    adjointCount (w.map (Words.actFactor ε)) = adjointCount w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases ε <;> cases a <;> simp_all [Words.actFactor, Words.graphFactor, adjointCount]

private theorem half_adjointCount_pos (w : List Factor) (d : ℕ) (ε : Bool)
    (hp : w.drop d = (w.take d).map (Words.actFactor ε))
    (ha : 0 < adjointCount w) : 0 < adjointCount (w.take d) := by
  have he : adjointCount w = 2 * adjointCount (w.take d) := by
    calc
      _ = adjointCount (w.take d ++ w.drop d) := by rw [List.take_append_drop]
      _ = adjointCount (w.take d) + adjointCount (w.drop d) := List.count_append
      _ = _ := by rw [hp, adjointCount_map]; omega
  omega

variable {B : BinaryField} {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {σ : Representation (ZMod 2) SL(3,B.Carrier) V} [IsIrreducible σ]

/-- A paired half word containing an adjoint factor supplies actual component
coordinates for the literal field or graph-field automorphism, including its
GL₃ twist. No action on the defining field is assumed for the original actor. -/
theorem pairedCoordinates_of_halfTurn (M : RepeatedModel B σ)
    {α : MulAut SL(3,B.Carrier)} (H : HalfTurnForm B α)
    (ha : 0 < adjointCount M.block)
    (hp : (List.replicate M.repetitions M.block).flatten.drop H.halfDegree =
      ((List.replicate M.repetitions M.block).flatten.take H.halfDegree).map
        (Words.actFactor H.withGraph)) :
    Nonempty (PairedTensorCoordinates B σ α) := by
  let K := SplittingField σ
  let w := (List.replicate M.repetitions M.block).flatten
  let u := w.take H.halfDegree
  let v := w.drop H.halfDegree
  have hw : w.length = B.degree := repeated_word_length M
  have hd := H.degree_eq
  have hu : u.length = H.halfDegree := by simp only [u, List.length_take]; omega
  have hv : v.length = H.halfDegree := by simp only [v, List.length_drop]; omega
  let ι := M.coefficientEmbedding
  let ψ := (iterateFrobenius K 2 u.length).comp ι
  let R := wordRep ι u
  let S := wordRep ψ v
  let : IsIrreducible R := short_word_irreducible ι B.degree B.card_eq u (by omega)
  let : IsIrreducible S := short_word_irreducible ψ B.degree B.card_eq v (by omega)
  let : IsIrreducible (R.comp α.toMonoidHom) :=
    (irreducible_comp_surjective_iff α.toMonoidHom α.surjective R).mpr inferInstance
  let Rα : Representation K SL(3,B.Carrier) (WordSpace K u) := R.comp α.toMonoidHom
  have hχ : S.character = Rα.character := by
    funext g
    change (wordRep ((iterateFrobenius K 2 u.length).comp ι) v).character g =
      (wordRep ι u).character (α g)
    rw [hu]
    change (wordRep ((iterateFrobeniusEquiv K 2 H.halfDegree).toRingHom.comp ι) v).character g = _
    calc
      _ = (wordRep ι v).character g ^ (2 ^ H.halfDegree) :=
        wordRep_character_frobenius_embedding ι v H.halfDegree g
      _ = _ := by
        have he := Words.word_character_standard ι u H.matrix H.halfDegree H.withGraph g
        have heα := congrArg (fun β : MulAut SL(3,B.Carrier) =>
          (wordRep ι u).character (β g)) H.automorphism_eq
        exact (congrArg (fun z => (wordRep ι z).character g ^ (2 ^ H.halfDegree)) hp).trans
          (heα.trans he).symm
  obtain ⟨e₂⟩ := (character_eq_iff_equiv_of_irreducible S (R.comp α.toMonoidHom)).mp hχ
  obtain ⟨e₀⟩ := wordRep_append_equiv ι u v
  have castEquiv {a b : List Factor} (hab : a = b) :
      (wordRep ι a).Equiv (wordRep ι b) := by
    subst b
    exact Representation.Equiv.refl _
  let e₁ : (wordRep ι w).Equiv (R.tprod S) :=
    (castEquiv (List.take_append_drop H.halfDegree w).symm).trans e₀
  let e := (Module.finBasis K (WordSpace K u)).equivFun
  let τ : Representation K SL(3,B.Carrier) (Fin (Module.finrank K (WordSpace K u)) → K) :=
    e.conjRingEquiv.toMonoidHom.comp R
  let E : R.Equiv τ := {
    toLinearEquiv := e
    isIntertwining' := by
      intro g
      apply LinearMap.ext
      intro x
      change e (R g x) = e (R g (e.symm (e x)))
      rw [e.symm_apply_apply] }
  let Eα : Representation.Equiv (R.comp α.toMonoidHom) (τ.comp α.toMonoidHom) := {
    toLinearEquiv := e
    isIntertwining' := fun g => E.isIntertwining' (α g) }
  let Q := M.equiv.trans (e₁.trans
    ((tensorEquiv (Representation.Equiv.refl R) e₂).trans (tensorEquiv E Eα)))
  refine ⟨{
    size := Module.finrank K (WordSpace K u)
    three_le := ?_
    half := τ
    equiv := Q.toLinearEquiv
    component_action := ?_ }⟩
  · have hau : 0 < adjointCount u := half_adjointCount_pos w H.halfDegree
      H.withGraph hp (by rw [adjointCount_repeat]; exact Nat.mul_pos M.repetitions_pos ha)
    rw [finrank_wordSpace, wordDegree_eq]
    have h8 : 8 ≤ 8 ^ adjointCount u := Nat.le_pow hau
    have h3 : 0 < 3 ^ naturalCount u := by positivity
    nlinarith
  · intro g x
    exact DFunLike.congr_fun (Q.isIntertwining' g) x

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.AdjointWords.OuterModels
