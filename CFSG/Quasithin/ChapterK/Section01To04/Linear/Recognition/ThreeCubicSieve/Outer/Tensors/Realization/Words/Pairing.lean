module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization.Words.Inputs
public import Theory.Representation.SL3.BinaryDefiningFactors.SmallPatterns
public import Theory.Representation.Quotient

/-!
# Tensor coordinates for paired SL₃ half words

Split the actual recursive word tensor at the half-degree boundary using the
append equivalence, which retains the accumulated coefficient Frobenius.
Padding short words by trivial factors proves that both half representations
are irreducible. The literal graph/field character formula, including the GL₃
conjugation, and irreducible trace rigidity then give an actual equivalence
from the second half to the first half pulled back by the given automorphism.
Finally one basis of the first half transports both factors to the same finite
coordinate space. An endpoint factor gives dimension at least three.

The conclusion concerns the action of SL₃ on the original Schur scalar
extension. No descent of the half representation or square-one hypothesis on
the automorphism is needed.

Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.8,
steps 2--5, manuscript pp.26--28; Aschbacher--Smith K.3.2, printed pp.454--456.
-/

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Representation Representation.BinaryOffender
open Representation.BinaryOffender.SchurNormalizer
open Representation.SL3.BinaryDefiningFactors
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open scoped MatrixGroups TensorProduct

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization
namespace Words

variable {F K : Type*} [Field F] [Field K] [CharP K 2]

private theorem trivial_tail_equiv (ι : F →+* K) (n : ℕ) :
    Nonempty ((wordRep ι (List.replicate n .trivial)).Equiv
      (Representation.trivial K SL(3,F) K)) := by
  induction n generalizing ι with
  | zero => exact ⟨Representation.Equiv.refl _⟩
  | succ n ih =>
    obtain ⟨e⟩ := ih ((frobenius K 2).comp ι)
    exact ⟨(Representation.TensorProduct.lid K _).trans e⟩

omit [CharP K 2] in
private theorem irreducible_of_equivalence
    {G U W : Type*} [Group G] [AddCommGroup U] [Module K U]
    [AddCommGroup W] [Module K W]
    {ρ : Representation K G U} {τ : Representation K G W}
    (e : ρ.Equiv τ) [IsIrreducible ρ] : IsIrreducible τ := by
  exact (RepEquiv.irreducible_euqiv
    (RepEquiv.mk e.toLinearEquiv e.isIntertwining')).mp inferInstance

private theorem short_word_irreducible [Finite F] (ι : F →+* K) (n : ℕ)
    (hcard : Nat.card F = 2 ^ n) (w : List Factor) (hw : w.length ≤ n) :
    IsIrreducible (wordRep ι w) := by
  let v := w ++ List.replicate (n - w.length) Factor.trivial
  have hv : v.length = n := by simp [v]; omega
  let : IsIrreducible (wordRep ι v) := wordRep_isIrreducible ι n hcard v hv
  obtain ⟨e⟩ := wordRep_append_equiv ι w (List.replicate (n - w.length) .trivial)
  obtain ⟨f⟩ := trivial_tail_equiv ((iterateFrobenius K 2 w.length).comp ι)
    (n - w.length)
  exact irreducible_of_equivalence
    (e.trans ((tensorRightEquiv f).trans (Representation.TensorProduct.rid K _)))

variable [Finite F] [CharP F 2] [IsAlgClosed K]

private theorem standard_half_equiv (ι : F →+* K) (n : ℕ)
    (hcard : Nat.card F = 2 ^ n) (u : List Factor) (hu : u.length ≤ n)
    (r : ℕ) (ε : Bool) (m : GL (Fin 3) F) :
    Nonempty ((wordRep ((iterateFrobenius K 2 r).comp ι)
      (u.map (actFactor ε))).Equiv
      ((wordRep ι u).comp
        (Matrix.PSL3.OuterSolvable.linearConjSL F m * fieldGraph (F := F) r ε).toMonoidHom)) := by
  let α := Matrix.PSL3.OuterSolvable.linearConjSL F m * fieldGraph (F := F) r ε
  let : IsIrreducible (wordRep ι u) := short_word_irreducible ι n hcard u hu
  let : IsIrreducible ((wordRep ι u).comp α.toMonoidHom) :=
    (irreducible_comp_surjective_iff α.toMonoidHom α.surjective _).mpr inferInstance
  let : IsIrreducible (wordRep ((iterateFrobenius K 2 r).comp ι)
      (u.map (actFactor ε))) :=
    short_word_irreducible _ n hcard _ (by simpa using hu)
  apply (character_eq_iff_equiv_of_irreducible _ _).mp
  funext g
  change (wordRep ((iterateFrobeniusEquiv K 2 r).toRingHom.comp ι)
    (u.map (actFactor ε))).character g = (wordRep ι u).character (α g)
  exact (wordRep_character_frobenius_embedding ι (u.map (actFactor ε)) r g).trans
    (word_character_standard ι u m r ε g).symm

end Words

variable (B : BinaryField) {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL(3,B.Carrier) V) [IsIrreducible σ]

/-- An explicitly paired repeated word has genuine tensor-square coordinates
for the literal field or graph-field half-turn, retaining its GL₃ twist. -/
theorem half_turn_word_pairing : HalfTurnWordPairing B σ := by
  intro M α H
  dsimp only
  intro hn hp
  let w := (List.replicate M.repetitions M.block).flatten
  let u := w.take H.halfDegree
  have hlen : w.length = 2 * H.halfDegree := (repeated_word_length M).trans H.degree_eq
  have hu : u.length = H.halfDegree := by
    dsimp [u]
    rw [List.length_take, Nat.min_eq_left (by omega)]
  have hule : u.length ≤ B.degree := by rw [hu, H.degree_eq]; omega
  have hsplit := wordRep_append_equiv M.coefficientEmbedding u (w.drop H.halfDegree)
  have hfull : u ++ w.drop H.halfDegree = w := List.take_append_drop _ _
  rw [hfull, hu, show w.drop H.halfDegree = u.map (Words.actFactor H.withGraph) from hp]
    at hsplit
  obtain ⟨esplit⟩ := hsplit
  obtain ⟨ehalf⟩ := Words.standard_half_equiv M.coefficientEmbedding B.degree B.card_eq
    u hule H.halfDegree H.withGraph H.matrix
  rw [← H.automorphism_eq] at ehalf
  let b := (Module.finBasis (SplittingField σ) (WordSpace (SplittingField σ) u)).equivFun
  let τ : Representation (SplittingField σ) SL(3,B.Carrier)
      (Fin (Module.finrank (SplittingField σ) (WordSpace (SplittingField σ) u)) →
        SplittingField σ) := b.conjRingEquiv.toMonoidHom.comp (wordRep M.coefficientEmbedding u)
  let eb : (wordRep M.coefficientEmbedding u).Equiv τ := Representation.Equiv.mk b (by
    intro g
    ext v
    simp [τ, LinearEquiv.conjRingEquiv])
  let ebα : Representation.Equiv ((wordRep M.coefficientEmbedding u).comp α.toMonoidHom)
      (τ.comp α.toMonoidHom) := Representation.Equiv.mk b (fun g => eb.isIntertwining' (α g))
  let e : (extendScalars (SplittingField σ) σ.endFieldRep).Equiv
      (τ.tprod (τ.comp α.toMonoidHom)) := M.equiv.trans (esplit.trans
    ((tensorRightEquiv ehalf).trans (tensorEquiv eb ebα)))
  refine ⟨{
    size := Module.finrank (SplittingField σ) (WordSpace (SplittingField σ) u)
    three_le := ?_
    half := τ
    equiv := e.toLinearEquiv
    component_action := ?_ }⟩
  · rw [finrank_wordSpace, wordDegree_eq]
    have hn' : 1 ≤ naturalCount u := hn
    have h3 : 3 ≤ 3 ^ naturalCount u := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 3) hn'
    exact h3.trans (Nat.le_mul_of_pos_right _ (by positivity))
  · intro g v
    exact LinearMap.congr_fun (e.isIntertwining' g) v

end CFSG.Quasithin.ChapterK.Linear.Recognition.ThreeCubicSieve.Outer.Tensors.Realization
