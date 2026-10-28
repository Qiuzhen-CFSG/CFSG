module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RationalDescent.BruhatParameters.RestrictedCells.NormalizerWords
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.ZeroAndMiddle.Geometry
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.WeylOpposition.Matrix
public import Theory.AlgebraicGroup.ClosedSubgroup.Conjugation

/-!
# Torus normalization and opposition for the literal F4 words

The checked simple-coroot commutation formulas show that every simple Weyl
word normalizes the actual split torus. The existing normalizer-word
factorization then proves this for every middle factor in concrete Bruhat
coverage. The sixth power of the Coxeter word is the checked opposition
matrix, so conjugation carries each literal root curve to its negative.

The matrix comparison for opposition adapts the private calculation in
`RationalDescent.BruhatParameters.RestrictedCells.OppositeCollection`, without
changing that module's public boundary. These results feed candidate maximality
and the conjugacy of the two prescribed candidates in the parent module.

Sources: GLS3, 1.12.1 and the root-word calculation underlying 1.11.2
(`refs/KGroup/GLS3/Chapter1.tex`); Steinberg, Lemmas 5–6 and Theorem 4′
(`refs/KGroup/GLS3/Chapter2St1.tex`).
-/

public noncomputable section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open Theory.AlgebraicGroup.F4Chevalley
open RootPairing.IntegralGeckConstruction ReeF4.WordRelations
open ReeF4.BinaryDegree.ExceptionalTensor
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels.Maximality
open RationalDescent.BruhatParameters RationalDescent.BruhatParameters.RestrictedCells
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]
local instance : InvolutiveNeg Root := typeF4RootPairing.indexNeg

omit [CharP F 2] in
private lemma corootProduct_mem (t : Fin 4 → Fˣ) : corootProduct t ∈ splitTorus (k := F) := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact algebraicCorootElement_mem_splitTorus i (t i)

private lemma simpleN_inv (i : Fin 4) :
    (algebraicNElement (F := F) (typeF4SimpleRootIndex i) 1)⁻¹ =
      algebraicNElement (typeF4SimpleRootIndex i) 1 := by
  simp only [algebraicNElement, mul_inv_rev, ZeroAndMiddle.root_inv, CharTwo.neg_eq]
  group

private lemma simpleN_mem_normalizer (i : Fin 4) :
    algebraicNElement (F := F) (typeF4SimpleRootIndex i) 1 ∈ (splitTorus (k := F)).normalizer := by
  let n := algebraicNElement (F := F) (typeF4SimpleRootIndex i) 1
  have hconj (x : Variety.Point (Carrier (k := F))) (hx : x ∈ splitTorus (k := F)) :
      n⁻¹ * x * n ∈ splitTorus (k := F) := by
    obtain ⟨t, rfl⟩ := exists_corootProduct_of_mem_splitTorus hx
    let H := (splitTorus (k := F)).toSubgroup.comap (MulAut.conj n⁻¹).toMonoidHom
    suffices h : corootProduct t ∈ H by
      have h' : n⁻¹ * corootProduct t * (n⁻¹)⁻¹ ∈ splitTorus (k := F) := h
      simpa only [inv_inv] using h'
    apply H.list_prod_mem
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    change n⁻¹ * algebraicCorootElement (typeF4SimpleRootIndex j) (t j) * (n⁻¹)⁻¹ ∈ splitTorus
    rw [inv_inv, mul_assoc, ZeroAndMiddle.coroot_n_commute i j (t j)]
    change n⁻¹ * (n * _) ∈ splitTorus
    rw [inv_mul_cancel_left]
    exact (splitTorus (k := F)).toSubgroup.mul_mem
      (algebraicCorootElement_mem_splitTorus j (t j))
      (algebraicCorootElement_mem_splitTorus i _)
  have hni : n⁻¹ = n := simpleN_inv i
  change n ∈ Subgroup.normalizer ((splitTorus (k := F)).toSubgroup : Set (Variety.Point (Carrier (k := F))))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  change x ∈ splitTorus (k := F) ↔ n * x * n⁻¹ ∈ splitTorus (k := F)
  constructor
  · intro hx
    simpa only [hni] using hconj x hx
  · intro hx
    have h := hconj _ hx
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h

private lemma weylWord_mem_normalizer (l : List (Fin 4)) :
    weylWord (F := F) l ∈ (splitTorus (k := F)).normalizer := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact simpleN_mem_normalizer i

/-- Every literal rank-one word normalizes the prescribed split torus. -/
lemma normalizerWords_le_normalizer :
    DenseParameters.normalizerWords (k := F) ≤ (splitTorus (k := F)).normalizer.toSubgroup := by
  intro n hn
  obtain ⟨t, l, rfl⟩ := normalizerWords_eq_corootProduct_mul_weylWord hn
  exact (splitTorus (k := F)).normalizer.toSubgroup.mul_mem
    ((splitTorus (k := F)).toSubgroup.le_normalizer (corootProduct_mem t))
    (weylWord_mem_normalizer l)

/-- The actual longest-element word in the concrete carrier. -/
def opposition : Variety.Point (Carrier (k := F)) := weylWord [0, 1, 2, 3] ^ 6

/-- The longest-element word normalizes the same literal torus. -/
lemma opposition_mem_normalizer : opposition (F := F) ∈ (splitTorus (k := F)).normalizer :=
  (splitTorus (k := F)).normalizer.toSubgroup.pow_mem (weylWord_mem_normalizer _) _

omit [CharP F 2] in
private lemma literalMatrix_weylWord (l : List (Fin 4)) :
    literalMatrix (weylWord (F := F) l) = titsUnit (l.map typeF4RootPairing_baseEquiv) := by
  induction l with
  | nil => simp [weylWord]
  | cons i l ih =>
    change literalMatrix (algebraicNElement (typeF4SimpleRootIndex i) 1 * weylWord l) = _
    rw [map_mul, literalMatrix_simpleN, ih]
    simp only [List.map_cons, titsUnit_cons, titsUnit_nil, mul_one]

private lemma literalMatrix_opposition :
    literalMatrix (opposition (F := F)) = ReeF4.WordRelations.Faithfulness.Adjoint.omegaUnit := by
  rw [opposition, map_pow, literalMatrix_weylWord]
  have h (l : List typeF4RootPairing_base.support) :
      titsUnit (S := F) l = ReeF4.WordRelations.Faithfulness.Adjoint.titsWordUnit l := by
    apply Units.ext
    rw [ReeF4.WordRelations.Faithfulness.Adjoint.titsWordUnit_val]
    rfl
  rw [h]
  exact ReeF4.LocalBlockInput.PairNormalization.WeylOpposition.coxeterWord_pow_six_eq_omega

/-- Opposition carries each original labelled root curve to its negative. -/
lemma opposition_conj_root (r : Root) (a : F) :
    opposition * algebraicRootElement r a * opposition⁻¹ = algebraicRootElement (-r) a := by
  apply literalMatrix_injective
  simp only [map_mul, map_inv, literalMatrix_opposition, literalMatrix_algebraicRoot]
  exact ReeF4.LocalBlockInput.PairNormalization.WeylOpposition.omega_conj_rootCurve r a

/-- The concrete opposition word is an involution in characteristic two. -/
lemma opposition_inv : (opposition (F := F))⁻¹ = opposition := by
  apply literalMatrix_injective
  rw [map_inv, literalMatrix_opposition]
  exact Units.ext rfl

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.OppositeBorels.Maximality
