module
public import Theory.Character.InductionClassFormula
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.CharacterOrder.NormalizerInduction.CharacterConstruction.InertiaCharacters.Construction

/-!
# Class-intersection calculations for the five inertia characters

The original binary coordinate and S4 actor define the integer-valued inducing
characters. The generic class-intersection formula evaluates their actual
inductions. The finite calculation below retains both possible assignments of the
two local order-four classes. Character norm integrality will distinguish them. The ambient normalizer fusion
and centralizer orders remain separate group-theoretic inputs.

Source: Z. Janko, *A characterization of the Mathieu simple groups, I*,
J. Algebra 9 (1968), Section 6, pp.10–11.
-/
open Subgroup
open scoped BigOperators
noncomputable section
attribute [local instance] Fintype.ofFinite Classical.propDecidable
namespace Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
open LocalModelDichotomy CaseII.Distribution
local instance : Fintype TwistedModel := Fintype.ofEquiv
  (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm

/-- The integer-valued character in the original marked semidirect coordinates. -/
@[expose] public def normalizerInertiaModelValue (j : Fin 5) (t : TwistedModel) : ℤ :=
  binaryParitySign t.left * SymmetricFourCharacters.table (normalizerInertiaCharacterIndex j)
    (SymmetricFourClasses.classIndex t.right)

/-- The local-to-normalizer fusion assignment, allowing the last two order-four classes to swap. -/
@[expose] public def normalizerInertiaFusionIndex (swap : Bool) : Fin 17 → Fin 9 :=
  ![5, 0, 0, 0, 6, 6, 7, 1, 1, 1, 3, 4, 8, 4,
    if swap then 4 else 3, if swap then 3 else 4, 2]

/-- Proposed centralizer orders for the nine fixed-vector representatives; numerical data only. -/
@[expose] public def normalizerFixedCentralizerOrders : Fin 9 → ℕ :=
  ![384, 12, 8, 32, 16, 5760, 32, 36, 8]

/-- The integer sums of the inducing characters on the nine class intersections. -/
@[expose] public def normalizerInertiaExpectedClassSum (swap : Bool) : Fin 5 → Fin 9 → ℤ :=
  if swap then ![![-3, 0, 48, -36, 24, 3, 12, 0, -48],
    ![-3, 0, -48, 12, 24, 3, -36, 0, 48],
    ![-2, 32, 0, 24, -48, 2, 24, -32, 0],
    ![-1, -32, 48, 36, -24, 1, -12, 32, -48],
    ![-1, -32, -48, -12, -24, 1, 36, 32, 48]]
  else ![![-3, 0, 48, 12, -24, 3, 12, 0, -48],
    ![-3, 0, -48, -36, 72, 3, -36, 0, 48],
    ![-2, 32, 0, 24, -48, 2, 24, -32, 0],
    ![-1, -32, 48, -12, 24, 1, -12, 32, -48],
    ![-1, -32, -48, 36, -72, 1, 36, 32, 48]]

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
    (k : TwistedModel ≃* D.centralizer) (L : LocalAnalysisData D k)

/-- The finite model value is the actual inertia character under the marked isomorphism. -/
public theorem normalizerInertiaCharacter_model (j : Fin 5) (t : TwistedModel) :
    normalizerInertiaCharacter D k L j (normalizerInertiaEquiv D k L t) =
      (normalizerInertiaModelValue j t : ℂ) := by
  rw [normalizerInertiaCharacter_apply]
  exact (Int.cast_mul _ _).symm

include D k L in
private theorem modelValue_class (j : Fin 5) (t : TwistedModel) :
    normalizerInertiaModelValue j t = normalizerInertiaModelValue j (localRepresentative (localClass t)) := by
  have hc : IsClassFunction (normalizerInertiaCharacter D k L j) := by
    obtain ⟨n, ρ, _, he⟩ := normalizerInertiaCharacter_irreducible D k L j
    rw [he]
    exact fun x g => Representation.char_conj ρ x g
  obtain ⟨x, hx⟩ := isConj_iff.mp
    ((normalizerInertiaEquiv D k L).toMonoidHom.map_isConj (localClass_conjugate t))
  have he := (hc _ x).symm.trans (congrArg (normalizerInertiaCharacter D k L j) hx)
  simp only [MulEquiv.coe_toMonoidHom, normalizerInertiaCharacter_model] at he
  exact_mod_cast he

/-- The class sum uses conjugacy internal to the actual normalizer. -/
@[expose] public def normalizerInertiaClassSum (j : Fin 5) (r : Fin 9) : ℤ := by
  classical
  letI : Fintype TwistedModel := Fintype.ofEquiv
    (BinaryFour × SymmetricFour) SemidirectProduct.equivProd.symm
  exact ∑ t : TwistedModel, if IsConj (normalizerCentralizer D k t)
    (normalizerFixedRepresentative D k r) then normalizerInertiaModelValue j t else 0

/-- Actual induced values reduce to integer class sums and actual normalizer centralizers. -/
public theorem normalizerInducedCharacter_fixed_class_sum (j : Fin 5) (r : Fin 9) :
    normalizerInducedCharacter D k L j (normalizerFixedRepresentative D k r) =
      (Nat.card (centralizer ({normalizerFixedRepresentative D k r} :
        Set (normalizer (CaseII.E D k : Set G)))) : ℂ) / 384 *
          (normalizerInertiaClassSum D k j r : ℂ) := by
  rw [normalizerInducedCharacter,
    inducedClassFunction_eq_centralizer_mul_sum_equiv _ (normalizerInertiaEquiv D k L),
    normalizerInertia_card D k L]
  congr 1
  rw [normalizerInertiaClassSum, Int.cast_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [normalizerInertiaEquiv_coe]
  by_cases h : IsConj (normalizerCentralizer D k t) (normalizerFixedRepresentative D k r)
  · simp only [if_pos h, normalizerInertiaCharacter_model]
  · simp only [if_neg h, Int.cast_zero]

include L in
/-- Evaluate the weighted intersection sums for either possible order-four assignment. -/
public theorem normalizerInertiaClassSum_of_fusion (swap : Bool)
    (hf : ∀ i : Fin 17, IsConj (normalizerCentralizer D k (localRepresentative i))
      (normalizerFixedRepresentative D k (normalizerInertiaFusionIndex swap i)))
    (j : Fin 5) (r : Fin 9) :
    normalizerInertiaClassSum D k j r = normalizerInertiaExpectedClassSum swap j r := by
  classical
  have hconj (t : TwistedModel) :
      IsConj (normalizerCentralizer D k t) (normalizerFixedRepresentative D k r) ↔
        normalizerInertiaFusionIndex swap (localClass t) = r := by
    have ht := ((normalizerCentralizer D k).map_isConj (localClass_conjugate t)).trans (hf (localClass t))
    constructor
    · intro hr
      exact normalizerFixedRepresentative_distinct D k L
        (ConjClasses.mk_eq_mk_iff_isConj.mpr (ht.symm.trans hr))
    · intro hr
      rwa [hr] at ht
  let f : Fin 17 → ℤ := fun i => if normalizerInertiaFusionIndex swap i = r then
    normalizerInertiaModelValue j (localRepresentative i) else 0
  have he : normalizerInertiaClassSum D k j r = ∑ t : TwistedModel, f (localClass t) := by
    unfold normalizerInertiaClassSum
    apply Finset.sum_congr rfl
    intro t _
    change (if IsConj (normalizerCentralizer D k t) (normalizerFixedRepresentative D k r)
      then normalizerInertiaModelValue j t else 0) = _
    simp only [hconj, f]
    split_ifs
    · exact modelValue_class D k L j t
    · rfl
  rw [he]
  have hs := Fintype.sum_fiberwise' localClass f
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Nat.card_eq_fintype_card, localClass_card] at hs
  rw [← hs]
  have hfinite : ∀ (swap : Bool) (j : Fin 5) (r : Fin 9),
      (∑ i : Fin 17, (![1, 1, 8, 6, 12, 24, 32, 32, 32, 32, 12, 24, 48, 24, 24, 24, 48] i : ℤ) *
        (if normalizerInertiaFusionIndex swap i = r then
          normalizerInertiaModelValue j (localRepresentative i) else 0)) =
      normalizerInertiaExpectedClassSum swap j r := by decide +kernel
  exact hfinite swap j r

end Theory.GroupTheory.HeldM22A10.M22Identification.CharacterOrder
