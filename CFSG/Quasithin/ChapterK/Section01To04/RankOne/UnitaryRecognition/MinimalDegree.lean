module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.Preparation
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.WordBounds
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.Descent
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.Catalogue
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.FrobeniusCounts
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Minimal-degree binary unitary recognition

Every nontrivial irreducible binary representation of SU₃(2ˢ), for s ≥ 2,
of dimension at most 6*s has actual natural-module coordinates. Over an
algebraic closure of its endomorphism field, the unitary catalogue supplies
a tensor-word model. Twisted Frobenius counts and the dimension tower force
one natural or dual factor and Schur degree 2*s. Descent retains its coefficient
embedding and duality label and constructs the required binary intertwiner
for the original Hermitian form.

The source application uses the literal surjective SU pullback without
assuming it faithful. Recognition proves the covering map injective and
constructs the original layer's `NaturalModel`, including in odd exponent
when SU has a nontrivial center. Its sole additional source premise is the
numerical upper bound; the independent cubic-degree argument supplies that
premise in the final K.3.3 assembly. The earlier conditional APIs are retained.

Source: Aschbacher--Smith K.3.3, printed p.456; GLS III, §2.8;
Guralnick--Malle, Theorem 4.10 and Table 7.
-/

public section
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree
open BenderSuzuki.MatrixGroups Representation
open Representation.SL3.BinaryDefiningFactors
open scoped MonoidAlgebra TensorProduct

variable {F V K : Type*} [Field F] [Field K] [CharP K 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (J : HermitianForm 3 F)
  (σ : Representation (ZMod 2) J.specialSubgroup V) [IsIrreducible σ]
  [Algebra (Module.End (ZMod 2)[J.specialSubgroup] σ.asModule) K]

/-- A genuine Schur-word equivalence gives the exact binary dimension formula. -/
theorem finrank_eq_schurDegree_mul_wordDegree (ι : F →+* K) (w : List Factor)
    (hmodel : Nonempty ((extendScalars K σ.endFieldRep).Equiv (word J ι w))) :
    Module.finrank (ZMod 2) V = schurDegree 2 σ * wordDegree w := by
  obtain ⟨e⟩ := hmodel
  rw [finrank_eq_schurDegree_mul 2 σ K, e.toLinearEquiv.finrank_eq,
    finrank_wordSpace]

/-- The degree argument selects actual coefficient-twisted natural or dual
models, retaining all the information needed for binary descent. -/
theorem schur_word_single_factor {s : ℕ} (ι : F →+* K) (w : List Factor)
    (hmodel : Nonempty ((extendScalars K σ.endFieldRep).Equiv (word J ι w)))
    (hperiod : PeriodCounts s (schurDegree 2 σ) w)
    (hd : Module.finrank (ZMod 2) V ≤ 6 * s) :
    schurDegree 2 σ = 2 * s ∧
      ∃ ι' : F →+* K,
        Nonempty ((extendScalars K σ.endFieldRep).Equiv (natural J ι')) ∨
        Nonempty ((extendScalars K σ.endFieldRep).Equiv (natural J ι').dual) := by
  have hdim := finrank_eq_schurDegree_mul_wordDegree J σ ι w hmodel
  obtain ⟨he, hn, ha⟩ := single_factor_of_periodCounts s (schurDegree 2 σ)
    (schurDegree_pos 2 σ) w hperiod (hdim ▸ hd)
  obtain ⟨e⟩ := hmodel
  obtain ⟨ι', hn | hn⟩ := word_single_factor J ι w hn ha
  · exact ⟨he, ι', Or.inl (hn.map (fun f => e.trans f))⟩
  · exact ⟨he, ι', Or.inr (hn.map (fun f => e.trans f))⟩


variable [Finite F] [Algebra (ZMod 2) F]

/-- Given the actual Schur-word model and its twisted-period counts, the
minimal binary degree forces a natural intertwiner, with no faithfulness
assumption. The catalogue and period assertions remain explicit inputs. -/
theorem isNatural_of_schur_word {s : ℕ}
    (hcard : Nat.card F = (2 ^ s) ^ 2) (ι : F →+* K) (w : List Factor)
    (hmodel : Nonempty ((extendScalars K σ.endFieldRep).Equiv (word J ι w)))
    (hperiod : PeriodCounts s (schurDegree 2 σ) w)
    (hd : Module.finrank (ZMod 2) V ≤ 6 * s) : IsNatural J σ := by
  obtain ⟨he, hm⟩ := schur_word_single_factor J σ ι w hmodel hperiod hd
  exact isNatural_of_absolute_natural J σ hcard he hm

/-- Every nontrivial irreducible binary SU₃(2ˢ) action of degree at most 6*s
is natural. The actual Schur field, word model, and twisted Frobenius counts
are constructed here; faithfulness and an ambient offender are not assumed.
The output supplies both a group automorphism and binary coordinates
intertwining the literal column action. -/
theorem isNatural_of_finrank_le {s : ℕ} (hs : 2 ≤ s)
    (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s)) (hne : ∃ g, σ g ≠ 1)
    (hd : Module.finrank (ZMod 2) V ≤ 6 * s) : IsNatural J σ := by
  let E := Module.End (ZMod 2)[J.specialSubgroup] σ.asModule
  let K' := AlgebraicClosure E
  let : CharP E 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) E).injective 2
  let : CharP K' 2 := charP_of_injective_algebraMap (algebraMap E K').injective 2
  let : Algebra (ZMod 2) K' := ZMod.algebra K' 2
  let ι : F →+* K' := (IsAlgClosed.lift (R := ZMod 2) (S := F) (M := K')).toRingHom
  obtain ⟨w, hw, hmodel⟩ := exists_schur_word_model J σ s hs ι hcard hconj
  have hp := periodCounts_of_schur_word J σ hs hconj ι w hw
    (word_isIrreducible J s hs hcard hconj ι)
    (fun u v hu hv he => (word_equiv_iff J s hs hcard hconj ι u v hu hv).mp he)
    hmodel hne
  exact isNatural_of_schur_word J σ hcard ι w hmodel hp hd

section Source
variable {G : Type*} [Group G] {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- Apply the conditional classifier to the literal source pullback. The
period producer receives the proved nontriviality of that pullback. The
additional word-model and period premises still have to be discharged by
unitary tensor classification; the numerical premise has an independent
source producer. No injectivity of the SU cover is assumed. -/
theorem source_naturalModel_of_schur_word
    (h : SourceHypotheses ρ L) (π : J.specialSubgroup →* L) (hπ : Function.Surjective π)
    {s : ℕ} (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hd : Module.finrank (ZMod 2) V ≤ 6 * s) :
    let τ : Representation (ZMod 2) J.specialSubgroup V := (ρ.comp L.subtype).comp π
    letI := pullback_irreducible J h π hπ
    ∀ (K' : Type*) [Field K'] [CharP K' 2]
      [Algebra (Module.End (ZMod 2)[J.specialSubgroup] τ.asModule) K']
      (ι : F →+* K') (w : List Factor),
      Nonempty ((extendScalars K' τ.endFieldRep).Equiv (word J ι w)) →
      ((∃ g, τ g ≠ 1) → PeriodCounts s (schurDegree 2 τ) w) →
      Nonempty (NaturalModel ρ L J) ∧ Function.Injective π := by
  dsimp only
  let τ : Representation (ZMod 2) J.specialSubgroup V := (ρ.comp L.subtype).comp π
  let := pullback_irreducible J h π hπ
  intro K' _ _ _ ι w hmodel hperiod
  have hnat := isNatural_of_schur_word J τ hcard ι w hmodel
    (hperiod (pullback_nontrivial J h π hπ)) hd
  exact ⟨naturalModel_of_pullback J π hπ hnat, cover_injective_of_natural J π hnat⟩

/-- The minimal-degree classifier applied to the actual source covering map.
Surjective pullback supplies irreducibility and nontriviality. The resulting
natural intertwiner proves injectivity of the full SU cover and gives the
original layer's coordinates. The numerical premise is the independent
cubic-degree input to K.3.3; no word, period, or faithfulness premise remains. -/
theorem source_naturalModel_of_finrank_le
    (h : SourceHypotheses ρ L) (π : J.specialSubgroup →* L) (hπ : Function.Surjective π)
    {s : ℕ} (hs : 2 ≤ s) (hcard : Nat.card F = (2 ^ s) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ s))
    (hd : Module.finrank (ZMod 2) V ≤ 6 * s) :
    Nonempty (NaturalModel ρ L J) ∧ Function.Injective π := by
  let τ : Representation (ZMod 2) J.specialSubgroup V := (ρ.comp L.subtype).comp π
  let : IsIrreducible τ := pullback_irreducible J h π hπ
  have hnat := isNatural_of_finrank_le J τ hs hcard hconj
    (pullback_nontrivial J h π hπ) hd
  exact ⟨naturalModel_of_pullback J π hπ hnat, cover_injective_of_natural J π hnat⟩

end Source
end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.MinimalDegree
