module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.WordBounds
public import Theory.Representation.SU3.CubicDegree.SchurOuter.Models
public import Theory.Representation.SU3.CubicDegree.SchurOuter.GraphStable.SingleAdjoint
public import Theory.Representation.EndFieldFrobenius
-- Internal proof access to the unexposed numerical predicate, preserving its API.
import all CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.WordBounds

/-!
# Selecting the single adjoint word

For a word without natural labels, the twisted period counts give e*r=s
with r bounded by the number of adjoint factors. Even the weak degree bound
e*dim ≤ 18s forces exactly one adjoint factor and e=s, since 8^r>18r for r≥2.
Tensor-unit intertwiners then identify the actual unitary word with the
published adjoint model, with its Frobenius twist absorbed in the embedding.

The absence of natural labels and the displacement estimate are separate
obligations. This arithmetic does not assert either of them.
Source: Guralnick--Malle, Proposition 4.11 and §3.5.
-/

public section
set_option backward.isDefEq.respectTransparency false
open BenderSuzuki.MatrixGroups Representation Representation.FrobeniusTensor
open Representation.SL3.BinaryDefiningFactors
open Representation.SU3.CubicDegree.SchurOuter
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable

private theorem eighteen_mul_lt_eight_pow {r : ℕ} (hr : 2 ≤ r) :
    18 * r < 8 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => decide
  | succ r hr ih =>
    rw [pow_succ]
    nlinarith

/-- The period count and a weak degree bound force the precise adjoint count
and Schur degree; the proof includes s=2. -/
theorem single_adjoint_of_periodCounts (s e : ℕ) (he : 0 < e)
    (w : List Factor) (hp : MinimalDegree.PeriodCounts s e w)
    (hn : naturalCount w = 0) (hd : e * wordDegree w ≤ 18 * s) :
    e = s ∧ adjointCount w = 1 := by
  unfold MinimalDegree.PeriodCounts at hp
  rcases hp with ⟨r, hr, _, hc⟩ | ⟨r, hr, hp, hc⟩
  · omega
  · have hw : wordDegree w = 8 ^ adjointCount w := by
      rw [wordDegree_eq, hn, pow_zero, one_mul]
    have hpow : 8 ^ r ≤ wordDegree w := by
      rw [hw]
      exact Nat.pow_le_pow_right (by decide) hc
    have hrone : r = 1 := by
      by_contra h
      have hstrict := eighteen_mul_lt_eight_pow (r := r) (by omega)
      have hlt := Nat.mul_lt_mul_of_pos_left (hstrict.trans_le hpow) he
      nlinarith
    subst r
    have hes : e = s := by simpa using hp
    have hdegree : wordDegree w ≤ 18 := by nlinarith
    have ha : adjointCount w = 1 := by
      by_contra h
      have htwo : 2 ≤ adjointCount w := by omega
      have hlarge := Nat.pow_le_pow_right (n := 8) (by decide) htwo
      norm_num at hlarge
      rw [hw] at hdegree
      omega
    exact ⟨hes, ha⟩

variable {F K : Type*} [Field F] [Field K] [CharP K 2]

/-- Restriction of the concrete adjoint word agrees with the published model.
This comparison uses literal conjugation on trace-zero endomorphisms. -/
noncomputable def restrictedAdjointEquiv (J : HermitianForm 3 F) (ι : F →+* K) :
    Representation.Equiv
      ((factorRep ι .adjoint).comp (MinimalDegree.specialLinearInclusion J))
      (adjoint J ι) := by
  refine Representation.Equiv.mk (LinearEquiv.refl K _) ?_
  intro g
  ext X : 1
  apply Subtype.ext
  change Representation.SL3.BinaryDefiningFactors.natural ι
      (MinimalDegree.specialLinearInclusion J g) * (show AdjointSpace K from X).val *
    Representation.SL3.BinaryDefiningFactors.natural ι
      ((MinimalDegree.specialLinearInclusion J g)⁻¹) =
        (adjoint J ι g X : Module.End K (Fin 3 → K))
  rw [adjoint_apply, ← map_inv]
  rfl

/-- An actual single-adjoint unitary word, including all trivial factors,
is intertwined with the adjoint model at a possibly twisted embedding. -/
theorem word_single_adjoint (J : HermitianForm 3 F) (ι : F →+* K)
    (w : List Factor) (hn : naturalCount w = 0) (ha : adjointCount w = 1) :
    ∃ ι' : F →+* K, Nonempty ((MinimalDegree.word J ι w).Equiv (adjoint J ι')) := by
  obtain ⟨j, _, he⟩ :=
    Representation.SU3.CubicDegree.SchurOuter.GraphStable.wordRep_single_adjoint_uniform
      (F := F) (K := K) w hn ha
  obtain ⟨e⟩ := he ι
  exact ⟨(iterateFrobenius K 2 j).comp ι,
    ⟨(MinimalDegree.restrictEquiv (MinimalDegree.specialLinearInclusion J) e).trans
      (restrictedAdjointEquiv J _)⟩⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (J : HermitianForm 3 F)
  (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]

/-- The numerical selection constructs the requested Schur model, rather than
only its dimension or its label. Graph symmetry and displacement remain explicit. -/
theorem adjointSchurModel_of_word_bound {s : ℕ}
    (ι : F →+* Closure σ) (w : List Factor)
    (hmodel : Nonempty ((absoluteRep σ).Equiv (MinimalDegree.word J ι w)))
    (hp : MinimalDegree.PeriodCounts s (schurDegree 2 σ) w)
    (hn : naturalCount w = 0)
    (hd : schurDegree 2 σ * wordDegree w ≤ 18 * s) :
    AdjointSchurModel J σ s := by
  obtain ⟨he, ha⟩ := single_adjoint_of_periodCounts s (schurDegree 2 σ)
    (schurDegree_pos 2 σ) w hp hn hd
  obtain ⟨ι', ⟨e⟩⟩ := word_single_adjoint J ι w hn ha
  obtain ⟨f⟩ := hmodel
  exact ⟨he, ι', ⟨f.trans e⟩⟩

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable
