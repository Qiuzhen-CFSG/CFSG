module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.CubicDegree.SchurOuter.GraphStable
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.Catalogue
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree.FrobeniusCounts
public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds
public import Theory.Representation.SU3.CubicDegree.SchurOuter.Reduction

/-!
# The source Schur-linear outer branch

Every Schur-linear elementary cubic actor of fixed codimension at most twice
its rank lies in the literal SU₃ action image. The concrete tensor catalogue
and twisted Frobenius counts discharge graph-stable adjoint selection. The
adjoint fixed-space estimates then exclude outer actors: the bound `3s`
handles `s > 2`, and the stronger bound eight closes the endpoint `s = 2`.
The odd-order Schur centralizer removes the remaining scalar ambiguity.

The source pullback is irreducible and has exactly the covering kernel, so
this containment applies to its full linear normalizer without assuming
faithfulness. Combining with the non-Schur-linear branch leaves an actual
inner cubic actor or the desired upper degree bound. The independent
inner-actor estimate and final degree assembly belong to CubicDegree.

Source: Aschbacher--Smith K.3.3, printed p.456 under p.451 hypotheses;
Guralnick--Malle II, Proposition 4.11, internal pp.31--32.
-/

public section
open BenderSuzuki.MatrixGroups Representation Representation.BinaryOffender
open Representation.SU3.CubicDegree.SchurOuter
open Subgroup
namespace CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree
variable {F V : Type*} [Field F] [Finite F] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (J : HermitianForm 3 F) {s : ℕ} (hs : 2 ≤ s)
  (hcard : Nat.card F = (2 ^ s) ^ 2) (hconj : ∀ x, J.conj x = x ^ (2 ^ s))

namespace SchurOuter
open Representation.FrobeniusTensor Representation.SL3.BinaryDefiningFactors
variable (σ : Representation (ZMod 2) J.specialSubgroup V) [σ.IsIrreducible]
  (hk : σ.ker ≤ center J.specialSubgroup)

include hs hcard hconj hk

/-- The actual Schur extension has a graph-stable adjoint model whenever a
Schur-linear cubic actor contains an outer operator and satisfies the offender
inequality. The tensor catalogue and exact twisted period are proved inputs;
no absolute irreducibility of the original binary action is assumed. -/
theorem graphStableReduction : GraphStableReduction J σ s := by
  let : CharP F 2 := by
    let := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (p := 2) (f := s * 2) (by
      rw [← Nat.card_eq_fintype_card, hcard, pow_mul])
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let : Algebra (ZMod 2) (Closure σ) := ZMod.algebra (Closure σ) 2
  let ι : F →+* Closure σ :=
    (IsAlgClosed.lift (R := ZMod 2) (S := F) (M := Closure σ)).toRingHom
  have hirr := MinimalDegree.word_isIrreducible J s hs hcard hconj (K := Closure σ)
  have hunique : ∀ (ι : F →+* Closure σ) (u v : List Factor),
      u.length = s → v.length = s →
      Nonempty ((MinimalDegree.word J ι u).Equiv (MinimalDegree.word J ι v)) → u = v :=
    fun ι u v hu hv he =>
      (MinimalDegree.word_equiv_iff J s hs hcard hconj ι u v hu hv).mp he
  obtain ⟨w, hw, he⟩ := MinimalDegree.exists_schur_word_model J σ s hs ι hcard hconj
  intro A hA hcu hc hl t ht ho
  have hne : ∃ g, σ g ≠ 1 := by
    by_contra h
    push Not at h
    have hall (x : actionImage σ) : x = 1 := by
      obtain ⟨g, hg⟩ := x.property
      apply Subtype.ext
      rw [← hg]
      apply Units.ext
      exact h g
    apply ho
    refine ⟨1, ?_⟩
    apply MulEquiv.ext
    intro x
    exact (hall _).trans (hall _).symm
  have hp : ∀ (ι : F →+* Closure σ) (w : List Factor), w.length = s →
      Nonempty ((absoluteRep σ).Equiv (MinimalDegree.word J ι w)) →
      MinimalDegree.PeriodCounts s (schurDegree 2 σ) w := by
    intro ι w hw he
    exact MinimalDegree.periodCounts_of_schur_word J σ hs hconj ι w hw
      (hirr ι) (hunique ι) he hne
  exact GraphStable.graphStableReduction_of_catalogue J hs hcard hconj σ hk
    hirr hunique ⟨ι, w, hw, he⟩ hp A hA hcu hc hl t ht ho

/-- A Schur-linear cubic offender is contained in the literal action image,
including at `s = 2` and for actions with a nontrivial central kernel. -/
theorem actor_le_image
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hcu : IsCubic (normalizerRepresentation σ) A)
    (hc : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A)
    (hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t) :
    A ≤ (actionImage σ).subgroupOf (linearNormalizer σ) :=
  actor_le_image_of_adjoint_steps J hs hcard hconj σ hk
    (graphStableReduction J hs hcard hconj σ hk)
    (adjointFixedSpaceBounds J σ hs hcard hconj hk) A hA hcu hc hl

/-- The equivalent strict common-fixed-codimension obstruction for an actor
not contained in the literal action image. -/
theorem strict_fixedCodim_of_not_le_image
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hcu : IsCubic (normalizerRepresentation σ) A)
    (hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear σ t)
    (ho : ¬ A ≤ (actionImage σ).subgroupOf (linearNormalizer σ)) :
    2 * rank A < fixedCodim (normalizerRepresentation σ) A := by
  by_contra! hc
  exact ho (actor_le_image J hs hcard hconj σ hk A hA hcu hc hl)

end SchurOuter

variable {G : Type*} [Group G] [Finite G]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}
  (h : SourceHypotheses ρ L) (π : J.specialSubgroup →* L)
  (hπ : Function.Surjective π) (hker : π.ker ≤ center J.specialSubgroup)

omit [Finite F] [Finite G] in
/-- The source actor's common fixed codimension is transported through the
Schur field of the actual inflated component, with no faithfulness assumption. -/
theorem source_actor_fixedCodim_eq_schur_mul
    (A : Subgroup (linearNormalizer ((ρ.comp L.subtype).comp π)))
    (hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear ((ρ.comp L.subtype).comp π) t) :
    let : Representation.IsIrreducible ((ρ.comp L.subtype).comp π) := pullback_irreducible J h π hπ
    fixedCodim (normalizerRepresentation ((ρ.comp L.subtype).comp π)) A =
      Module.finrank (ZMod 2) (FrobeniusTensor.SchurField ((ρ.comp L.subtype).comp π)) *
        Module.finrank (FrobeniusTensor.Closure ((ρ.comp L.subtype).comp π))
          (FrobeniusTensor.AbsoluteSpace ((ρ.comp L.subtype).comp π) ⧸
            (absoluteActorRepresentation ((ρ.comp L.subtype).comp π) A hl).invariants) := by
  let : Representation.IsIrreducible ((ρ.comp L.subtype).comp π) := pullback_irreducible J h π hπ
  exact fixedCodim_eq_schur_mul ((ρ.comp L.subtype).comp π) A hl

include hs hcard hconj hker

omit [Finite G] in
/-- Apply the conditional outer exclusion to the literal central-cover pullback. -/
theorem source_actor_le_image_of_adjoint_steps
    (hmodels : letI := pullback_irreducible J h π hπ
      GraphStableReduction J ((ρ.comp L.subtype).comp π) s)
    (hbounds : letI := pullback_irreducible J h π hπ
      AdjointFixedSpaceBounds J ((ρ.comp L.subtype).comp π) s)
    (A : Subgroup (linearNormalizer ((ρ.comp L.subtype).comp π)))
    (hA : IsElementaryTwo A)
    (hcu : IsCubic (normalizerRepresentation ((ρ.comp L.subtype).comp π)) A)
    (hc : fixedCodim (normalizerRepresentation ((ρ.comp L.subtype).comp π)) A ≤ 2 * rank A)
    (hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear ((ρ.comp L.subtype).comp π) t) :
    A ≤ (actionImage ((ρ.comp L.subtype).comp π)).subgroupOf
      (linearNormalizer ((ρ.comp L.subtype).comp π)) := by
  let : Representation.IsIrreducible ((ρ.comp L.subtype).comp π) := pullback_irreducible J h π hπ
  have hk : ((ρ.comp L.subtype).comp π).ker ≤ center J.specialSubgroup := by
    rw [pullback_ker_eq J h π]
    exact hker
  exact actor_le_image_of_adjoint_steps J hs hcard hconj
    ((ρ.comp L.subtype).comp π) hk hmodels hbounds A hA hcu hc hl

/-- The existing source disjunction feeds the literal inner-actor degree theorem,
once the two outer source steps have been proved. -/
theorem source_degree_le_or_inner_actor_of_adjoint_steps
    (hmodels : letI := pullback_irreducible J h π hπ
      GraphStableReduction J ((ρ.comp L.subtype).comp π) s)
    (hbounds : letI := pullback_irreducible J h π hπ
      AdjointFixedSpaceBounds J ((ρ.comp L.subtype).comp π) s) :
    Module.finrank (ZMod 2) V ≤ 6 * s ∨
      ∃ A : Subgroup (linearNormalizer ((ρ.comp L.subtype).comp π)),
        IsElementaryTwo A ∧
        IsCubic (normalizerRepresentation ((ρ.comp L.subtype).comp π)) A ∧
        fixedCodim (normalizerRepresentation ((ρ.comp L.subtype).comp π)) A ≤ 2 * rank A ∧
        A ≤ (actionImage ((ρ.comp L.subtype).comp π)).subgroupOf
          (linearNormalizer ((ρ.comp L.subtype).comp π)) := by
  rcases source_degree_le_or_schurLinear_actor J hs hcard hconj h π hπ hker with hd | ha
  · exact Or.inl hd
  · obtain ⟨A, hA, hcu, hc, hl⟩ := ha
    exact Or.inr ⟨A, hA, hcu, hc,
      source_actor_le_image_of_adjoint_steps J hs hcard hconj h π hπ hker
        hmodels hbounds A hA hcu hc hl⟩

include h hπ

omit [Finite G] in
/-- Unconditional outer exclusion for the exact K.3.3 pullback. Its kernel is
the given central covering kernel, and irreducibility is inherited by
surjective inflation; neither faithfulness nor natural recognition is assumed. -/
theorem source_actor_le_image
    (A : Subgroup (linearNormalizer ((ρ.comp L.subtype).comp π)))
    (hA : IsElementaryTwo A)
    (hcu : IsCubic (normalizerRepresentation ((ρ.comp L.subtype).comp π)) A)
    (hc : fixedCodim (normalizerRepresentation ((ρ.comp L.subtype).comp π)) A ≤ 2 * rank A)
    (hl : ∀ t ∈ A, SchurNormalizer.IsSchurLinear ((ρ.comp L.subtype).comp π) t) :
    A ≤ (actionImage ((ρ.comp L.subtype).comp π)).subgroupOf
      (linearNormalizer ((ρ.comp L.subtype).comp π)) := by
  let : Representation.IsIrreducible ((ρ.comp L.subtype).comp π) :=
    pullback_irreducible J h π hπ
  have hk : ((ρ.comp L.subtype).comp π).ker ≤ center J.specialSubgroup := by
    rw [pullback_ker_eq J h π]
    exact hker
  exact SchurOuter.actor_le_image J hs hcard hconj
    ((ρ.comp L.subtype).comp π) hk A hA hcu hc hl

/-- The source degree bound or a literal inner cubic actor, with every outer
representation and fixed-space premise discharged. This is the input to the
independent inner-actor degree estimate. -/
theorem source_degree_le_or_inner_actor :
    Module.finrank (ZMod 2) V ≤ 6 * s ∨
      ∃ A : Subgroup (linearNormalizer ((ρ.comp L.subtype).comp π)),
        IsElementaryTwo A ∧
        IsCubic (normalizerRepresentation ((ρ.comp L.subtype).comp π)) A ∧
        fixedCodim (normalizerRepresentation ((ρ.comp L.subtype).comp π)) A ≤ 2 * rank A ∧
        A ≤ (actionImage ((ρ.comp L.subtype).comp π)).subgroupOf
          (linearNormalizer ((ρ.comp L.subtype).comp π)) := by
  rcases source_degree_le_or_schurLinear_actor J hs hcard hconj h π hπ hker with hd | ha
  · exact Or.inl hd
  · obtain ⟨A, hA, hcu, hc, hl⟩ := ha
    exact Or.inr ⟨A, hA, hcu, hc,
      source_actor_le_image J hs hcard hconj h π hπ hker A hA hcu hc hl⟩

end CFSG.Quasithin.ChapterK.RankOne.UnitaryRecognition.CubicDegree
