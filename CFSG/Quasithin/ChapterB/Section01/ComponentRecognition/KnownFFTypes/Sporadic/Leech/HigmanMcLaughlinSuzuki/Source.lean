module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Defs
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.Representation.BinaryOffender.CubicConjugateDimension
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.AutomorphismTwoRank

/-!
# The actual Higman--Sims source domain and cubic degree reduction

For K.4 the actor is the given finite SQTK group G, its generalized Fitting
subgroup acts faithfully and irreducibly, and the latter's actual central
quotient is the ATLAS Higman--Sims carrier. Schur's lemma and faithful descent
of automorphisms through perfect central covers bound the two-rank of G by
five. A cubic actor of ratio at most two therefore contains an involution
moving at most ten dimensions. Five-conjugate generation, when supplied,
then bounds the whole degree by fifty.

The final conditional lemma combines this with the two still separate
representation-theoretic inputs: recognition of degree twenty in this window
and the degree-twenty fixed-space estimates. Neither input is asserted here.

Source: Aschbacher--Smith K.4, printed p.457; Guralnick--Malle,
*Classification of 2F-modules, I*, Proposition 5.1 (the HS paragraph) and
Theorem 6.6/Table 6.7, DOI 10.1016/S0021-8693(02)00526-4. The author's
preprint is https://agag-malle.math.rptu.de/~malle/download/failfact.dvi.
The HS paragraph gives bounds 24 for HS and 50 for its outer extension,
followed by the degree-twenty inner and outer involution calculations.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
open Subgroup Theory.GroupTheory Representation.BinaryOffender

universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The genuine K.4 hypotheses for the HS branch, before imposing a ratio
bound. No degree, module classification, or exclusion is included. -/
structure SourceHypotheses : Prop where
  sqtk : IsSQTK KnownSimple.IsKnownSimple G
  quasisimple : IsQuasisimple (generalizedFitting G)
  faithful : Function.Injective ρ
  irreducible : Representation.IsIrreducible (ρ.comp (generalizedFitting G).subtype)
  centralQuotient : Nonempty
    ((generalizedFitting G) ⧸ center (generalizedFitting G) ≃*
      KnownSimple.SporadicName.hs.Carrier)

variable {ρ}

/-- Central covers and every permissible outer action retain the rank-five
bound on the actual ambient group. -/
theorem SourceHypotheses.twoRank_le_five (h : SourceHypotheses ρ) :
    primeRank 2 G ≤ 5 := by
  let := h.quasisimple
  obtain ⟨e⟩ := h.centralQuotient
  exact (primeRank_le_central_quotient_automorphisms ρ (generalizedFitting G)
    h.faithful h.irreducible e).trans
      _root_.Sporadic.LeechRelated.HS.automorphism_twoRank_le_five

/-- A cubic-ratio witness in the actual actor, retaining its cubic condition
and both numerical bounds for the local representation calculation. -/
theorem SourceHypotheses.exists_small_cubic_actor (h : SourceHypotheses ρ)
    (hq : cubicRatio ρ ≤ 2) :
    ∃ A : Subgroup G, IsElementaryTwo A ∧ IsCubic ρ A ∧
      rank A ≤ 5 ∧ fixedCodim ρ A ≤ 2 * rank A := by
  obtain ⟨A, hA, hc, hd⟩ := (cubicRatio_le_nat_iff ρ 2).mp hq
  exact ⟨A, hA, hc, hA.rank_le_of_primeRank_le h.twoRank_le_five, hd⟩

variable [FiniteDimensional (ZMod 2) V]

/-- The small-displacement involution is in G, on the literal representation. -/
theorem SourceHypotheses.exists_involution_codim_le_ten (h : SourceHypotheses ρ)
    (hq : cubicRatio ρ ≤ 2) :
    ∃ t : G, t ≠ 1 ∧ t ^ 2 = 1 ∧ fixedCodim ρ (zpowers t) ≤ 10 := by
  exact exists_involution_of_cubicRatio_le ρ h.twoRank_le_five hq

/-- The source's uniform degree window, conditional only on the concrete
five-conjugate generation fact still to be supplied by the HS producer. -/
theorem SourceHypotheses.finrank_le_fifty_of_five_conjugates
    (h : SourceHypotheses ρ)
    (hgen : InvolutionConjugateGenerationBound (generalizedFitting G) 5)
    (hq : cubicRatio ρ ≤ 2) : Module.finrank (ZMod 2) V ≤ 50 := by
  let := h.quasisimple
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) :=
    IsQuasisimple.simple
  let : Nontrivial (generalizedFitting G) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting G))).nontrivial
  have hfix : fixedSpace ρ (generalizedFitting G) = ⊥ :=
    invariants_eq_bot_of_faithful_irreducible (ρ.comp (generalizedFitting G).subtype)
      (h.faithful.comp (generalizedFitting G).subtype_injective) h.irreducible
  exact finrank_le_of_cubicRatio_le_of_conjugates ρ (generalizedFitting G)
    hfix hgen h.twoRank_le_five hq

/-- Conditional assembly for the actual K.4 actor. The degree-window
recognition and degree-twenty fixed-space estimate are independent inputs;
this is not an unconditional HS exclusion. -/
theorem SourceHypotheses.not_cubicRatio_le_two_of_inputs
    (h : SourceHypotheses ρ)
    (hgen : InvolutionConjugateGenerationBound (generalizedFitting G) 5)
    (hdegree : Module.finrank (ZMod 2) V ≤ 50 → Module.finrank (ZMod 2) V = 20)
    (hlocal : Module.finrank (ZMod 2) V = 20 →
      ∀ A : Subgroup G, IsElementaryTwo A → 2 * rank A < fixedCodim ρ A) :
    ¬ cubicRatio ρ ≤ 2 := by
  intro hq
  have hd := hdegree (h.finrank_le_fifty_of_five_conjugates hgen hq)
  obtain ⟨A, hA, _, _, hcodim⟩ := h.exists_small_cubic_actor hq
  exact (not_lt_of_ge hcodim) (hlocal hd A hA)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
