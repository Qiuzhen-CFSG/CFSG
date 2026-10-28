module
public import CFSG.Quasithin.Chapter14.Section06.SourceF9
public import CFSG.Quasithin.Chapter14.Section06.MaximalOvergroups
public import CFSG.Quasithin.Chapter14.Section06.SuitableInvolutionIndices
public import CFSG.Quasithin.ClassificationModels

/-!
# Source contracts for the two terminal rank contradictions

These interfaces retain the original F.9 plane, point, residual, and outside
subgroup. The suitable-element conditions are (U0)--(U3), except that the
local Sylow clause is derived from (U3). The second parabolic is a subgroup
of the literal quotient centralizer, with its actual S₃ quotient.

The terminal witness asks for the rank-four residual span established in
14.6.17(5) or the last paragraph on p.1042. It does not assume a rank-three
bound or a contradiction. The independent rank-three input is the precise
14.6.10(5) conclusion used by both endgames, for the preferred IStar choice.

Source: Aschbacher--Smith, 14.6.10(5), 14.6.17 and 14.6.24, pp.1029--1042.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- Recover the literal plane and M-centralizer quotient from the original
rank-two hypothesis, preserving the specified residual and overgroup. -/
theorem source_plane_of_rankTwo
    {T : Sylow 2 G} {M Mc : Subgroup G}
    (h : RankTwoHypothesis KnownSimple.IsKnownSimple T (sourceResidual M Mc) M) :
    Nat.card (localModule T M) = 4 ∧
      Nonempty ((M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
        Equiv.Perm (Fin 3)) := by
  refine ⟨?_, ?_⟩
  · simpa only [Section02.rankTwoSeed_eq_localModule] using rankTwoSeed_card h
  · let f := setupSeedAction M (rankTwoSeed T M) RankTwoHypothesis.M_normalizes_seed
    have hk : f.ker = (centralizer (rankTwoSeed T M : Set G)).subgroupOf M :=
      setupSeedAction_ker M (rankTwoSeed T M) RankTwoHypothesis.M_normalizes_seed
    let : ((centralizer (rankTwoSeed T M : Set G)).subgroupOf M).Normal := by
      rw [← hk]
      infer_instance
    obtain ⟨e⟩ := h.seedAut_model
    have he : Nonempty ((M ⧸ (centralizer (rankTwoSeed T M : Set G)).subgroupOf M) ≃*
        Equiv.Perm (Fin 3)) := ⟨
      ((QuotientGroup.quotientMulEquivOfEq
        (setupSeedAction_ker M (rankTwoSeed T M) RankTwoHypothesis.M_normalizes_seed).symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective f h.full_M_action)).trans e⟩
    have hdenom : (centralizer (rankTwoSeed T M : Set G)).subgroupOf M =
        (centralizer (localModule T M : Set G)).subgroupOf M :=
      congrArg (fun V : Subgroup G => (centralizer (V : Set G)).subgroupOf M)
        (Section02.rankTwoSeed_eq_localModule T M)
    obtain ⟨eM⟩ := he
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hdenom.symm).trans eM⟩

/-- Actual suitable element and second-parabolic data, before either terminal
rank calculation. All normalizers and cores retain their original ambient group. -/
structure SourceSecondParabolicData {D : ChapterF.Section09.Setup G}
    (h : D.Hypothesis) (Mc M : Subgroup G) where
  u : G
  mem_span : u ∈ D.UH
  index : (suitableQuotientCentralizer h u).relIndex (D.T : Subgroup G) = 2
  moves_core : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G)
  product_moves_core : ∀ t ∈ (D.T : Subgroup G),
    t ∉ suitableQuotientCentralizer h u →
      ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)
  local_normalizer : Mc ⊓ normalizer (suitableQuotientCentralizer h u : Set G) =
    (D.T : Subgroup G)
  H2 : Subgroup G
  quotient_sylow : Chapter1.IsSylowIn 2 (suitableQuotientCentralizer h u) H2
  le_quotient_centralizer : H2 ≤ h.kernel (zpowers u)
  quotient_model : Nonempty ((H2 ⧸ pCore 2 H2) ≃* Equiv.Perm (Fin 3))
  outside : ¬ H2 ≤ M
  core_index : 4 < (D.H.pCoreIn 2).relIndex (D.T : Subgroup G)
  module_rank : 4 ≤ Nat.log 2 ((centralizer (D.H.pCoreIn 2 : Set G)).relIndex D.UH)

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))


/-- The remaining rank bound on the literal second parabolic. The inclusion
minimality condition IMin is deliberately absent. -/
def SourceSecondParabolicRankThree : Prop :=
  ∀ (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M)
    (I : Subgroup G),
    I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M) →
    ((T : Subgroup G) ⊓ I = (T : Subgroup G) ⊓ centralizer ({d.u} : Set G) →
      I ≤ centralizer ({d.u} : Set G)) →
    primeRank 2 (conjugateSpanBy (localModule T M)
      ((pResidual 2 d.H2).map d.H2.subtype ⊔ ((T : Subgroup G) ⊓ I))) = 3

/-- The actual witness needed after the odd-core and component reductions.
Its rank-four assertion concerns the smaller residual span, before adjoining
any maximal-intersection Sylow subgroup. -/
def SourceTerminalWitness : Prop :=
  ∃ (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (d : SourceSecondParabolicData
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) Mc M),
    centralizer ({d.u} : Set G) ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({d.u} : Set G)) Mc M ∧
    primeRank 2 (conjugateSpanBy (localModule T M)
      ((pResidual 2 d.H2).map d.H2.subtype)) = 4

end CFSG.Quasithin.Chapter14.Section06
