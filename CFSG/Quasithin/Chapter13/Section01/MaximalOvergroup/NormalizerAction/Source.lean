module
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.NormalizerAction
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.GuardedPositiveStar.PrimaryRadicals
public import CFSG.Quasithin.Chapter13.Section01.RadicalQuotient

/-!
# Original 13.1.8 on the maximal nonquasisimple component

The primary-radical theorem centralizes R₂(N_G(L)) with the whole
solvable radical. The original faithful local hypothesis makes the
commutator nonzero, and component minimality gives the reverse kernel
inclusion. Thus the literal component image is L/O∞(L), hence PSL₂(p)
for p>3. All radical supplements give the same nontrivial commutator.

The universal A.3.12 embedding, C.2.7 sieve, and guarded 3.1.8 families
remain the earlier source inputs in the centralization theorem.
Source: Aschbacher--Smith 13.1.4(5),13.1.8, pp.867--869.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01
open Chapter1 Chapter1.Section02 Chapter12.Section02
open Chapter1.RadicalExclusions.ModelReduction
universe u
variable {G : Type u} [Group G] [Finite G]

theorem maximal_nonquasisimple_normalizer_action
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hA312 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ →
      ∀ (S : Sylow 2 A) (B : Subgroup A),
        B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (source : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    (hout : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      (T : Subgroup G) ≤ M → Chapter3.HasMaximalOutside T M)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) :
    (NormalizerReducedAction.componentMap L).ker = solvableRadical L ∧
      L ⊓ centralizer (normalizerReduced L : Set G) = (solvableRadical L).map L.subtype ∧
      (∃ p : ℕ, p.Prime ∧ 3 < p ∧
        ClassicalGroup.IsPSL (NormalizerReducedAction.componentImage L) 2 p) ∧
      normalizerMoved L ≠ ⊥ ∧
      ∀ L₁ : Subgroup G, (solvableRadical L).map L.subtype ⊔ L₁ = L →
        ⁅normalizerReduced L,L₁⁆ = normalizerMoved L := by
  have hTL := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk hG hL.1.1.2.2) hn
  have hne := (faithful_maximal_normalizer_moved hG hL hTL).2.1
  have hc := GuardedPositiveStar.maximal_solvableRadical_centralizes_reduced
    hG T hA312 source h318 hout hL.1 hn
    (normalizer (L : Set G)) L.le_normalizer le_rfl
  rw [← normalizerReduced_eq] at hc
  have hk := NormalizerReducedAction.kernel_eq_solvableRadical hL.1.1 hne hc
  have hC : L ⊓ centralizer (normalizerReduced L : Set G) =
      (solvableRadical L).map L.subtype := by
    have hh := congrArg (Subgroup.map L.subtype) hk
    rw [NormalizerReducedAction.componentMap_ker_ambient,map_comap_eq,range_subtype] at hh
    exact hh
  obtain ⟨p,hp,hp3,he⟩ := nonquasisimple_local_radical_quotient hG T hL.1.1 hn
  exact ⟨hk,hC,⟨p,hp,hp3,he.of_mulEquiv
    (NormalizerReducedAction.radicalQuotientEquiv hL.1.1 hne hc).symm⟩,
    hne,fun _ hgen => NormalizerReducedAction.supplement_commutator hc hgen⟩

end CFSG.Quasithin.Chapter13.Section01
