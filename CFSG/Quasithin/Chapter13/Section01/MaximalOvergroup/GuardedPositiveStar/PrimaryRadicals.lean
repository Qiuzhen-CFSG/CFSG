module

public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.GuardedPositiveStar.Radicals
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.PrimaryAction
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.PrimaryExponent
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ReducedAction
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.ReducedDetection
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.GuardedRatio
public import Theory.GroupTheory.SolvableRadical.PrimaryDetection

/-!
# Centralization by the original primary radicals

For a maximal nonquasisimple local component L, each original
I_p=O^{p′}(O∞(L)) has zero intrinsic module. In exponent p it is exactly
Ξ_p(L), so the guarded positive-star theorem applies. A larger exponent
forces p>5 by A.1.30. The actual irreducible Frattini action identifies
the Sylow centralizer on R₂(I_pT), and guarded 3.1.8 with D.2.13 gives
p=3 or5, a contradiction. The reduced module and its kernel are constructed.

The original universal A.3.12, C.2.7 and guarded 3.1.8 source families
remain earlier inputs; no faithfulness or primary action conclusions are
assumed. Source: Aschbacher--Smith 3.2.14, p.585;13.1.4(5), p.867.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.GuardedPositiveStar
open Chapter1 Chapter1.Section02 Chapter1.RadicalExclusions.ModelReduction ChapterA.Section04
open Chapter3.RadicalCentralization
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Each original odd-primary radical of a maximal nonquasisimple local
component has zero intrinsic module. The original action and its Sylow
centralizer have no remaining premises. -/
theorem maximal_primary_intrinsicModule_eq_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hA312 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ →
      ∀ (S : Sylow 2 A) (B : Subgroup A),
        B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (source : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    (hout : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      (T : Subgroup G) ≤ M → Chapter3.HasMaximalOutside T M)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    intrinsicSignalizerModule (primaryRadical p L) = ⊥ := by
  by_cases hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))
  swap
  · have he := primaryRadical_eq_bot_of_not_dvd hG T hL.1 ho hd
    exact bot_unique ((intrinsicModule_le_self _).trans_eq he)
  have hstar := maximal_radical_positive_star hG T hA312 source hL hn ho hd
  obtain ⟨hq,he,hm⟩ := RadicalConjugateRigidity.maximal_radical_structure hG T hL hn ho hd
  have hXI := XiP_le_primaryRadical L hq
  by_cases hexp : ∀ x : primaryRadical p L ⧸ pCore 2 (primaryRadical p L), x ^ p = 1
  · have heq := le_antisymm (primaryRadical_le_XiP_of_exponent hG T hL.1 ho hexp) hXI
    rw [heq]
    exact positive_star_intrinsicModule_eq_bot hG h318 T hout hstar
  by_contra hnonzero
  have hnorm : normalizer (XiP p L : Set G) ≤ normalizer (primaryRadical p L : Set G) := by
    rw [he]
    exact normalizer_le_normalizer_primaryRadical L p
  have hT : (T : Subgroup G) ≤ normalizer (primaryRadical p L : Set G) :=
    hstar.2.1.invariant.trans hnorm
  have hI := primaryRadical_twoPerfect L ho
  have hquot := primaryRadical_quotient_isPGroup hG T hL.1 ho
  have hirr := primaryRadical_irreducible hG T hL.1 hn ho hd hT
  have hne := reduced_action_ne_bot_of_intrinsic_module (T : Subgroup G)
    (primaryRadical p L) hT hI ho hquot hnonzero
  have hc := reduced_sylow_centralizer T (primaryRadical p L) hT hI hirr hne
  have hIM : primaryRadical p L ≤ normalizer (XiP p L : Set G) := by
    rw [he]
    exact (map_subtype_le _).trans L.le_normalizer
  have hsmall := prime_restriction_of_guarded_star hG T h318 hstar.2 hXI hIM hnorm hI
    (hout _ (he.symm ▸ hm) hstar.2.1.invariant) ho hquot
    (reducedTwoSubgroup (primaryRadical p L ⊔ (T : Subgroup G) : Subgroup G))
    isPReduced_reducedPSubgroup hc
  have hp := (primaryRadical_higher_structure hG T hL.1 hn ho hexp).1
  rcases hsmall with he | he <;> omega

/-- Every primary radical centralizes R₂ of any original overgroup in
which its defining local component is normal. -/
theorem maximal_primary_centralizes_reduced
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hA312 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ →
      ∀ (S : Sylow 2 A) (B : Subgroup A),
        B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (source : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    (hout : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      (T : Subgroup G) ≤ M → Chapter3.HasMaximalOutside T M)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (J : Subgroup G) (hLJ : L ≤ J) (hJn : J ≤ normalizer (L : Set G)) :
    primaryRadical p L ≤ centralizer ((reducedTwoSubgroup J).map J.subtype : Set G) := by
  have hzero := maximal_primary_intrinsicModule_eq_bot hG T hA312 source h318 hout hL hn ho
  have hXJ : primaryRadical p L ≤ J := (map_subtype_le _).trans hLJ
  have hnorm : ((primaryRadical p L).subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer
      (hJn.trans (normalizer_le_normalizer_primaryRadical L p))
  have hm : ⁅reducedTwoSubgroup J,(primaryRadical p L).subgroupOf J⁆ = ⊥ := by
    by_contra hne
    exact (intrinsicModule_ne_bot_of_reduced_action _ J hXJ hnorm.isSubnormal
      (primaryRadical_twoPerfect L ho) hne) hzero
  have ha := congrArg (Subgroup.map J.subtype) hm
  rw [map_commutator,map_subgroupOf_eq_of_le hXJ,Subgroup.map_bot,commutator_comm] at ha
  exact commutator_eq_bot_iff_le_centralizer.mp ha

/-- The primary residuals detect the whole solvable radical, proving the
maximal-component case of original 3.2.14 in every normal overgroup. -/
theorem maximal_solvableRadical_centralizes_reduced
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hA312 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ →
      ∀ (S : Sylow 2 A) (B : Subgroup A),
        B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (source : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.GuardedSourceTheorem318One G)
    (hout : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      (T : Subgroup G) ≤ M → Chapter3.HasMaximalOutside T M)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L))
    (J : Subgroup G) (hLJ : L ≤ J) (hJn : J ≤ normalizer (L : Set G)) :
    (solvableRadical L).map L.subtype ≤
      centralizer ((reducedTwoSubgroup J).map J.subtype : Set G) := by
  let R := (solvableRadical L).map L.subtype
  have hRJ : R ≤ J := (map_subtype_le _).trans hLJ
  let N := R.subgroupOf J
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (hJn.trans (normalizer_le_normalizer_characteristic_image L (solvableRadical L)))
  have hNC : N ≤ centralizer (reducedTwoSubgroup J : Set J) := by
    apply normal_centralizes_reduced_of_primary_residuals N _ isPReduced_reducedPSubgroup
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    have hc := maximal_primary_centralizes_reduced hG T hA312 source h318 hout hL hn ho J hLJ hJn
    have he : ((primeToResidual p N).map N.subtype).map J.subtype = primaryRadical p L := by
      rw [map_embedded_primeToResidual_of_hom,
        map_subgroupOf_eq_of_le hRJ,← map_embedded_primeToResidual_of_hom p (solvableRadical L) L.subtype]
      rfl
    intro x hx
    apply mem_centralizer_iff.mpr
    intro v hv
    have hh := mem_centralizer_iff.mp (hc (he ▸ mem_map_of_mem J.subtype hx))
      (v : G) (mem_map_of_mem J.subtype hv)
    exact Subtype.ext hh
  intro r hr
  apply mem_centralizer_iff.mpr
  rintro v ⟨w,hw,rfl⟩
  exact congrArg Subtype.val
    (mem_centralizer_iff.mp (hNC (show (⟨r,hRJ hr⟩ : J) ∈ N from hr)) w hw)


end CFSG.Quasithin.Chapter13.Section01.GuardedPositiveStar
