module

public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.GuardedPositiveStar
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.PositiveStar.PositiveRadical
public import CFSG.Quasithin.Chapter13.Section01.MaximalOvergroup.ReducedModule
public import CFSG.Quasithin.Chapter13.Section01.RadicalConjugateRigidity.Source
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.SourceCompletion.AllPrimes

/-!
# Canonical radicals centralize the actual normalizer's reduced subgroup

The complete odd-prime-support construction supplies starred membership
of every canonical radical of the original maximal local component.
The actual quaternion action supplies positive membership. Guarded 3.2.13
then makes its intrinsic module vanish, and A.4.11 transfers this to
R₂(N_G(L)). The equality of the radical and component normalizers also
identifies the unique maximal local above the original C_G(Ω₁Z(T)).

The remaining earlier inputs are the universal A.3.12 and C.2.7 source
implications and guarded 3.1.8. No starred membership, centralization or
maximal-local uniqueness is assumed.
Source: Aschbacher--Smith 13.1.4(4--6), pp.867--868.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.GuardedPositiveStar
open Chapter1 Chapter1.Section02 Chapter1.RadicalExclusions.ModelReduction ChapterA.Section04
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A positive starred radical centralizes the reduced subgroup of its
full normalizer, by the intrinsic-module commutator bound A.4.11. -/
theorem positive_star_centralizes_normalizerReduced
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h318 : Chapter3.GuardedSourceTheorem318One G) (T : Sylow 2 G)
    (hout : ∀ M : Subgroup G, IsMaximalTwoLocal M →
      (T : Subgroup G) ≤ M → Chapter3.HasMaximalOutside T M)
    {X : Subgroup G} (hX : X ∈ Chapter3.XiPlus G (T : Subgroup G) ∩ XiStar G T) :
    X ≤ centralizer (normalizerReduced X : Set G) := by
  let J := normalizer (X : Set G)
  let Y := X.subgroupOf J
  let : Y.Normal := normal_subgroupOf_of_le_normalizer (show J ≤ normalizer (X : Set G) from le_rfl)
  let e : Y ≃* X := subgroupOfEquivOfLe X.le_normalizer
  have he : Y.map J.subtype = X := map_subgroupOf_eq_of_le X.le_normalizer
  have hzero : intrinsicSignalizerModule Y = ⊥ := by
    apply map_injective (f := J.subtype) J.subtype_injective
    rw [← intrinsicSignalizerModule_map_of_injective J.subtype J.subtype_injective,
      he, positive_star_intrinsicModule_eq_bot hG h318 T hout hX, Subgroup.map_bot]
  have hm : ⁅reducedTwoSubgroup J,Y⁆ = ⊥ := bot_unique
    ((reduced_commutator_le_intrinsicModule Y
      (show Y.Normal from inferInstance).isSubnormal
      (hX.1.1.perfect.of_surjective e.symm.toMonoidHom e.symm.surjective)).trans_eq hzero)
  have ha := congrArg (Subgroup.map J.subtype) hm
  rw [map_commutator,he,Subgroup.map_bot,commutator_comm] at ha
  rw [normalizerReduced_eq]
  exact commutator_eq_bot_iff_le_centralizer.mp ha

/-- The canonical radical of any nonquasisimple maximal local component
is positive and starred; single-prime Fitting support is not required. -/
theorem maximal_radical_positive_star
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hA312 : ∀ (A : Type u) [Group A] [Finite A],
      IsSQTK KnownSimple.IsKnownSimple A → pCore 2 A = ⊥ →
      ∀ (S : Sylow 2 A) (B : Subgroup A),
        B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (source : FullSieve.SourceInterface.Source KnownSimple.IsKnownSimple G)
    {L : Subgroup G} (hL : L ∈ LStar G (T : Subgroup G))
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    XiP p L ∈ Chapter3.XiPlus G (T : Subgroup G) ∩ XiStar G T :=
  ⟨XiP_mem_XiPlus_source hG T hL.1 hn ho hd,
    XiP_mem_XiStar_of_A312_C27 hG T hA312 source hL hn ho hd⟩

/-- The actual Ξ_p(L) centralizes R₂(N_G(L)), and its normalizer is the
unique maximal two-local over the original Sylow-center centralizer. -/
theorem maximal_radical_reduced_and_centralizer
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
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L))) :
    XiP p L ≤ centralizer (normalizerReduced L : Set G) ∧
      normalizer (XiP p L : Set G) = normalizer (L : Set G) ∧
      IsMaximalTwoLocal (normalizer (L : Set G)) ∧
      centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ normalizer (L : Set G) ∧
      ∀ M : Subgroup G, IsMaximalTwoLocal M →
        centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M →
        M = normalizer (L : Set G) := by
  have hX := maximal_radical_positive_star hG T hA312 source hL hn ho hd
  obtain ⟨_,he,_⟩ := RadicalConjugateRigidity.maximal_radical_structure hG T hL hn ho hd
  have hc := positive_star_centralizes_normalizerReduced hG h318 T hout hX
  have hu := positive_star_centralizer_unique hG h318 T hout hX
  rw [normalizerReduced_eq,he,← normalizerReduced_eq] at hc
  rw [he] at hu
  exact ⟨hc,he,hu⟩

end CFSG.Quasithin.Chapter13.Section01.GuardedPositiveStar
