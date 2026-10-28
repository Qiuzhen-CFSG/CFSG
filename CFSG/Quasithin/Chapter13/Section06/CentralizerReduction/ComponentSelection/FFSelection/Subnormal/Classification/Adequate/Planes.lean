module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Adequate
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Adequate.SourcePlane

/-!
# Recovering the cubic dimension in the adequate 13.6.10 argument

The B.5.7 recovery theorem reconstructs the cubic moved plane from its
actual faithful offender action and complete earlier-source inputs. The
proved group-only placement identifies the restricted subnormal cubic
with that same second factor. Transport along the literal offender inclusion
gives dimension two in the original representation, and the normalizer
bound completes both original conclusions.

The earlier B.5.1/B.5.2/preparation B.5.5/A.2.1/A.3.6 implications remain
explicit in AdequateSource.EarlierSources. Their producers are
qt-b05-quasisimple, qt-b05-quotient-components, qt-a-02 and qt-a03-sqtk-structure;
qt-b05-general-classification also requires them. No multiplier table,
moved-plane conclusion or fixed-space splitting is assumed.
Source: Aschbacher–Smith, B.5.7, p.106; 13.6.10, p.928
(combined manuscript, 1 March 2004).
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
open Solvable.Construction.Exceptional
universe u v
variable {D : Type u} [Group D] [Finite D]
    {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) D W)

omit [FiniteDimensional (ZMod 2) W] in
private theorem native_hypothesis {K : GroupClass.{u}} (h : FFHypothesis K ρ) :
    ChapterB.SourceInduction.FFHypothesis K ρ := by
  refine ⟨h.finite_module, h.faithful, h.twoCore, h.generated, ?_⟩
  obtain ⟨d⟩ := h.quotient
  let := d.coverGroup
  let := d.coverFinite
  let := d.kernelNormal
  exact ⟨{ Cover := d.Cover, kernel := d.kernel, sqtk := d.sqtk, equiv := d.equiv }⟩

omit [FiniteDimensional (ZMod 2) W] in
/-- Recover the original cubic dimension from B.5.7's proved source
construction, preserving the literal offender restriction and cubic. -/
theorem outerSixThree_bounds_of_adequate {K : GroupClass.{u}}
    (earlier : AdequateSource.EarlierSources.{u,v} K)
    (hyp : FFHypothesis K (offenderRepresentation ρ))
    {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (c : ChapterB.OuterSixThreeShape (offenderSubgroup ρ)) : CubicBounds ρ A := by
  have hplane := AdequateSource.outer_moved_plane c (offenderRepresentation ρ) earlier
    (native_hypothesis (offenderRepresentation ρ) hyp)
  have he : moved ρ A = moved (offenderRepresentation ρ) c.second := by
    change subspaceCommutator ρ ⊤ A =
      subspaceCommutator (offenderRepresentation ρ) ⊤ c.second
    rw [← marked_commutator ρ A h.le_offender ⊤,
      outerSixThree_internal_eq_second_of_adequate h c]
  refine ⟨?_, ?_⟩
  · rw [he]
    exact hplane
  · rw [normalizer_eq_top_iff.mpr (outerSixThree_normal_of_adequate h c), index_top]
    decide

/-- Both full cubic bounds from the corrected adequate alternatives and
the genuine earlier-source inputs for the exceptional cubic-plane recovery. -/
theorem bounds_of_adequate {K : GroupClass.{u}}
    (earlier : AdequateSource.EarlierSources.{u,v} K)
    (hyp : FFHypothesis K (offenderRepresentation ρ))
    {A : Subgroup D} {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (hc : ProjectiveLine.AdequateSourceAlternative (offenderRepresentation ρ)) :
    CubicBounds ρ A := by
  cases hc with
  | trivial ht => exact (h.not_trivial ht).elim
  | quasisimple hq ha => exact (quasisimple_excluded_of_source ρ h hq ha).elim
  | symmetricThree c => exact symmetricThree_bounds ρ h c
  | twoFactors c => exact twoFactors_bounds ρ h c
  | outerSixThree c => exact outerSixThree_bounds_of_adequate ρ earlier hyp h c
  | hyperplane c => exact hyperplane_bounds ρ h c

section Application
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
    (s : A5Module.Marking L V)
    [IsElementaryAbelian 2 (internalUv (A5Module.markedZ s) (A5Module.markedV s))]
local notation "z₀" => A5Module.markedZ s
local notation "v₀" => A5Module.markedV s
local notation "ρ₀" => uvRepresentation z₀ v₀ (A5Module.markedZ_mem_Gv s)
local notation "A₀" => starImage z₀ v₀ (Lv L v₀)

/-- Both original bounds for the actual marked Chapter 13 source module. -/
theorem marked_bounds_of_adequate (T : Subgroup G)
    (S : Sylow 2 (Gv v₀))
    (hS : (S : Subgroup (Gv v₀)).map (Gv v₀).subtype = Tv T v₀)
    (hT : Tv T v₀ ≤ normalizer (Lv L v₀ : Set G))
    (hcore : pCore 2 (Gstar z₀ v₀) = ⊥)
    (hcard : Nat.card (Lv L v₀ ⧸ pCore 2 (Lv L v₀)) = 3)
    (hfull : A₀ = ⁅A₀, starImage z₀ v₀ (Stellmacher.elementaryAbelianMaxJ (Tv T v₀))⁆)
    (hs : (A₀).IsSubnormal)
    {𝒦 : GroupClass.{u}}
    (earlier : AdequateSource.EarlierSources.{u,u} 𝒦)
    (classification : ProjectiveLine.AdequateGeneralClassificationInput.{u,u} 𝒦)
    (hSQ : IsSQTK 𝒦 (Gv v₀)) : CubicBounds ρ₀ A₀ := by
  have hyp := uv_offender_hypothesis z₀ v₀ (A5Module.markedZ_mem_Gv s) hSQ hcore
  exact bounds_of_adequate ρ₀ earlier hyp
    (marked_cubic_hypothesis s T S hS hT hcore hcard hfull hs)
    (classification _ _ _ hyp)

end Application
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification
