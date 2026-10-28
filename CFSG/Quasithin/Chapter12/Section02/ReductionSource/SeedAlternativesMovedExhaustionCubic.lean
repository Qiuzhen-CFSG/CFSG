module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesNormalizerBound
public import CFSG.Quasithin.Chapter3.Section02.ChosenSource325.MovedExhaustionCubic

/-!
# Minimal cubic actors on the full chosen-seed normalizer orbit

The proved source 3.1.6 bound, with the multiple-overgroup guard supplied,
constructs a minimal cubic actor in the image of the original Sylow T on
U = componentOrbit V (normalizer L). It acts on the literal smaller orbit
W = componentOrbit V T. Restriction gives the original centralizer image,
its rank and fixed-codimension budgets, and the three D.2.7 alternatives.

The conditional strict-ratio theorem supplies the numerical step in D.3.19.
The source325 assembly owner qt-baumann-fsu must still discharge its movement
and kernel premises through the D.3.12--18 structural argument, then exclude
strict normalizer-orbit enlargement. No equality U = W is used here.
Source: Aschbacher--Smith D.3.10--19, 3.2.5 and12.2.2,
printed pp.201--204,580 and794--795.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Theory.GroupTheory Chapter3.Section02.ChosenSource325 ChapterD
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Reducedness of the full normalizer orbit gives the zero two-core needed
for the cubic permutation argument, on this exact faithful image. -/
theorem normalizerActor_twoCore_eq_bot
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    pCore 2 (internalActionImage (normalizer (L : Set G))
      (componentOrbit V (normalizer (L : Set G))) (le_normalizer_componentOrbit _ _)) = ⊥ := by
  have hUL : componentOrbit V (normalizer (L : Set G)) ≤ L :=
    iSup_conjugates_le_of_le_normalizer V (normalizer (L : Set G)) L D.le_component le_rfl
  exact Chapter3.Section02.internalActionImage_core_of_reduced _ _
    (hUL.trans L.le_normalizer) (le_normalizer_componentOrbit _ _)
    (D.normalizerOrbit_reduced h
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)))

/-- The full cubic minimum has a minimal actor in the original Sylow image,
which therefore preserves the literal Sylow orbit inside the full orbit. -/
theorem exists_normalizer_starred_in_sylow_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let hn := le_normalizer_componentOrbit V M
    ∃ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component ∧
      A ∈ QhatStar (UniqueFactor.imageRepresentation M U hn) ∧
      A ≤ subspaceStabilizer (UniqueFactor.imageRepresentation M U hn)
        (internalSection U (componentOrbit V (T : Subgroup G))) := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let hn := le_normalizer_componentOrbit V M
  obtain ⟨A,hAS,hA⟩ := exists_starred_in_sylow (UniqueFactor.imageRepresentation M U hn)
    (internalSylow T M U hn D.sylow_normalizes_component)
    (D.normalizerOrbit_cubicBound_of_many h hmany)
  exact ⟨A,hAS,hA,hAS.trans (internalSylow_section_stable T M U
    (componentOrbit V T) hn D.sylow_normalizes_component (le_normalizer_componentOrbit V T))⟩

/-- The literal normalizer cubic bound gives a minimal actor in the original
Sylow image, with the exact centralizer/strict-ratio/faithful-span alternatives
and the same actor's kernel-plus-section rank and displacement budgets. -/
theorem normalizer_starred_sylow_section_of_many
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    letI := D.normalizerOrbit_elementary h.toHypothesis1221
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let W := componentOrbit V (T : Subgroup G)
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let J := internalSection U W
    let f := internalHom M U hn
    ∃ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component ∧ A ∈ QhatStar ρ ∧
      pCore 2 (internalActionImage M U hn) = ⊥ ∧
      (A.comap f ≤ (centralizer (W : Set G)).subgroupOf M ∨
        actionRatio (subspaceImageRepresentation ρ J) (restrictedSubgroup ρ J A) < 2 ∨
        ((A.comap f ⊓ (centralizer (W : Set G)).subgroupOf M).map f = ⊥ ∧
          J ⊔ fixedSpace ρ A = ⊤)) ∧
      rank ((A.comap f ⊓ (centralizer (W : Set G)).subgroupOf M).map f) +
        rank (restrictedSubgroup ρ J A) = rank A ∧
      fixedCodim ρ ((A.comap f ⊓ (centralizer (W : Set G)).subgroupOf M).map f) +
        (rank W - rank (W ⊓ centralizer (((A.comap f).map M.subtype : Subgroup G) : Set G))) ≤
          2 * rank A := by
  let := D.normalizerOrbit_elementary h.toHypothesis1221
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let W := componentOrbit V (T : Subgroup G)
  let hn := le_normalizer_componentOrbit V M
  have hWU : W ≤ U := by
    apply iSup_conjugates_le_of_le_normalizer V T U (le_componentOrbit V M)
    exact D.sylow_normalizes_component.trans hn
  obtain ⟨A,hAS,hA,_⟩ := D.exists_normalizer_starred_in_sylow_of_many h hmany
  obtain ⟨hr,hb⟩ := internal_starred_section_budget T M U W hn D.sylow_normalizes_component
    (le_normalizer_componentOrbit V T) hWU hAS hA
  rw [internalSection_fixedCodim M U W hn hWU A
    (hAS.trans (internalSylow_section_stable T M U W hn D.sylow_normalizes_component
      (le_normalizer_componentOrbit V T)))] at hb
  exact ⟨A,hAS,hA,D.normalizerActor_twoCore_eq_bot h.toHypothesis1221,
    internal_starred_section_alternatives T M U W hn D.sylow_normalizes_component
      (le_normalizer_componentOrbit V T) hWU hAS hA,
    hr,hb⟩

/-- The D.3.19 implication on the original W inside U. Noncentral action
and nontrivial centralizer image are the surviving structural premises;
this theorem does not claim D.3.13 or D.3.18. -/
theorem normalizer_starred_sylow_section_strict
    (D : ChosenModule T L V) (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) :
    letI := D.normalizerOrbit_elementary h
    let M := normalizer (L : Set G)
    let U := componentOrbit V M
    let W := componentOrbit V (T : Subgroup G)
    let hn := le_normalizer_componentOrbit V M
    let ρ := UniqueFactor.imageRepresentation M U hn
    let f := internalHom M U hn
    ∀ A : Subgroup (internalActionImage M U hn),
      A ≤ internalSylow T M U hn D.sylow_normalizes_component → A ∈ QhatStar ρ →
      (¬ A.comap f ≤ (centralizer (W : Set G)).subgroupOf M) →
      (A.comap f ⊓ (centralizer (W : Set G)).subgroupOf M).map f ≠ ⊥ →
      actionRatio (subspaceImageRepresentation ρ (internalSection U W))
        (restrictedSubgroup ρ (internalSection U W) A) < 2 := by
  let := D.normalizerOrbit_elementary h
  let M := normalizer (L : Set G)
  let U := componentOrbit V M
  let W := componentOrbit V (T : Subgroup G)
  let hn := le_normalizer_componentOrbit V M
  dsimp only
  intro A hAS hA hm hk
  have hWU : W ≤ U := by
    apply iSup_conjugates_le_of_le_normalizer V T U (le_componentOrbit V M)
    exact D.sylow_normalizes_component.trans hn
  exact internal_starred_section_strict T M U W hn D.sylow_normalizes_component
    (le_normalizer_componentOrbit V T) hWU hAS hA hm hk

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
