module
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceExclusion
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.TorusSections
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.SourceLocal
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.OddCore
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.ParabolicActions
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.MinimumGeometry

/-!
# The original component branches of E.6.11 at the source minimum

The intrinsic Borel and parabolic theorems construct a torus in the original
component. TorusSections proves its relative normal image and packages the
literal regular cyclic section. The alternative symplectic Borel has a
strictly larger escaping fixed subspace, contradicting source maximality.
Thus both ordinary-component branches directly construct the section used
by E.6.24–25, including the same Borel or root model used in factor counting.

At the full globalR minimum, maximality and local odd-core vanishing follow
from their source proofs. Only the source component sieve is retained by the
last consumer; its rank-one outcomes are excluded by the actual corank.
Source: Aschbacher–Smith, E.6.11(2–3) and E.6.25, printed pp.249–250,255.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
open Components LocalFactors Hyperplanes Hyperplanes.ComponentBalance
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- The Borel source torus supplies the literal E.6.24 input and local model. -/
theorem minimalRegularSection_of_borel
    (h : HypothesisE61 K T M V) (ho : pPrimeCore 2 (centralizer (U : Set G)) = ⊥)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hfixed : V ⊓ centralizer (L : Set G) = U)
    (hr : 1 < subgroupCorank V U)
    {n : ℕ} (b : BorelAlternative M V U L n) :
    Nonempty (MinimalRegularSection T M V U) := by
  have hn : n = subgroupCorank V U := by
    simpa only [actionCorank,hfixed] using b.dimension
  subst n
  have hVL := component_normalized_by_V h hU hL
  obtain ⟨S,hS⟩ := Components.component_sylow_intersection h hU hL
  obtain ⟨X,hX,_⟩ := BorelActions.conclusion_of_borelAlternative
    h hU hL b hr hVL rfl S hS
  have hgen : V = U ⊔ ⁅V,X⁆ := by
    simpa only [hX.displacement,hfixed,sup_comm] using (b.decomposition hr).1.symm
  have hdis : U ⊓ ⁅V,X⁆ = ⊥ := by
    simpa only [hX.displacement,hfixed,inf_comm] using (b.decomposition hr).2.1
  have hq : IsQuasisimple L := by
    let _ := hL.2.2
    exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hL.1)
  exact ⟨⟨L,X,⟨hL.1,hL.2.isCComponent⟩,
    component_not_le h (source_earlierLocalFacts h) hU hL,
    regularSection_of_torus h ho hU (Or.inl hL) hVL hfixed hgen hdis hr hX,
    hX.le_intersection.trans inf_le_left,hfixed,Or.inl hq,
    Or.inr (Or.inl ⟨hL,b,hX,hVL,S,hS⟩)⟩⟩

/-- Maximal escape excludes the Borel subcase and constructs the parabolic section. -/
theorem minimalRegularSection_of_symplectic
    (h : HypothesisE61 K T M V) (ho : pPrimeCore 2 (centralizer (U : Set G)) = ⊥)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hfixed : V ⊓ centralizer (L : Set G) = U)
    (hmax : ∀ W : Subgroup G, U < W → W ≤ V → centralizer (W : Set G) ≤ M)
    (hr : 1 < subgroupCorank V U)
    {n : ℕ} (s : SymplecticAlternative M V U L n) :
    Nonempty (MinimalRegularSection T M V U) := by
  have hcor : actionCorank V L = subgroupCorank V U := by rw [actionCorank,hfixed]
  rcases s.local_structure with ⟨_,hb⟩ | ⟨hp,hroot,hn⟩
  · rcases hb with ⟨_,A,hUA,hAV,_,hesc⟩ | ⟨_,hc⟩
    · exact (hesc (inf_le_right.trans (hmax A hUA hAV.le))).elim
    · rw [hcor] at hc
      omega
  · rw [hcor] at hn
    subst n
    obtain ⟨X,hX,hR,_⟩ := ParabolicActions.parabolic_torus_conclusion hr s hp hroot
    have hgen : V = U ⊔ ⁅V,X⁆ := by
      simpa only [hX.displacement,hfixed,sup_comm] using (s.decomposition hr).1.symm
    have hdis : U ⊓ ⁅V,X⁆ = ⊥ := by
      simpa only [hX.displacement,hfixed,inf_comm] using (s.decomposition hr).2.1
    have hq : IsQuasisimple L := by
      let _ := hL.2.2
      exact IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hL.1)
    exact ⟨⟨L,X,⟨hL.1,hL.2.isCComponent⟩,
      component_not_le h (source_earlierLocalFacts h) hU hL,
      regularSection_of_torus h ho hU (Or.inl hL) hroot.1 hfixed hgen hdis hr hX,
      hX.le_intersection.trans inf_le_left,hfixed,Or.inl hq,
      Or.inr (Or.inr ⟨hroot.1,hX,hp,hR⟩)⟩⟩

/-- At the actual minimum, the component branch produces the original section. -/
theorem component_regularSection_of_minimum
    (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hmin : (subgroupCorank V U : ℕ∞) = globalR V)
    (hr : 1 < subgroupCorank V U)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hsieve : (∃ n, BorelAlternative M V U L n) ∨
      (∃ n, SymplecticAlternative M V U L n) ∨ globalR V = 1) :
    Nonempty (MinimalRegularSection T M V U) := by
  have hmax := h.maximal_escape_of_minimum hmin
  have ho := h.oddCore_eq_bot_of_maximal_escape (source_earlierLocalFacts h) hU hmax hr
  have hfixed : V ⊓ centralizer (L : Set G) = U :=
    (fixedSpace_eq_of_maximal_escape hU.1 hmax hL.1
      (component_not_le h (source_earlierLocalFacts h) hU hL)).symm
  rcases hsieve with ⟨n,b⟩ | ⟨n,s⟩ | hone
  · exact minimalRegularSection_of_borel h ho hU hL hfixed hr b
  · exact minimalRegularSection_of_symplectic h ho hU hL hfixed hmax hr s
  · rw [hone] at hmin
    have he : subgroupCorank V U = 1 := by exact_mod_cast hmin
    omega

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction
