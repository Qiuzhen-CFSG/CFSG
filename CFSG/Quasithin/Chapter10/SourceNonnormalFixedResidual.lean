module

public import CFSG.Quasithin.Chapter3.Section02.FundamentalActor
public import CFSG.Quasithin.Chapter4.Section01.Maximality
public import CFSG.Quasithin.Chapter4.Section04.PerfectCentralizer
public import Theory.GroupTheory.CComponent.SectionKernelCover
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The individual fixed residual in the original nonnormal pair

An actor centralizing L₀/O₂(L₀) also centralizes the original component's
quotient L/O₂(L): inside M, uniqueness of C-component lifting reflects
normalization from the ambient two-core quotient. For an odd actor B,
the literal residual C_L(B)^∞ consequently covers L modulo O₂(L).
Normalizing this cover inside M would normalize L. Thus an actor retaining
the original nontrivial orbit cannot normalize the fixed residual.

This is the contradiction endpoint of the nonnormal covering argument in
Aschbacher–Smith 4.2.12–13 and 4.4.5–6 (combined manuscript, 1 March 2004,
printed pp.609–610 and 620), for the actual Chapter 10 setup. It does not
assert the earlier classification consequence forcing residual normality
or the resulting covering uniqueness and Hall placement.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise

namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {K : GroupClass}
  {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)

include D in
/-- Centralizing the full orbit quotient centralizes each original component quotient. -/
theorem source_orbit_sectionCentralizer_le_component :
    sectionCentralizer (localOrbit T L) ≤ sectionCentralizer L := by
  let M := D.maximalLocal
  let X := localOrbit T L
  let C := sectionCentralizer X
  have hCM : C ≤ M := (le_sectionCentralizer_iff C X).mp le_rfl |>.1
  have hLM : L ≤ M := (le_componentOrbit L T).trans X.le_normalizer
  have hc : ⁅C,L⁆ ≤ M.pCoreIn 2 :=
    ((commutator_mono le_rfl (le_componentOrbit L T)).trans
      ((le_sectionCentralizer_iff C X).mp le_rfl).2).trans
        (pCoreIn_mono_of_normalizes X.le_normalizer le_rfl)
  have hcM : ⁅C.subgroupOf M,L.subgroupOf M⁆ ≤ pCore 2 M := by
    apply (map_le_map_iff_of_injective M.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hCM,map_subgroupOf_eq_of_le hLM]
    exact hc
  obtain ⟨hn,hq⟩ := section_kernel_controls_cComponent D.component_in_maximalLocal hcM
  apply (le_sectionCentralizer_iff C L).mpr
  constructor
  · rw [←subgroupOf_normalizer_eq hLM] at hn
    intro c hc
    exact hn (show (⟨c,hCM hc⟩ : M) ∈ C.subgroupOf M from hc)
  · have hmap := map_mono (f := M.subtype) hq
    rw [map_commutator,map_subgroupOf_eq_of_le hCM,map_subgroupOf_eq_of_le hLM,
      map_pCoreIn_of_injective 2 _ _ M.subtype_injective,map_subgroupOf_eq_of_le hLM] at hmap
    exact hmap

include D in
/-- The individual fixed residual covers the original component quotient. -/
theorem source_component_oddActor_cover
    (B : Subgroup G) (hB : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) :
    (L : Set G) =
      ((solvableResidual (L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (L ⊓ centralizer (B : Set G)).subtype : Set G) * (L.pCoreIn 2 : Set G) := by
  let := Chapter1.mem_L_isPerfect D.maximal.1
  exact perfect_centralizer_cover L B
    (hB.trans (source_orbit_sectionCentralizer_le_component D)) hodd

/-- Normalizing any literal cover inside M normalizes the original component. -/
theorem source_component_cover_normalizer {A : Subgroup G} (hAL : A ≤ L)
    (hcover : (L : Set G) ⊆ (A : Set G) * (L.pCoreIn 2 : Set G)) :
    D.maximalLocal ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  let M := D.maximalLocal
  have hLM : L ≤ M := (le_componentOrbit L T).trans (localOrbit T L).le_normalizer
  have hAM : A ≤ M := hAL.trans hLM
  have hc : (L.subgroupOf M : Set M) ⊆
      (A.subgroupOf M : Set M) * ((L.subgroupOf M).pCoreIn 2 : Set M) := by
    intro l hl
    obtain ⟨a,ha,c,hc,he⟩ := hcover hl
    refine ⟨⟨a,hAM ha⟩,ha,⟨c,hLM (pCoreIn_le 2 L hc)⟩,?_,Subtype.ext he⟩
    rw [pCoreIn_subgroupOf 2 L M hLM]
    exact hc
  have hn := normalizer_cover_le_component_normalizer D.component_in_maximalLocal
    (comap_mono hAL) hc
  change normalizer (A.subgroupOf M : Set M) ≤ normalizer (L.subgroupOf M : Set M) at hn
  rw [←subgroupOf_normalizer_eq hAM,←subgroupOf_normalizer_eq hLM] at hn
  intro m hm
  exact hn (show (⟨m,hm.1⟩ : M) ∈ (normalizer (A : Set G)).subgroupOf M from hm.2)

/-- The fixed component residual cannot be normalized by an actor retaining
the original nontrivial orbit. Thus the normality consequence sought from
C.4.8 in the nonnormal branch of 4.2.13 gives a contradiction here. -/
theorem source_nonnormal_fixedResidual_not_normalized
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hB : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B))
    (I : Subgroup G) (hIM : I ≤ D.maximalLocal)
    (horbit : componentOrbit L I = localOrbit T L) :
    ¬ I ≤ normalizer
      ((solvableResidual (L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (L ⊓ centralizer (B : Set G)).subtype : Set G) := by
  intro hi
  have hIL : I ≤ normalizer (L : Set G) :=
    (le_inf hIM hi).trans (source_component_cover_normalizer D
      ((map_subtype_le _).trans inf_le_left) (source_component_oddActor_cover D B hB hodd).subset)
  have he : localOrbit T L = L := horbit.symm.trans
    (le_antisymm (iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl hIL)
      (le_componentOrbit L I))
  apply hn
  have hT := le_normalizer_componentOrbit L T
  change (T : Subgroup G) ≤ normalizer (localOrbit T L : Set G) at hT
  rwa [he] at hT
end CFSG.Quasithin.Chapter10
