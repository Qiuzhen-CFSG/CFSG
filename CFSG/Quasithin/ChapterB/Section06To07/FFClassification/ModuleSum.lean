module

public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.MovedSection
public import Theory.Representation.BinaryOffender.ComponentSum

/-!
# The actual source component-module sum

Minimal best offenders and the earlier ratio-one recognition identify each
original Irr+ section with its full component moved space. Distinct components
centralize those sections by perfectness. The common-quotient theorem then
constructs the direct sum and preserves its original ambient permutation action.
This proves the module-sum step of B.6.9(2) once the selected sections have the
earlier source recognition; it makes no assertion that the whole ambient module
splits over its fixed space.

Source: Aschbacher–Smith, proof of B.6.9, printed pp.116–117, especially
case (a) and the distinct-component centralization step (1 March 2004).
-/

public section
open scoped DirectSum
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
variable {G V ι : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
  (L A : ι → Subgroup G) (W : ι → Submodule (ZMod 2) V)
  (hL : ∀ i, IsComponent G (L i)) (hinj : Function.Injective L)
  (hA : ∀ i, IsMinimalBestOffender ρ (A i)) (hW : ∀ i, IsIrrPlus ρ (L i) (W i))
  (hAW : ∀ i, A i ≤ subspaceStabilizer ρ (W i))
  (hgen : ∀ i, ⁅L i, A i⁆ = L i)
  (hq : ∀ i, quadraticRatio (subspaceImageRepresentation ρ (W i)) = 1)

include hA hW hAW hgen hq in
/-- Each original source section is its entire actual component moved space. -/
theorem component_sections_eq_moved :
    ∀ i, W i = subspaceCommutator ρ ⊤ (L i) :=
  fun i => (moved_section_of_ratio_one ρ (hA i) (hW i) (hAW i) (hgen i) (hq i)).1

include hL hinj hA hW hAW hgen hq in
/-- Distinct source components centralize each other's actual sections. -/
theorem component_sections_cross_centralize :
    ∀ i j, i ≠ j → W i ≤ fixedSpace ρ (L j) := by
  intro i j hij
  apply (subspaceCommutator_eq_bot_iff ρ (W i) (L j)).mp
  exact other_component_moved_eq_bot ρ (hL i) (hL j)
    (fun h => hij (hinj h.symm)) (hA i) (hW i) (hAW i) (hgen i) (hq i)

include hL hinj hA hW hAW hgen hq in
/-- B.6.9(2): independence in the original quotient, with no independence premise. -/
theorem component_section_images_independent :
    iSupIndep (fun i => (W i).map (fixedSpace ρ (⨆ j, L j)).mkQ) :=
  familyCentralQuotient_independent ρ L W
    (component_sections_cross_centralize ρ L A W hL hinj hA hW hAW hgen hq)

include hA hW hAW hgen hq in
/-- The sum is exactly the commutator space in the original ambient fixed-space quotient. -/
theorem component_section_images_span [(⨆ i, L i).Normal] :
    (⨆ i, (W i).map (fixedSpace ρ (⨆ j, L j)).mkQ) =
      subspaceCommutator (fixedQuotient ρ (⨆ j, L j)) ⊤ (⨆ i, L i) := by
  simp_rw [component_sections_eq_moved ρ L A W hA hW hAW hgen hq]
  rw [moved_fixedQuotient, subspaceCommutator_iSup_family, Submodule.map_iSup]

/-- The actual component quotients form the actual moved central quotient. -/
noncomputable def component_section_sum_equiv [DecidableEq ι] :
    (⨁ i, centralQuotient ρ (L i) (W i)) ≃ₗ[ZMod 2]
      centralQuotient ρ (⨆ i, L i) (subspaceCommutator ρ ⊤ (⨆ i, L i)) :=
  familyMovedCentralQuotientEquiv ρ L W
    (component_sections_cross_centralize ρ L A W hL hinj hA hW hAW hgen hq)
    (component_sections_eq_moved ρ L A W hA hW hAW hgen hq)

include hA hW hAW hgen hq in
/-- Original ambient conjugation permutes the sections without an extra action choice. -/
theorem component_sections_permuted {g : G} {i j : ι}
    (hg : (L i).map (MulAut.conj g).toMonoidHom = L j) :
    (W i).map (ρ g) = W j :=
  family_moved_permuted ρ L W
    (component_sections_eq_moved ρ L A W hA hW hAW hgen hq) hg

include hA hW hAW hgen hq in
/-- Full ambient conjugation acts on the same component images in the same quotient. -/
theorem component_section_images_permuted [(⨆ i, L i).Normal] {g : G} {i j : ι}
    (hg : (L i).map (MulAut.conj g).toMonoidHom = L j) :
    ((W i).map (fixedSpace ρ (⨆ j, L j)).mkQ).map (fixedQuotient ρ (⨆ j, L j) g) =
      (W j).map (fixedSpace ρ (⨆ j, L j)).mkQ :=
  family_central_images_permuted ρ L W
    (component_sections_eq_moved ρ L A W hA hW hAW hgen hq) hg

end CFSG.Quasithin.ChapterB
