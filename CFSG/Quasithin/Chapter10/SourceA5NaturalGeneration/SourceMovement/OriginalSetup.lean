module

public import CFSG.Quasithin.Chapter3.Section01.Source318Movement
public import CFSG.Quasithin.Chapter10.SourceThompsonControl

/-!
# The original Thompson movement in 10.2.2

For an original H in H*(T,M), the source hypothesis [Z,H] ≠ 1 excludes
Z ≤ Z(H). The genuine qrc configuration of the Fundamental Setup then
applies 3.1.8(3) to force J(T) to move the original module V. The existing
faithful-action argument gives L₀ = [L₀,J(T)] and the FF-module conclusion.

All uniqueness and earlier-source inputs are discharged for the complete
known-simple catalogue. This result retains the original setup and chosen
comparison subgroup, and requires neither a full fixed layer nor a new seed.
Source: Aschbacher--Smith 10.2.2(1), printed p.744, citing 3.1.8(3), p.576.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original nontrivial omega-center commutator forces Thompson movement. -/
theorem source_hstar_thompson_moves_of_omega_commutator
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hq := D.qrcHypotheses hu hH
  apply hq.thompson_moves_of_noncentral_omega D.simpleQTKE
    (D.lemma_3_2_3_uniqueness hu).1 (D.lemma_3_2_3_uniqueness hu).2.2 D.module_ne_bot
  intro hz
  apply hZH
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro z hzZ h hh
  obtain ⟨zH, hzH, rfl⟩ := hz hzZ
  exact congrArg H.subtype (mem_center_iff.mp hzH ⟨h, hh⟩)

/-- The commutator assertion in original 10.2.2(1). -/
theorem source_hstar_actor_eq_thompson_commutator
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    localOrbit T L = ⁅localOrbit T L, elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  exact D.actor_eq_commutator_of_thompson_not_centralizes hu
    (source_hstar_thompson_moves_of_omega_commutator D hH hZH)

/-- Both original algebraic consequences of the moving-Thompson branch. -/
theorem source_hstar_thompson_movement_consequences
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    letI := D.module_elementary
    localOrbit T L = ⁅localOrbit T L, elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      Representation.BinaryOffender.IsFFModule
        (ChapterD.UniqueFactor.imageRepresentation (localJoin T L) D.moduleSubgroup
          D.join_normalizes_module) := by
  let := D.module_elementary
  exact ⟨source_hstar_actor_eq_thompson_commutator D hH hZH,
    D.module_isFF_of_thompson_not_centralizes
      (source_hstar_thompson_moves_of_omega_commutator D hH hZH)⟩

end CFSG.Quasithin.Chapter10
