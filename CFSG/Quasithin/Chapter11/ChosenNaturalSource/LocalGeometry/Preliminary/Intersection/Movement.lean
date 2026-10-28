module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.FixedComplete
public import CFSG.Quasithin.Chapter3.Section01.Source318Movement
public import Theory.GroupTheory.PGroup.IrreducibleOmegaCore
public import Theory.GroupTheory.TINormalizerControl
/-!
# A moving H-star intersection forces the Thompson commutator

The original Sylow-invariant seed meets Ω₁Z(T). Its TI property makes a
comparison subgroup centralizing Ω₁Z(T) normalize the seed on intersection
with M. Thus a moving intersection gives the noncentral branch of 3.1.8(3).
The original FSU commutator theorem then gives L = [L,J(T)], with its
common-normal and uniqueness premises discharged.

Source: Aschbacher--Smith, 11.0.3(5), printed p.760, using 3.1.8(3).
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Stellmacher
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

theorem seed_meets_omegaCenter : V ⊓ omegaOneCenterAmbient (T : Subgroup G) ≠ ⊥ := by
  have he : omegaCenterIn (T : Subgroup G) = omegaOneCenterAmbient (T : Subgroup G) := by
    ext x
    rw [mem_omegaCenterIn_iff, mem_omegaOneCenterAmbient_iff]
    tauto
  rw [← he]
  exact inf_omegaCenterIn_ne_bot_of_normalized_twoGroup V T D.le_sylow T.isPGroup'
    S.sylow_normalizes D.ne_bot

theorem omega_not_central_of_intersection_moves {H : Subgroup G}
    (hmove : ¬ H ⊓ normalizer (L : Set G) ≤ normalizer (V : Set G)) :
    ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
  intro hZ
  apply hmove
  have hc : H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
    intro h hh z hz
    obtain ⟨w, hw, rfl⟩ := hZ hz
    exact (congrArg Subtype.val ((mem_center_iff.mp hw) ⟨h, hh⟩)).symm
  exact (le_inf inf_le_right (inf_le_left.trans
    (hc.trans (centralizer_le (show V ⊓ omegaOneCenterAmbient (T : Subgroup G) ≤
      omegaOneCenterAmbient (T : Subgroup G) from inf_le_right))))).trans
    (inf_centralizer_le_normalizer_of_trivial_intersections (seed_ti D S)
      (seed_meets_omegaCenter D S) inf_le_left)

theorem thompson_commutator_of_intersection_moves {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hmove : ¬ H ⊓ normalizer (L : Set G) ≤ normalizer (V : Set G)) :
    L = ⁅L, elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  let F := D.fundamentalSetup S.source.toHypothesis1221
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    S.source.simpleQTKE T S.source.maximal_faithful.1
  obtain ⟨hM, _, huniq⟩ := F.lemma_3_2_3_uniqueness hu
  have hHF : H ∈ Chapter3.HStar (T : Subgroup G) F.maximalLocal := by
    change H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (Chapter3.Section02.localOrbit T L : Set G))
    rwa [D.localOrbit_eq]
  have hq := Chapter3.Section02.source_reduced_seed_qrc_hypotheses
    T (Chapter3.Section02.localOrbit T L) F.maximalLocal
    (Chapter3.Section02.localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
    F.simpleQTKE hM F.internal_actor_residual F.internal_actor_cases
    F.seedSpace F.homogeneous.isIrrPlus hHF
  have hn : F.moduleSubgroup ≠ ⊥ := S.unchanged_seed.symm ▸ D.ne_bot
  have hj := hq.thompson_moves_of_noncentral_omega F.simpleQTKE hM huniq hn
    (omega_not_central_of_intersection_moves D S hmove)
  have he := Chapter3.Section02.source_reduced_seed_thompson_commutator
    T (Chapter3.Section02.localOrbit T L) F.maximalLocal
    (Chapter3.Section02.localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
    F.simpleQTKE hM F.internal_actor_residual F.internal_actor_cases
    F.seedSpace F.homogeneous.isIrrPlus hj
  rwa [D.localOrbit_eq] at he
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
