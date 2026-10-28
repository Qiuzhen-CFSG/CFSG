module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixA2Geometry
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixContainedRanks
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixContainedFusion
public import CFSG.Quasithin.Chapter12.Section07.Preliminaries.WeakClosure

/-!
# Weak closure in the original contained triple-six branch

The actual A₂ geometry supplies a full-weight point in its common
commutator space. The original contained-centralizer hypothesis transfers
to this point, so the proved fusion uniqueness and numerical parameters
force every conjugate of U inside T to centralize U. The whole zeroth
weak closure therefore lies in the literal O₂(KT); weak closure and the
original local uniqueness theorem control its full ambient normalizer.

Source: Aschbacher--Smith12.7.11, printed p.843.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The complete original weak-closure conclusion, with its actual
two-core containment and full ambient normalizer bound. -/
theorem original_tripleSix_contained_weakClosure
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (contained : centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    let := D.elementary
    indexedWeakClosure U (T : Subgroup G) 0 ≤
        (T : Subgroup G) ⊓ centralizer (U : Set G) ∧
      indexedWeakClosure U (T : Subgroup G) 0 ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      0 < globalW U (T : Subgroup G) ∧
      normalizer (indexedWeakClosure U (T : Subgroup G) 0 : Set G) ≤
        normalizer (K : Set G) := by
  let := D.elementary
  obtain ⟨V2,t2,ht2,ht2V,hweight,hgeometry⟩ := original_tripleSix_a2_geometry h structural D a
  let c := tripleSixPointCoordinates D a
  have ht20 : (c t2).toAdd ≠ 0 := by
    intro hz
    exact ht2 (c.injective (show c t2 = c 1 from hz.trans c.map_one.symm))
  have heven2 : 2 ∣ (centralizer ({(t2 : G)} : Set G)).relIndex K := by
    have hc := Hexacode.evenAction_orbit_card (c t2).toAdd ht20
    rw [tripleSixPoint_orbit_card D a t2] at hc
    have hn : hammingNorm (c t2).toAdd.val ≠ 4 := by rw [hweight]; decide
    rw [if_neg hn] at hc
    exact hc ▸ (by norm_num : 2 ∣ 18)
  have hcontained2 := original_tripleSix_full_weight_centralizer_le
    D a t ht heven contained t2 hweight
  have hunique := (original_tripleSix_contained_fusion
    h structural D a t2 ht2 heven2 hcontained2).2.1
  obtain ⟨hr,hs⟩ := original_tripleSix_contained_rank_parameters
    h structural D a t ht heven contained
  have hTU := ((structural K h).2.2 U D).1
  obtain ⟨hW,hw⟩ := Preliminaries.weakClosure_zero_centralizes
    U (T : Subgroup G) V2 t2 ht2V hTU hr hs hgeometry hunique
  have hc : (T : Subgroup G) ⊓ centralizer (U : Set G) =
      (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
    have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      h.simpleQTKE T h.maximal_faithful.1
    have ho : componentOrbit U (T : Subgroup G) = U :=
      le_antisymm (iSup_conjugates_le_of_le_normalizer U T U le_rfl hTU)
        (le_componentOrbit U T)
    have he := (D.fundamentalSetup h.toHypothesis1221).sylow_centralizer_module hu
    rw [D.fundamentalSetup_module,ho] at he
    simpa only [Chapter3.Section02.localJoin,D.localOrbit_eq] using he
  have hWQ := hW.trans_eq hc
  refine ⟨hW,hWQ,hw,?_⟩
  apply D.normal_subgroup_normalizer_le h.toHypothesis1221
    ((indexedWeakClosure_le U (T : Subgroup G) 0).trans le_sup_right)
  · exact fun he => D.ne_bot (bot_unique ((self_le_weakClosure_zero D.le_sylow).trans_eq he))
  · have hJQ : K ⊔ (T : Subgroup G) ≤
        normalizer ((K ⊔ (T : Subgroup G)).pCoreIn 2 : Set G) :=
      (K ⊔ (T : Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply weakClosure_weakly_closed
    exact ((map_mono hWQ).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (hJQ hg))).trans (hc.symm.le.trans inf_le_left)

end CFSG.Quasithin.Chapter12.Section07
