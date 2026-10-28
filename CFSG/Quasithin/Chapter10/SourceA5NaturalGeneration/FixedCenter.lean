module
public import CFSG.Quasithin.Chapter10.SourceBaumannFixedCenter
/-!
# The common fixed-center step in the natural generation branch

The original uniqueness theorem forces the centralizer of every nontrivial
common fixed subgroup of Ω₁Z(T) into M. An H* overgroup escaping M therefore
has no common fixed center with L₀. A natural-action fixed-space containment
then removes the individual fixed center. No splitting of the original
central covers is assumed.

Source: Aschbacher–Smith10.2.3(4), printed p.746.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- The actual original orbit and H* have no common fixed Sylow-center element. -/
theorem source_hstar_common_fixed_center_eq_bot {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) ⊓ centralizer (H : Set G) = ⊥ := by
  by_contra hne
  let C := omegaOneCenterAmbient (T : Subgroup G) ⊓
    centralizer (localOrbit T L : Set G) ⊓ centralizer (H : Set G)
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hCT : C ≤ centralizer ((T : Subgroup G) : Set G) := by
    intro z hz t ht
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz.1.1).2.2 t ht
  have hCL : C ≤ centralizer (localJoin T L : Set G) := by
    apply le_centralizer_iff.mpr
    exact sup_le (le_centralizer_iff.mp (inf_le_left.trans inf_le_right))
      (le_centralizer_iff.mp hCT)
  have hN : normalizer (C : Set G) ≤ D.maximalLocal :=
    normalizer_le_of_unique_maximalTwoLocal (D.lemma_3_2_3_uniqueness hu).2.2
      ((omegaOneCenterAmbient_elementaryAbelian _).isPGroup.to_le
        (inf_le_left.trans inf_le_left)) hne
      ((le_centralizer_iff.mp hCL).trans (centralizer_le_normalizer (C : Set G)))
  exact hH.1.2 ((le_centralizer_iff.mp inf_le_right).trans
    ((centralizer_le_normalizer (C : Set G)).trans hN))

/-- Fixed-space containment from the natural action eliminates the H* fixed center. -/
theorem source_hstar_fixed_center_eq_bot_of_le {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hle : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) ≤
      centralizer (localOrbit T L : Set G)) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥ := by
  apply bot_unique
  rw [← source_hstar_common_fixed_center_eq_bot D hH]
  exact le_inf (le_inf inf_le_left hle) inf_le_right
/-- The natural fixed-space equality removes both original fixed centers. -/
theorem source_hstar_fixed_centers_eq_bot_of_eq {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (he : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G)) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥ ∧
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (H : Set G) = ⊥ := by
  have hh := source_hstar_fixed_center_eq_bot_of_le D hH (he.le.trans inf_le_right)
  exact ⟨he.symm.trans hh,hh⟩

end CFSG.Quasithin.Chapter10
