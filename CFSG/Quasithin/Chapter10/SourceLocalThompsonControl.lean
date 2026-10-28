module
public import CFSG.Quasithin.Chapter10.SourceThompsonControl

/-!
# Thompson control from the original local module

If J(T) centralizes V_T, the proved equality C_T(V_T)=O₂(L₀T) puts J(T)
inside that core. Thompson heredity identifies it with J(O₂(L₀T)), so
L₀T normalizes J(T). Uniqueness of the maximal two-local over L₀T then
controls N_G(J(T)) and N_G(Baum(T)).

This proves the centralizing branch of 10.2.1 directly from the local
module; equality with its full M-orbit is unnecessary for this branch.
Source: Aschbacher–Smith, 3.2.2(8), 3.2.10(1,8), and 10.2.1,
combined manuscript of 1 March 2004, printed pp.579,583,742.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D

/-- The local FSU module alone suffices for the Thompson normalizer bound. -/
theorem source_local_thompson_normalizer_le_of_centralizes
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G)) :
    normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ D.maximalLocal := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have he := elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G)
    ((T : Subgroup G) ⊓ centralizer (D.moduleSubgroup : Set G))
    (le_inf hJT hJ) inf_le_left
  rw [D.sylow_centralizer_module hu] at he
  have hn : localJoin T L ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
    rw [← he]
    exact ((localJoin T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (localJoin T L)
        (pCore 2 (localJoin T L)))).trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ _)
  have hT : (T : Subgroup G) ≠ ⊥ := fun ht =>
    D.module_ne_bot (bot_unique (D.module_le_sylow.trans_eq ht))
  exact normalizer_le_of_unique_maximalTwoLocal (D.lemma_3_2_3_uniqueness hu).2.2
    (T.isPGroup'.to_le hJT)
    (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup _ T.isPGroup' hT) hn

/-- The Baumann normalizer is controlled whenever J(T) centralizes V_T. -/
theorem source_local_baumann_normalizer_le_of_centralizes
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G)) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal := by
  have he := elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G)
    (ChapterB.baumann (T : Subgroup G))
    (ChapterB.elementaryAbelianMaxJ_le_baumann _) inf_le_left
  exact (normalizer_le_normalizer_elementaryAbelianMaxJ _).trans
    (he.symm ▸ source_local_thompson_normalizer_le_of_centralizes D hJ)

end CFSG.Quasithin.Chapter10
