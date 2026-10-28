module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.GroupTheory.TwoLocalUniquenessControl.NormalSubgroups
/-!
# Normalizer control in the original Section 12.2 setup

The actual T-normalized maximal local component has unique maximal two-local
normalizer by the proved A/C source theorem. Its join with T has characteristic
two. Consequently every nontrivial subgroup normal in that join has its full
ambient normalizer inside N_G(L). A chosen module supplies the required
T-normalization directly, with the same original L and T.

This constructs the uniqueness input used for the covered L₀ in
Aschbacher--Smith 13.2.2(9), printed p.878; no module classification is used.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem Hypothesis1221.normal_subgroup_normalizer_le
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    {B : Subgroup G} (hB : B ≤ L ⊔ (T : Subgroup G)) (hne : B ≠ ⊥)
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer (B : Set G)) :
    normalizer (B : Set G) ≤ normalizer (L : Set G) := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    h.simpleQTKE T h.maximal_faithful.1
  have he : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl hTL)
      (le_componentOrbit L T)
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ⊔ (T : Subgroup G) ≤ N →
      N = normalizer (L : Set G) := by
    simpa only [he] using hu.normalizer_unique
  have hchar : HasCharacteristicTwo (L ⊔ (T : Subgroup G) : Subgroup G) :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)
      ⟨h.maximal_faithful.1.1.2.2, fun x hx => (le_sup_right : (T : Subgroup G) ≤ L ⊔ (T : Subgroup G)) hx⟩)
  exact normalizer_le_of_characteristic_two_unique hchar huniq hB hne hn

namespace ChosenModule
variable {V : Subgroup G} (D : ChosenModule T L V)
include D

theorem normal_subgroup_normalizer_le (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {B : Subgroup G} (hB : B ≤ L ⊔ (T : Subgroup G)) (hne : B ≠ ⊥)
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer (B : Set G)) :
    normalizer (B : Set G) ≤ normalizer (L : Set G) :=
  h.normal_subgroup_normalizer_le D.sylow_normalizes_component hB hne hn
end ChosenModule
end CFSG.Quasithin.Chapter12.Section02
