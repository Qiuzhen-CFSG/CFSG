module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.NonsolvableAt.Nonsolvable.SourceContradiction
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.SolvableRecognitionAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentCoveredNaturalAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSixNormalizerAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentFullLinearAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.GeneralPairSourceAt

/-!
# Fixed-core recognition from the genuine preceding source inputs

Negating symplectic recognition makes every escaping omega-point centralizer
nonsolvable, by the constructed solvable implication. At an actual escaping
point the two surviving component rows give the ordinary initial quotient
and N_G(L)=LT. Repeat this argument at each reciprocal marked component to
construct its fusion and plane-amalgam inputs. The general pair theorem is
constructed separately. The guarded nonsolvable contradiction then applies.

All local 13.4 hypotheses are discharged on the original five-dimensional
module; only the preceding Chapter12/13.3 and natural large-distance inputs
remain. The variant for multiple maximal overgroups also constructs 12.2.13.
This is conditional source assembly, pending the independent producers of
those earlier inputs, rather than an unconditional assertion of 13.4.1.
Source: Aschbacher--Smith 13.4.1--17, printed pp.896--915.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private theorem applicability (h₀ : Hypothesis1331 T L) (h1332 : Source1332OneTwo T) :
    Hypothesis1223 KnownSimple.IsKnownSimple T L := by
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  exact h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
      h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)

/-- In a counterexample to symplectic recognition, construct the ordinary
initial quotient and full normalizer on every applicable marked core. -/
theorem ordinary_normalizer_of_not_symplectic_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (hnot : ¬ ClassicalGroup.IsPSp G 3 2) :
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
      normalizer (L : Set G) = L ⊔ (T : Subgroup G) := by
  obtain ⟨z,hz1,hzT,hzL,hout⟩ := exists_nonfixed_omega_escape_at h₀ h structural D m earlier
  have hnonsolv : ¬ Group.IsSolvable (centralizer ({z.val} : Set G)) :=
    fun hs => hnot (augmentation_solvable_recognition_at hl h₀ h structural modules D m
      h1332 fixed covered h13316 z hzT hzL hout hs)
  have hindex := original_omega_fixed_index_at h₀ h structural D m earlier
  obtain ⟨K,hK,hfK,_,hKN,_,hKM,_⟩ := augmentation_exists_escaping_component_at
    h₀ h structural m h1332 hzT (fun he => hz1 (Subtype.ext he)) hout hnonsolv
  rcases selected_component_rows_at hl h₀ h structural D m h1332 fixed five covered
      h13316 hindex z hzT hzL hK hKN hKM hfK with h3 | h6
  · obtain ⟨eK⟩ := h3
    have hL := (linear_component_geometry_at hl h₀ h structural modules D m h1332 fixed
      hindex z hzT hzL hK.1 hKN hKM hfK eK).choose_spec.2.1
    have hM := (linear_component_normalizer_supplement_at hl h₀ h structural modules D m
      h1332 fixed hindex z hzT hzL hK.1 hKN hKM hfK eK).2.2.1
    exact ⟨hL,hM⟩
  · obtain ⟨eK⟩ := h6
    obtain ⟨_,_,_,hL,_⟩ := ordinary_six_component_geometry_at h₀ h structural modules D m
      h1332 fixed hindex z hzT hzL hK hKN hKM hfK eK
    exact ⟨hL,(six_component_normalizer_supplement_at h₀ h structural modules D m
      h1332 fixed hindex z hzT hzL hK hKN hKM hfK eK).2.2.1⟩

/-- Assemble the original fixed-core implication with all local 13.4
premises constructed. The only remaining inputs are genuine earlier results. -/
theorem isPSp_of_original_fixed_core_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3) :
    ClassicalGroup.IsPSp G 3 2 := by
  classical
  by_contra hnot
  have h := applicability h₀ h1332
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  obtain ⟨m⟩ := coreMarking_of_faithful_core_action D h.quasisimple a
  have hns := original_universal_escaping_nonsolvable_at hl h₀ D hfixed structural modules
    h1332 fixed covered h13316 hnot
  have hi := original_omega_fixed_index_at h₀ h structural D m earlier
  have hM := (ordinary_normalizer_of_not_symplectic_at hl h₀ h structural modules earlier
    D m h1332 fixed five covered h13316 hnot).2
  have hlocal (A W : Subgroup G) (DA : ChosenModule T A W) (ma : CoreMarking DA)
      (hA : Hypothesis1331 T A) :=
    ordinary_normalizer_of_not_symplectic_at hl hA (applicability hA h1332)
      structural modules earlier DA ma h1332 (fun _ => fixed h₀) (fun _ => five h₀)
      (fun _ => covered h₀) h13316 hnot
  have hplane : ∀ (A W : Subgroup G) (DA : ChosenModule T A W) (ma : CoreMarking DA),
      Hypothesis1331 T A → Solvable.PlaneAmalgamSource1347 DA ma := by
    intro A W DA ma hA
    have hA12 := applicability hA h1332
    exact Amalgam.planeAmalgamSource1347_at hl hA hA12 structural modules DA ma h1332
      (fun _ => fixed h₀) (fun _ => covered h₀) h13316
      (original_omega_fixed_index_at hA hA12 structural DA ma earlier)
      (hlocal A W DA ma hA).2
  have hfusion : ∀ (A W : Subgroup G) (DA : ChosenModule T A W),
      CoreMarking DA → Hypothesis1331 T A → ∀ v : W, v ≠ 1 →
      ∀ w ∈ W, IsConj v.val w →
        ∃ n ∈ normalizer (W : Set G), MulAut.conj n v.val = w := by
    intro A W DA ma hA v _ w hw hc
    exact ordinary_core_normalizer_fusion_at hl hA (applicability hA h1332)
      structural DA ma earlier (hlocal A W DA ma hA).1.some v w hw hc
  obtain ⟨z,hz1,hzT,_,hout⟩ := exists_nonfixed_omega_escape_at h₀ h structural D m earlier
  exact false_of_universal_escaping_nonsolvable_at hl h₀ h structural modules D m
    h1332 fixed five covered h13316 hi hM hplane
    (Amalgam.pairAmalgamSource1347_at h₀ h structural D m h1332 fixed covered h13316 hi)
    hfusion hns z hz1 hzT hout

/-- In the actual multiple-overgroup branch, 12.2.13 is also constructed
from the structural and module inputs at G,T. -/
theorem isPSp_of_original_fixed_core_of_many_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3) :
    ClassicalGroup.IsPSp G 3 2 :=
  isPSp_of_original_fixed_core_at hl h₀ D hfixed structural modules
    (Chapter12.Section02.RecognitionSource.theorem12213_of_modules_of_many_at
      structural modules hmany) h1332 fixed five covered h13316

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
