module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ReciprocalSixCenter
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ReciprocalCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentRecognition
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentCoveredNatural

/-!
# Mixed reciprocity for the original linear amalgam

Select a component of the original escaping point centralizer, apply the
source recognition theorem, and exclude the covered natural row. The checked
linear-three and ordinary A₆ reciprocal arguments then prove commutation
for the original conjugator and both literal O₂(L₂T) containments.
No selected component or quotient recognition is supplied as a premise.

The nonsolvability premise concerns this point only. Universal escaping
nonsolvability is still needed for the uniqueness and final graph argument.
The product alternative is proved in ProductMixed and the source pair is
assembled in SourceReciprocity. Product reciprocity in 13.4.16 and the graph
and terminal assembly remain separate obligations of this source proof. All earlier-source inputs retain their existing producers.
Source: Aschbacher–Smith 13.4.13 and 13.4.15, printed pp.911–912.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V A B : Subgroup G}

/-- Complete the selected component recognition by excluding the covered natural row. -/
theorem selected_component_ordinary_or_linear
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hKN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T) :
    Nonempty ((K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) := by
  rcases selected_component_recognition hl h₀ h structural D m h1332 fixed five covered
      h13316 hindex z hzT hzL hK hKN hKM hfK with hlin | hsix | hc
  · exact Or.inl hlin
  · exact Or.inr hsix
  · obtain ⟨hcover,DK,_,_,q,e,he⟩ := hc
    have hcard : Nat.card (center (K ⧸ pCore 2 K)) = 3 := by
      obtain ⟨_,⟨c⟩,_⟩ := hcover
      rw [Nat.card_congr c.toEquiv]
      simp
    exact (covered_natural_component_excluded h₀ h structural D m h1332
      z hzT hzL hK hKN hKM hfK hcard DK q e he).elim

/-- The linear alternative of original 13.4.15, with component selection discharged. -/
theorem original_linear_pair_mixed_commute
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (h1338 : ∀ H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G),
      ∀ Y : Subgroup G, Y ≤ H → H ≤ normalizer (Y : Set G) →
        IsPPerfect 2 Y → Y ≤ normalizer (L : Set G) → IsPiGroup twoThreePrimes Y)
    (hlin : Solvable.LinearAmalgamConclusion T (A ⊔ B))
    (eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6))
    (hM : normalizer (L : Set G) = L ⊔ (T : Subgroup G))
    (hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hTW : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hB : B = (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hAz : A ≤ centralizer ({z.val} : Set G))
    (hnonsolv : ¬ Group.IsSolvable (centralizer ({z.val} : Set G))) :
    let X := A ⊔ B
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    ∀ g : G, U.conjBy g ≤ B.pCoreIn 2 → V ≤ (B.pCoreIn 2).conjBy g →
      ⁅V,U.conjBy g⁆ = ⊥ := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G) := by
    intro hc
    have hBM : B ≤ normalizer (L : Set G) := by rw [hB,hM]; exact inf_le_left
    exact hout (sup_le (hAz.trans hc) hBM)
  obtain ⟨K,hK,hfK,_,hKN,_,hKM,_⟩ :=
    exists_escaping_component h₀ h structural m h1332 h1338 hzT hz1 hzout hnonsolv
  rcases selected_component_ordinary_or_linear hl h₀ h structural D m h1332 fixed
      five covered h13316 hindexL z hzT hzL hK hKN hKM hfK with model | model
  · obtain ⟨eK⟩ := model
    exact original_linear_pair_mixed_commute_of_selected_linear hl h₀ h structural modules
      D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 fixed hlin
      eL hM hZV W hW hTW hB hfusion z hzT hzL hAz hK.1 hKN hKM hfK eK
  · obtain ⟨eK⟩ := model
    exact original_linear_pair_mixed_commute_of_selected_six h₀ h structural modules
      D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres h1332 fixed hlin
      eL hM hZV W hW hTW hB hfusion z hzT hzL hAz hK hKN hKM hfK eK

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
