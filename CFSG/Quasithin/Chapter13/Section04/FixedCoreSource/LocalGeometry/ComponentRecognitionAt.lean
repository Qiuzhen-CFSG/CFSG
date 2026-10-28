module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentCoveredFiveAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentNonsplitAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.AugmentationSelectionAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentRecognition

/-!
# Guarded recognition at every original escaping point

Reduce the actual 13.3.2 component list: the complete A₅ argument excludes
that row in both original covering cases, 13.3.16 excludes the unitary row,
and nonzero fixed space excludes the covered A₆ row. In the remaining
covered case small-quotient minimality and the genuine earlier natural
module clause mark the entire moved omega orbit over the literal central
core quotient. The linear-three and ordinary A₆ alternatives are retained.

ComponentCoveredNaturalAt eliminates the remaining covered natural row and
constructs the original-module application at each escaping point separately.
Linear-three geometry, amalgam and recognition assembly remain required, as
do the genuine earlier-source producers.
The universal APIs are preserved; only same-G,T structural facts are used.
Source: Aschbacher--Smith 13.3.2(3,5),13.3.16,13.4.10(1--5), pp.885,894,907--909.
The binary projective-linear transport retains LICENSES/ATLAS.txt attribution.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher NoncentralChiefRefinement
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}
open Section03.Noncentrality.SupercriticalSource
open Section08.TransvectionRecognition.Component.ModelExtension
open ChapterB.QuasisimpleSource Chapter1.Section02.LocalModels

/-- Reduce the original component list, retaining the literal marking in the fixed-free covered row. -/
theorem selected_component_recognition_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
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
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) ∨
    (IsAlternatingCover (K ⧸ pCore 2 K) 6 ∧
      let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      ∃ DK : ChosenModule T K U,
        U ⊓ centralizer (K : Set G) = ⊥ ∧
        U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
          (K ⊔ (T : Subgroup G)).subtype,K⁆ ∧
        ∃ q : (K ⧸ centralCore K) ≃* alternatingGroup (Fin 6),
          ∃ e : U ≃* Multiplicative (BinaryPermutation.natural (Fin 6)),
            ∀ (k : K) (v : U),
              (e (U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
                BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
                  (q (QuotientGroup.mk' (centralCore K) k)) (e v).toAdd) := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  rcases (h1332 K hfK).2 with h5 | h3 | h6 | hc | hu
  · obtain ⟨eK⟩ := h5
    exact (five_excluded_of_largeDistance_at hl h₀ h structural D m h1332 five
      z hzT hzL hK.1 hKN hKM hfK eK).elim
  · obtain ⟨F,_,_,hF,⟨eK⟩⟩ := h3
    let := Fintype.ofFinite F
    let a : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
      (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
    exact Or.inl ⟨(eK.trans (Atlas.fieldEquivPSL 3 a)).trans Matrix.PSL3Two.equiv.symm⟩
  · exact Or.inr (Or.inl h6)
  · have hcc : Nat.card (center (K ⧸ pCore 2 K)) = 3 := by
      obtain ⟨_,⟨e⟩,_⟩ := hc
      rw [Nat.card_congr e.toEquiv]
      simp
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    by_cases hfix : U ⊓ centralizer (K : Set G) = ⊥
    · have hcard : Nat.card (K ⧸ pCore 2 K) = 1080 := by
        obtain ⟨_,⟨e⟩,⟨q⟩⟩ := hc
        rw [card_eq_card_quotient_mul_card_subgroup (center (K ⧸ pCore 2 K)),
          Nat.card_congr e.toEquiv,Nat.card_congr q.toEquiv,nat_card_alternatingGroup]
        norm_num
      obtain ⟨⟨DK⟩,hU⟩ := component_chosen_of_small_quotient_at h₀ h structural m hzT hz1
        hK.1 h1332 hKN hKM hfK (Or.inr (Or.inr hcard))
      obtain ⟨a⟩ := covered h₀ K hfK hc U DK hfix
      exact Or.inr (Or.inr ⟨hc,DK,hfix,hU,
        natural_marking_of_faithful_six_action DK (component_quotient_quasisimple h1332 hfK) a⟩)
    · exact (covered_component_excluded_of_source_fixed_at h₀ h structural D m h1332 fixed
        hindex z hzT hzL hK hKN hKM hfK hcc hfix).elim
  · exact (selected_unitary_excluded h₀ h13316 hfK hu).elim

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
