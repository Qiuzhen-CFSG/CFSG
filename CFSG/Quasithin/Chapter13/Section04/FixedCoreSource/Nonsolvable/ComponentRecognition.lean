module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentLinearGeometry
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentNaturalResidual
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentCoveredFive
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# Selecting and marking every escaping component

At a selected component of C_G(z), the actual 13.3.2 list is reduced using
13.3.16 and the proved A₅ exclusion. Nonzero fixed space also excludes the
covered A₆ row. The remaining covered row is retained as an actual natural
module on the whole moved omega-orbit, with its central-core quotient and
conjugation formula. Its minimality follows from the small-quotient theorem.

All three resulting module types give Ω₁Z(T) = V ∩ Ω₁Z(T) of order four.
The final theorem constructs the component and this marking at any escaping
point from nonsolvability of that point's centralizer. In particular, it does
not assume recognition or transfer nonsolvability between different points.

The fixed-free natural covered clause of 13.3.2 and the original universal
13.3.16 implication are explicit earlier-source inputs, with producers
qt-d-1332-source and qt-d-13316-source. Earlier 13.3.8, structural and module
inputs retain their producers and final discharge with the fixed-core owner.
The fixed-free selected covered row still needs exclusion here; the new
UniversalComparison consumer exposes it as the sole obstruction to applying
the checked both-weight comparison at every escaping point.

Source: Aschbacher--Smith 13.3.2(3,5),13.3.16,13.4.5(1,3),13.4.10(1,4,5),
printed pp.885,894,897--898,907--909. The imported binary projective-linear
field transport retains the ATLAS attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
open Section08.TransvectionRecognition.Component.ModelExtension
open ChapterB.QuasisimpleSource Chapter1.Section02.LocalModels
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

/-- Convert the faithful natural action to the literal central-core quotient. -/
theorem natural_marking_of_faithful_six_action (DK : ChosenModule T K V)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (a : letI := DK.actionCentralizer_normal
      ChapterB.QuasisimpleSource.ActionEquiv DK.faithfulAction
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6))) :
    ∃ q : (K ⧸ centralCore K) ≃* alternatingGroup (Fin 6),
      ∃ e : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6)),
        ∀ (k : K) (v : V),
          (e (V.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
            BinaryPermutation.alternatingNaturalRepresentation (Fin 6)
              (q (QuotientGroup.mk' (centralCore K) k)) (e v).toAdd := by
  let := hqK
  let := DK.actionCentralizer_normal
  let f := a.groupEquiv.toMonoidHom.comp DK.coreToFaithful
  have hf : Function.Surjective f := a.groupEquiv.surjective.comp DK.coreToFaithful_surjective
  have hk : f.ker = center (K ⧸ pCore 2 K) := by
    have hh := IsQuasisimple.comap_center_of_surjective f hf
    have hz : center (alternatingGroup (Fin 6)) = ⊥ :=
      alternatingGroup.center_eq_bot (by simp)
    rw [hz] at hh
    exact hh
  let q := f.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := hf.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = centralCore K := by
    rw [← MonoidHom.comap_ker,hk]
  let e : (K ⧸ centralCore K) ≃* alternatingGroup (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
  let c := DK.spaceEquiv.symm.trans a.linearEquiv.toAddEquiv.toMultiplicative
  refine ⟨e,c,?_⟩
  intro k v
  obtain ⟨w,rfl⟩ := DK.spaceEquiv.surjective v
  have hv : V.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ (DK.spaceEquiv w) =
      DK.spaceEquiv (Multiplicative.ofAdd (DK.chosenAction k w.toAdd)) := by
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_apply_coe,DK.spaceEquiv_apply]
    have hw := DK.spaceEquiv_apply w.toAdd
    change (DK.spaceEquiv w).val = w.toAdd.val.toMul.val.val at hw
    rw [hw]
    rfl
  rw [hv]
  change a.linearEquiv (DK.spaceEquiv.symm (DK.spaceEquiv _)).toAdd =
    BinaryPermutation.naturalRepresentation (Fin 6)
      (e (QuotientGroup.mk' (centralCore K) k)).val
      (a.linearEquiv (DK.spaceEquiv.symm (DK.spaceEquiv w)).toAdd)
  simp only [DK.spaceEquiv.symm_apply_apply]
  exact a.intertwines (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf K) k) w.toAdd

/-- The fixed-free covered-row specialization of original 13.3.2(3).
This is an earlier-source input, with producer qt-d-1332-source. -/
@[expose] def OriginalCoveredNatural1332At (T : Sylow 2 G) (L : Subgroup G) : Prop :=
  Hypothesis1331 T L → ∀ K ∈ MainForward.faithfulLocalComponents T,
    IsAlternatingCover (K ⧸ pCore 2 K) 6 →
    ∀ U : Subgroup G, ∀ DK : ChosenModule T K U,
      letI := DK.actionCentralizer_normal
      U ⊓ centralizer (K : Set G) = ⊥ →
      Nonempty (ActionEquiv DK.faithfulAction
        (BinaryPermutation.alternatingNaturalRepresentation (Fin 6)))

/-- The original 13.3.16 input applies to this same selected component.
Its five-minimality clause is vacuous in the unitary row. -/
theorem selected_unitary_excluded
    (h₀ : Hypothesis1331 T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (hfK : K ∈ MainForward.faithfulLocalComponents T) :
    ¬ ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 3 := by
  intro hu
  have hc : Nat.card (K ⧸ pCore 2 K) = 6048 := by
    obtain ⟨F,_,_,J,hF,hJ,⟨e⟩⟩ := hu
    exact (Nat.card_congr e.toEquiv).trans
      (BenderSuzuki.MatrixGroups.HermitianForm.TernaryPerfectCover.card_projective J hF hJ)
  have hn : ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) := by
    rintro ⟨e⟩
    have hh := Nat.card_congr e.toEquiv
    rw [hc,nat_card_alternatingGroup] at hh
    norm_num at hh
  have hK₀ : Hypothesis1331 T K :=
    { h₀ with local_component := hfK
              five_minimal := fun he => (hn he).elim }
  exact h13316 K hK₀ hu

/-- Actual component recognition leaves only the two completed rows or the
fixed-free natural module of the covered A₆ row. The A₅ and unitary rows,
and the covered row with nonzero fixed space, are excluded internally. -/
theorem selected_component_recognition
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
    exact (five_excluded_of_largeDistance hl h₀ h structural D m h1332 five
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
      obtain ⟨⟨DK⟩,hU⟩ := component_chosen_of_small_quotient h₀ h structural m hzT hz1
        hK.1 h1332 hKN hKM hfK (Or.inr (Or.inr hcard))
      obtain ⟨a⟩ := covered h₀ K hfK hc U DK hfix
      exact Or.inr (Or.inr ⟨hc,DK,hfix,hU,
        natural_marking_of_faithful_six_action DK (component_quotient_quasisimple h1332 hfK) a⟩)
    · exact (covered_component_excluded_of_source_fixed h₀ h structural D m h1332 fixed
        hindex z hzT hzL hK hKN hKM hfK hcc hfix).elim
  · exact (selected_unitary_excluded h₀ h13316 hfK hu).elim

/-- Every selected component supplies the actual moved-module marking and
full central four-group, including the remaining covered natural branch. -/
theorem selected_component_marking_and_seed
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
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
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    ∃ DK : ChosenModule T K U,
      Nonempty (ComponentModuleAt DK z.val) ∧
      U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
        (K ⊔ (T : Subgroup G)).subtype,K⁆ ∧
      omegaOneCenterAmbient (T : Subgroup G) = V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  rcases selected_component_recognition hl h₀ h structural D m h1332 fixed five covered
      h13316 hindex z hzT hzL hK hKN hKM hfK with hlin | hsix | hc
  · obtain ⟨eK⟩ := hlin
    obtain ⟨DK,mark,_,_,_,_,_,hU,_,hZ,hcard,_⟩ := linear_component_geometry
      hl h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK.1 hKN hKM hfK eK
    exact ⟨DK,mark,hU,hZ,hcard⟩
  · obtain ⟨eK⟩ := hsix
    obtain ⟨DK,mark,hU,_,_,_,hZ,hcard,_⟩ := ordinary_six_component_geometry
      h₀ h structural modules D m h1332 fixed hindex z hzT hzL hK hKN hKM hfK eK
    exact ⟨DK,mark,hU,hZ,hcard⟩
  · obtain ⟨_,DK,_,hU,q,e,he⟩ := hc
    let mark : ComponentModuleAt DK z.val := .naturalSix q e he
    have hz1 : z ≠ 1 := fun he => hzL (congrArg Subtype.val he ▸ one_mem _)
    exact ⟨DK,⟨mark⟩,hU,full_seed_of_component_moved_module
      h₀ h structural m z hz1 hzT hindex hK.1 hKM DK mark⟩

/-- Apply selection and the module analysis at an arbitrary escaping point.
Nonsolvability belongs to this point; no conclusion about other points is inferred. -/
theorem exists_escaping_component_marking_and_seed
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (five : Section03.SourceCompletion.OriginalAlternatingFiveModules1332At T L)
    (covered : OriginalCoveredNatural1332At T L)
    (h13316 : ∀ A : Subgroup G, Hypothesis1331 T A →
      ¬ ClassicalGroup.IsPSU (A ⧸ pCore 2 A) 3 3)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1338 : ∀ H ∈ Chapter1.HOutside G (T : Set G) (normalizer (L : Set G) : Set G),
      ∀ Y : Subgroup G, Y ≤ H → H ≤ normalizer (Y : Set G) →
        IsPPerfect 2 Y → Y ≤ normalizer (L : Set G) → IsPiGroup twoThreePrimes Y)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hnonsolv : ¬ Group.IsSolvable (centralizer ({z.val} : Set G))) :
    ∃ K : Subgroup G,
      K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)) ∧
      K ∈ MainForward.faithfulLocalComponents T ∧
      K ∈ Chapter1.LStar G T ∧
      centralizer ({z.val} : Set G) ≤ normalizer (K : Set G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      ¬ K ≤ normalizer (L : Set G) ∧
      ¬ L ≤ normalizer (K : Set G) ∧
      let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
      ∃ DK : ChosenModule T K U,
        Nonempty (ComponentModuleAt DK z.val) ∧
        U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
          (K ⊔ (T : Subgroup G)).subtype,K⁆ ∧
        omegaOneCenterAmbient (T : Subgroup G) = V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
        Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  obtain ⟨K,hK,hfK,hstar,hKN,hTK,hKM,hLN⟩ :=
    exists_escaping_component h₀ h structural m h1332 h1338 hzT hz1 hzout hnonsolv
  exact ⟨K,hK,hfK,hstar,hKN,hTK,hKM,hLN,
    selected_component_marking_and_seed hl h₀ h structural modules D m h1332 fixed
      five covered h13316 hindex z hzT hzL hK hKN hKM hfK⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
