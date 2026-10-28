module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.FixedModuleAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSeedAt
public import Theory.GroupTheory.ReducedNormal.SubspaceMinimality

/-!
# The selected component with nonzero fixed space at the original G,T

The two actual maximal normalizers supply Thompson generation of K.
Nontrivial fixed space makes the reduced moved module nonsplit, so the
existing B.5 construction supplies an Irr⁺ chosen module. The invariant
subgroup minimality theorem identifies it with the actual moved omega
orbit. Earlier 13.3.2 provides its whole augmentation marking. Its fixed
line has order two and is T-invariant, hence lies in Ω₁Z(T); ComponentSeedAt
identifies it with ⟨z⟩ and proves that the full omega center has order four.

The final application starts with the original chosen V and nonzero fixed
part, constructing the initial marking, Chapter 12 guard and omega index.
The selected component keeps its original centralizer, relative normality
and faithful-local conditions. No universal structural record, assumed
minimality, marking, Thompson-generation or full-seed premise is used.
The fixed-free component branches and final recognition remain separate
source obligations. Existing universal component APIs are unchanged.
Source: Aschbacher--Smith B.5.1(2), 13.3.2(3), 13.4.6(3), 13.4.10(4--5),
printed pp.99,885,899,907--909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Section03.Noncentrality.SupercriticalSource ChapterA.Section04
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L K V U : Subgroup G}
variable {D : ChosenModule T L V}
theorem component_moved_ne_bot_at
    {V : Subgroup G} {D : ChosenModule T L V}
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (m : CoreMarking D) (hKM : ¬ K ≤ normalizer (L : Set G)) :
    ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ ≠ ⊥ := by
  intro he
  have hKC := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
  apply hKM
  apply le_trans ?_ (fixed_generator_centralizer_at h structural D m
    ⟨m.constant.property,m.constant_fixed⟩
    (fun hh => m.constant_ne_one (Subtype.ext hh))).le
  exact hKC.trans (centralizer_le (Set.singleton_subset_iff.mpr
    (le_conjugateSpanBy _ _ (m.constant_mem_central_four_at h structural).2)))

theorem component_thompson_generation_at
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hHN : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T) :
    ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K := by
  have hTK := (h1332 K hfK).1
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hqK := component_quotient_quasisimple h1332 hfK
  have huni := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h₀.qtke T hstar
  have horb : componentOrbit K (T : Subgroup G) = K :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer K _ K le_rfl hTK)
      (le_componentOrbit K _)
  have hN : IsMaximalTwoLocal (normalizer (K : Set G)) := horb ▸ huni.normalizer_maximal
  have hM := h.source_normalizer_maximal_unique_at structural
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  have hout : Chapter3.HasMaximalOutside T (normalizer (K : Set G)) :=
    Chapter3.hasMaximalOutside_of_two_distinct hN hM.1 hTK D.sylow_normalizes_component
      (by intro he; exact hKM (he.symm ▸ K.le_normalizer))
  have hC : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
      normalizer (K : Set G) :=
    (centralizer_le (Set.singleton_subset_iff.mpr hzT)).trans hHN
  exact Chapter3.Section02.source_component_thompson_generation h₀.qtke T K hstar
    ((Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK).2
    hqK hTK hout hC

/-- Nonzero fixed vectors force minimality on the actual moved orbit and identify it
with the whole reduced moved subgroup. -/
theorem component_chosen_of_moved_fixed_at
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (m : CoreMarking D) {z : G}
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K)
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    Nonempty (ChosenModule T K U) ∧
      U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
        (K ⊔ (T : Subgroup G)).subtype,K⁆ := by
  let H := K ⊔ (T : Subgroup G)
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let R := (ReducedModule H).map H.subtype
  obtain ⟨_,_,_,_,hSQ⟩ := MainForward.localComponents_local_setup h₀.qtke T hfK.1
  have hred := component_moved_reduced h₀ hzT hz1 hKz hTK
  have hUH : U ≤ H :=
    (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy _ _)).trans
      (conjugateSpanBy_le
        ((show omegaOneCenterAmbient (T : Subgroup G) ≤ (T : Subgroup G) from
          fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).1).trans le_sup_right)
        (le_sup_left.trans H.le_normalizer))
  have hUR : U ≤ R := by
    have hh := map_mono (f := H.subtype) hred.le_reducedPSubgroup
    rwa [map_subgroupOf_eq_of_le hUH] at hh
  have hUU : ⁅U,K⁆ = U := component_moved_eq_commutator h₀ hzT hz1 hKz hTK
  have hUB : U ≤ ⁅R,K⁆ := hUU ▸ commutator_mono hUR le_rfl
  have hBfixed : ⁅R,K⁆ ⊓ centralizer (K : Set G) ≠ ⊥ := by
    intro he
    exact hfixed (bot_unique ((inf_le_inf_right _ hUB).trans he.le))
  have hlocal : Section03.Noncentrality.Diagonal.localGroup K ⊥ T = H := by
    change (K ⊔ ⊥) ⊔ (T : Subgroup G) = H
    rw [sup_bot_eq]
  have hmoved : Section03.Noncentrality.Diagonal.movedModule K ⊥ T = ⁅R,K⁆ := by
    unfold Section03.Noncentrality.Diagonal.movedModule
      Section03.Noncentrality.Diagonal.reducedModule
    rw [hlocal]
  obtain ⟨DK⟩ := Section03.SourceCompletion.containing_moved_module_chosen T K ⊥
    bot_le hTK (hlocal.symm ▸ hSQ)
    (hlocal.symm ▸ hfK.1.1)
    hqK hfK.2.2 hgen (hmoved.symm ▸ hBfixed)
  have DK' : ChosenModule T K ⁅R,K⁆ := hmoved ▸ DK
  have hn : K ≤ normalizer (U : Set G) := normalizer_commutator_ge_right _ _
  have hmin := Theory.GroupTheory.ReducedNormal.subspaceImage_eq_or_le_centralizer
    H K (show K ≤ H from le_sup_left) DK'.irrPlus.isIrrPlus U
    (by
      change U ≤ subspaceImage (K ⊔ (T : Subgroup G)) DK'.space
      rwa [DK'.image_eq]) hn
  change U = subspaceImage (K ⊔ (T : Subgroup G)) DK'.space ∨
    U ≤ centralizer (K : Set G) at hmin
  rw [DK'.image_eq] at hmin
  have he : U = ⁅R,K⁆ := hmin.resolve_right (by
    intro hc
    have hh := commutator_eq_bot_iff_le_centralizer.mpr hc
    rw [hUU] at hh
    exact component_moved_ne_bot_at h structural m hKM hh)
  refine ⟨?_,he⟩
  change Nonempty (ChosenModule T K U)
  rw [he]
  exact ⟨DK'⟩

/-- The nonsplit source branch constructs the whole-module marking, its precise
fixed involution line, and the full omega-center conclusion of 13.4.10(5). -/
theorem component_core_marking_of_moved_fixed_at
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (m : CoreMarking D)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    {z : G} (hzV : z ∈ V)
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆ = K)
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    ∃ DK : ChosenModule T K U, Nonempty (CoreMarking DK) ∧
      U ⊓ centralizer (K : Set G) = zpowers z ∧
      U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
        (K ⊔ (T : Subgroup G)).subtype,K⁆ ∧
      Nonempty (ComponentModuleAt DK z) ∧
      omegaOneCenterAmbient (T : Subgroup G) =
        V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  obtain ⟨⟨DK⟩,hUR⟩ := component_chosen_of_moved_fixed_at h₀ h structural m hzT hz1
    hKz hTK hKM hfK hqK hgen hfixed
  obtain ⟨a⟩ := fixed h₀ K hfK U DK hfixed
  obtain ⟨mK⟩ := coreMarking_of_faithful_core_action DK hqK a
  have hred := component_moved_reduced h₀ hzT hz1 hKz hTK
  have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) := le_sup_right.trans
    (le_normalizer_of_normal_subgroupOf (DK.le_sylow.trans le_sup_right) (hK := hred.normal))
  have hnC : (T : Subgroup G) ≤ normalizer (U ⊓ centralizer (K : Set G) : Set G) :=
    (le_inf hTU (hTK.trans (normalizer_le_normalizer_centralizer K))).trans
      inf_normalizer_le_normalizer_inf
  have hCZ : U ⊓ centralizer (K : Set G) ≤ omegaOneCenterAmbient (T : Subgroup G) := by
    let := DK.elementary
    intro x hx
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨DK.le_sylow hx.1,elemPow_eq_one_of_isElementaryAbelian x hx.1,
        le_centralizer_iff.mp
          (hnC.trans (normalizer_le_centralizer_of_card_two _ mK.card_fixed)) hx⟩
  have hCZz : U ⊓ centralizer (K : Set G) ≤ zpowers z := by
    rw [←component_full_fixed_line_at h structural z hz1 hzT hindex K hKz hKM]
    exact le_inf hCZ inf_le_right
  have hzcard : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ((mem_omegaOneCenterAmbient_iff _ _).mp hzT).2.1 hz1
  have he : U ⊓ centralizer (K : Set G) = zpowers z :=
    eq_of_le_of_card_ge hCZz (by rw [hzcard,mK.card_fixed])
  have hzU : z ∈ U := (he.symm ▸ mem_zpowers z).1
  have hs := full_seed_of_component_split_at h structural m ⟨z,hzV⟩
    (fun hh => hz1 (congrArg Subtype.val hh)) hzT hindex DK
    (ComponentModuleAt.coreSix mK hzU) hKz hKM
    (component_seed_split h₀ hzT hz1 hKz hTK)
  exact ⟨DK,⟨mK⟩,he,hUR,⟨ComponentModuleAt.coreSix mK hzU⟩,hs⟩

theorem component_core_marking_of_source_fixed_at
    {D : ChosenModule T L V}
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    {z : G} (hzV : z ∈ V)
    (hzT : z ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hKz : K ≤ centralizer ({z} : Set G))
    (hHN : centralizer ({z} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hfixed : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    ∃ DK : ChosenModule T K U, Nonempty (CoreMarking DK) ∧
      U ⊓ centralizer (K : Set G) = zpowers z ∧
      U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
        (K ⊔ (T : Subgroup G)).subtype,K⁆ ∧
      Nonempty (ComponentModuleAt DK z) ∧
      omegaOneCenterAmbient (T : Subgroup G) =
        V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  have hqK := component_quotient_quasisimple h1332 hfK
  have hgen := component_thompson_generation_at (D := D) h₀ h structural h1332 hzT hHN hKM hfK
  exact component_core_marking_of_moved_fixed_at h₀ h structural m fixed hindex hzV hzT hz1
    hKz (h1332 K hfK).1 hKM hfK hqK hgen hfixed

/-- Apply the guarded fixed-space component construction to the original
chosen module. The original augmentation marking and omega index are derived;
the selected component retains its literal centralizer and faithful-local guards. -/
theorem original_component_core_marking_at
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V)
    (hfixed : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
    (h1332 : Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G)) (hz1 : z ≠ 1)
    (hK : K ∈ Chapter1.cComponentsIn (centralizer ({z.val} : Set G)))
    (hKN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (hfixedK : (⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ :
      Subgroup G) ⊓ centralizer (K : Set G) ≠ ⊥) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    ∃ DK : ChosenModule T K U, Nonempty (CoreMarking DK) ∧
      U ⊓ centralizer (K : Set G) = zpowers z.val ∧
      U = ⁅(ReducedModule (K ⊔ (T : Subgroup G))).map
        (K ⊔ (T : Subgroup G)).subtype,K⁆ ∧
      Nonempty (ComponentModuleAt DK z.val) ∧
      omegaOneCenterAmbient (T : Subgroup G) =
        V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  have hstar := Section03.Noncentrality.source1332_faithful_maximal
    h₀.qtke T h1332 h₀.local_component
  have h : Hypothesis1223 KnownSimple.IsKnownSimple T L :=
    h₀.hypothesis1311.hypothesis1223
      ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T L).mp
        h₀.local_component |>.2⟩ (component_quotient_quasisimple h1332 h₀.local_component)
  obtain ⟨a⟩ := fixed h₀ L h₀.local_component V D hfixed
  obtain ⟨m⟩ := coreMarking_of_faithful_core_action D h.quasisimple a
  exact component_core_marking_of_source_fixed_at h₀ h structural m h1332 fixed
    (original_omega_fixed_index_at h₀ h structural D m earlier) z.property hz
    (fun he => hz1 (Subtype.ext he)) hK.1 hKN hKM hfK hfixedK

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
