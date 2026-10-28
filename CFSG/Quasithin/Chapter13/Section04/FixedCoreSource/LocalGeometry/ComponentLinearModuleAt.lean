module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentCoveredDoubledAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.ComponentSeedAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ComponentLinearModule

/-!
# The actual selected natural linear module at the original G,T

Apply B.5 to the reduced moved omega orbit. Its quotient order 168 leaves
minimality or the doubled natural representation; ComponentCoveredDoubledAt
excludes the latter in both original covering rows. The earlier fixed-module
clause excludes fixed vectors, and the earlier seven-row module theorem
constructs the natural coordinates over the literal K/O₂(K). Orbit splitting
then gives the full central four-group inside the original V.

Only same-G,T structural and module facts are used. The earlier source
clauses and natural LargeDistanceInput remain explicit. ComponentLinearWholeAt
and ComponentLinearGeometryAt apply this marking to the original geometry.
Source: Aschbacher--Smith B.5.1,13.3.2(3),13.4.10(4--5), pp.99,885,907--909.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource Nonsolvable
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open AlternatingSixReconstruction.Natural AlternatingSixReconstruction.Natural.Exhaustion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L K V : Subgroup G}

theorem linear_component_chosen_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    Nonempty (ChosenModule T K
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆) := by
  let H := K ⊔ (T : Subgroup G)
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  let A := K.subgroupOf H
  let W := U.subgroupOf H
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  have hTK := (h1332 K hfK).1
  have hred := component_moved_reduced h₀ hzT hz1 hKz hTK
  have hUK : U ≤ K := (component_moved_le_twoCore h₀ hzT hz1 hKz hTK).trans (pCoreIn_le 2 K)
  have hKH : K ≤ H := le_sup_left
  have hUH : U ≤ H := hUK.trans hKH
  have hnK : H ≤ normalizer (K : Set G) := sup_le K.le_normalizer hTK
  let : A.Normal := normal_subgroupOf_of_le_normalizer hnK
  let : W.Normal := hred.normal
  let : IsElementaryAbelian 2 W := hred.elementary
  have hUn : H ≤ normalizer (U : Set G) := le_normalizer_of_normal_subgroupOf hUH
  have hmove := component_moved_eq_commutator h₀ hzT hz1 hKz hTK
  have hne : U ≠ ⊥ := component_moved_ne_bot_at h structural m hKM
  have hgen := component_thompson_generation_at (D := D) h₀ h structural h1332 hzT hHN hKM hfK
  obtain ⟨_,_,_,_,hSQ⟩ := MainForward.localComponents_local_setup h₀.qtke T hfK.1
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let a : A ≃* K := subgroupOfEquivOfLe hKH
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let := component_quotient_quasisimple h1332 hfK
  have hqA : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv aq.symm
  have hcard : Nat.card (A ⧸ pCore 2 A) = 168 := by
    rw [Nat.card_congr (aq.trans eK).toEquiv,
      Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
    norm_num
  have hsup : A ⊔ (S : Subgroup H) = ⊤ := by
    apply map_injective H.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKH,
      ←MonoidHom.range_eq_map,range_subtype]
    change K ⊔ ((T : Subgroup G).subgroupOf H).map H.subtype = H
    rw [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)]
  have hgenA : ⁅A,elementaryAbelianMaxJ (S : Subgroup H)⁆ = A := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hKH,
      ←elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective]
    change ⁅K,elementaryAbelianMaxJ (((T : Subgroup G).subgroupOf H).map H.subtype)⁆ = K
    rw [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ H from le_sup_right)]
    exact hgen
  have hmoveW : ⁅W,A⁆ = W := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hKH,map_subgroupOf_eq_of_le hUH]
    exact hmove
  have hneW : W ≠ ⊥ := by
    intro he
    have hh := congrArg (map H.subtype) he
    rw [map_subgroupOf_eq_of_le hUH,Subgroup.map_bot] at hh
    exact hne hh
  rcases linear_reduced_component_minimal_or_double S A W hSQ hred hfK.1.1
      hqA hcard hsup hgenA hmoveW hneW with hmin | ⟨qK,e,he⟩
  · apply Section03.PlaneNoncentralitySource.exists_chosenModuleOfMinimal
      hred hUH hTK hUn hmove hne
    intro B hBU hn
    have hBn : A ≤ normalizer (B.subgroupOf H : Set H) := by
      apply le_normalizer_iff.mpr
      intro k hk b hb
      exact (mem_normalizer_iff.mp (hn hk) b.val).mp hb
    rcases hmin (B.subgroupOf H) (comap_mono hBU) hBn with he | hc
    · left
      have hh := congrArg (map H.subtype) he
      rwa [map_subgroupOf_eq_of_le (hBU.trans hUH),map_subgroupOf_eq_of_le hUH] at hh
    · right
      intro b hb k hk
      exact congrArg Subtype.val (hc (show (⟨b,(hBU.trans hUH) hb⟩ : H) ∈ B.subgroupOf H from hb)
        ⟨k,hKH hk⟩ hk)
  · let w : W ≃* U := subgroupOfEquivOfLe hUH
    let qK' := aq.symm.trans qK
    let e' := w.symm.trans e
    have he' : letI := conjMulDistribMulActionOfLeNormalizer K U (normalizer_commutator_ge_right _ _)
        ∀ (k : K) (v : U), (e' (k • v)).toAdd =
          (Representation.prod BinaryLinearThree.W BinaryLinearThree.W)
            (qK' (QuotientGroup.mk' (pCore 2 K) k)) (e' v).toAdd := by
      intro k v
      exact he (a.symm k) (w.symm v)
    exact (doubled_excluded_of_largeDistance_at hl h₀ h structural D m z hzT hzL
      hKz hHN hKM hTK qK' e' he').elim

omit [Finite G] in
private theorem linear_three_card (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    Nat.card (K ⧸ pCore 2 K) = 168 := by
  rw [Nat.card_congr eK.toEquiv,Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear]
  norm_num

omit [Finite G] in
private theorem linear_three_centralCore
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    Section08.TransvectionRecognition.Component.ModelExtension.centralCore K = pCore 2 K := by
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have he : eK x ∈ center BinaryLinearThree.Group := (centerCongr eK ⟨x,hx⟩).property
    rw [Matrix.PSL3Two.center_eq_bot,mem_bot] at he
    exact eK.map_eq_one_iff.mp he
  change (center (K ⧸ pCore 2 K)).comap (QuotientGroup.mk' (pCore 2 K)) = _
  rw [hz,MonoidHom.comap_bot,QuotientGroup.ker_mk']

/-- The original linear-three component has a natural marking and the full
central four-group. Minimality and vanishing fixed space are proved here. -/
theorem linear_component_marking_at
    (hl : LargeDistanceInput.{u} KnownSimple.IsKnownSimple)
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Section03.Noncentrality.SupercriticalSource.Source1332OneTwo T)
    (fixed : Section03.SourceCompletion.OriginalFixedModule1332At T L)
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hKz : K ≤ centralizer ({z.val} : Set G))
    (hHN : centralizer ({z.val} : Set G) ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ normalizer (L : Set G))
    (hfK : K ∈ MainForward.faithfulLocalComponents T)
    (eK : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
    ∃ DK : ChosenModule T K U,
      ∃ q : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group,
        ∃ e : U ≃* Multiplicative BinaryLinearThree.Vector,
          (∀ (k : K) (v : U),
            (e (U.normalizerMonoidHom ⟨k.val,DK.normalizes k.property⟩ v)).toAdd =
              BinaryLinearThree.W (q (QuotientGroup.mk' (pCore 2 K) k)) (e v).toAdd) ∧
          U ⊓ centralizer (K : Set G) = ⊥ ∧
          Nonempty (ComponentModuleAt DK z.val) ∧
          omegaOneCenterAmbient (T : Subgroup G) =
            V ⊓ omegaOneCenterAmbient (T : Subgroup G) ∧
          Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 := by
  let U := ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆
  obtain ⟨DK⟩ := linear_component_chosen_at hl h₀ h structural D m h1332 z hzT hzL hKz hHN hKM hfK eK
  have hfixed : U ⊓ centralizer (K : Set G) = ⊥ := by
    by_contra hf
    obtain ⟨a⟩ := fixed h₀ K hfK U DK hf
    let := DK.actionCentralizer_normal
    have hd := card_dvd_of_surjective
      (a.groupEquiv.toMonoidHom.comp DK.coreToFaithful)
      (a.groupEquiv.surjective.comp DK.coreToFaithful_surjective)
    rw [linear_three_card eK,nat_card_alternatingGroup,Nat.card_fin] at hd
    norm_num at hd
  have hstar := Section03.Noncentrality.source1332_faithful_maximal h₀.qtke T h1332 hfK
  have hK12 := h₀.hypothesis1311.hypothesis1223
    ⟨hstar,(Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T K).mp hfK |>.2⟩
    (component_quotient_quasisimple h1332 hfK)
  obtain ⟨q,e,he⟩ := linear_three_natural_coordinates DK eK hfixed (modules K U hK12 DK)
  let ec := QuotientGroup.quotientMulEquivOfEq (linear_three_centralCore eK)
  have mark : ComponentModuleAt DK z.val := .linearThree (ec.trans q) e (fun k v => he k v)
  have hz1 : z.val ≠ 1 := fun he => hzL (he ▸ one_mem _)
  exact ⟨DK,q,e,he,hfixed,⟨mark⟩,full_seed_of_component_split_at h structural m z
    (fun hh => hz1 (congrArg Subtype.val hh)) hzT hindex DK mark hKz hKM
    (component_seed_split h₀ hzT hz1 hKz (h1332 K hfK).1)⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
