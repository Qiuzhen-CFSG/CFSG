module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.FirstFlagMSPair
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.InitialAction
public import Theory.Representation.BinaryOffender.NoncentralMoved

/-!
# The original five-space in the covered Baumann MS pair

The chosen module V lies in the central omega layer of the literal product
L Baum(R₁): it is normal elementary abelian and centralizes its two-core.
The source initial FF classification makes the layer's moved space Irr⁺.
A noncentral invariant subgroup for a perfect actor contains that whole
moved space. Since V=[V,L], its literal inclusion identifies the entire
initial moved subgroup with V.

The faithful triple-cover initial action would have moved dimension six,
but the original V has order 32. This excludes that branch and identifies
the actual initial kernel with the retained cubic extension. The construction
uses the preceding genuine MS pair; no action-kernel or whole-core exhaustion
premise is supplied. Excluding the remaining cubic-kernel pair, proving the
Baumann normalizer bound and assembling covered recognition remain later
source steps.

Source: Aschbacher--Smith C.1.32, C.1.37 and 13.2.2(7), pp.135--143,878;
Meierfrankenfeld--Stellmacher (1993), initial moved layer (3.2), pp.863--864.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Solvable Nonsolvable
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

open Representation Representation.BinaryOffender ChapterB.QuasisimpleSource
open scoped IsMulCommutative
open AlternatingSixReconstruction.Exceptional
open AlternatingSixReconstruction.Exceptional.Exhaustion

private theorem moved_le_noncentral_subgroup
    {H A : Type*} [Group H] [Finite H] [Group A]
    (W X : Subgroup H) [W.Normal] [X.Normal] [IsElementaryAbelian 2 X]
    (hWX : W ≤ X) (q : H →* A) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (X : Set H)) (K : Subgroup H) [Group.IsPerfect K]
    (hne : ¬ W ≤ centralizer (K : Set H))
    (hi : IsIrrPlus (NormalElementaryQuotient.representation X q hq hk) (K.map q)
      (moved (NormalElementaryQuotient.representation X q hq hk) (K.map q))) :
    moved (NormalElementaryQuotient.representation X q hq hk) (K.map q) ≤
      AddSubgroup.toZModSubmodule 2 (W.subgroupOf X).toAddSubgroup := by
  let ρ := NormalElementaryQuotient.representation X q hq hk
  let Y : Submodule (ZMod 2) (Additive X) :=
    AddSubgroup.toZModSubmodule 2 (W.subgroupOf X).toAddSubgroup
  let : Group.IsPerfect (K.map q) := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective K)
  have hY : K.map q ≤ subspaceStabilizer ρ Y := by
    apply le_subspaceStabilizer
    rintro _ ⟨k,hk,rfl⟩ v hv
    change ((ρ (q k) v).toMul : H) ∈ W
    rw [NormalElementaryQuotient.representation_apply]
    exact (inferInstance : W.Normal).conj_mem _ hv k
  have hn : ¬ Y ≤ fixedSpace ρ (K.map q) := by
    intro hf
    apply hne
    intro w hw k hk
    have he := congrArg (fun v : Additive X => (v.toMul : H))
      (hf (show Additive.ofMul (⟨w,hWX hw⟩ : X) ∈ Y from hw)
        (q.subgroupMap K ⟨k,hk⟩))
    change ((ρ (q k) (Additive.ofMul ⟨w,hWX hw⟩)).toMul : H) = w at he
    rw [NormalElementaryQuotient.representation_apply] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hm : moved ρ (K.map q) ≤ Y := by
    change subspaceCommutator ρ ⊤ (K.map q) ≤ Y
    rw [←moved_eq_of_noncentral_invariant ρ (K.map q) hi Y hY hn]
    exact subspaceCommutator_le_of_invariant ρ hY
  exact hm

private theorem moved_card_le_noncentral_subgroup
    {H A : Type*} [Group H] [Finite H] [Group A]
    (W X : Subgroup H) [W.Normal] [X.Normal] [IsElementaryAbelian 2 X]
    (hWX : W ≤ X) (q : H →* A) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (X : Set H)) (K : Subgroup H) [Group.IsPerfect K]
    (hne : ¬ W ≤ centralizer (K : Set H))
    (hi : IsIrrPlus (NormalElementaryQuotient.representation X q hq hk) (K.map q)
      (moved (NormalElementaryQuotient.representation X q hq hk) (K.map q))) :
    2 ^ Module.finrank (ZMod 2)
      (moved (NormalElementaryQuotient.representation X q hq hk) (K.map q)) ≤ Nat.card W := by
  let ρ := NormalElementaryQuotient.representation X q hq hk
  let Y : Submodule (ZMod 2) (Additive X) :=
    AddSubgroup.toZModSubmodule 2 (W.subgroupOf X).toAddSubgroup
  have hm := moved_le_noncentral_subgroup W X hWX q hq hk K hne hi
  let e : Y ≃ W := {
    toFun := fun v => ⟨v.val.toMul.val,v.property⟩
    invFun := fun w => ⟨Additive.ofMul ⟨w.val,hWX w.property⟩,w.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hcard : Nat.card (moved ρ (K.map q)) =
      2 ^ Module.finrank (ZMod 2) (moved ρ (K.map q)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  rw [←hcard,←Nat.card_congr e]
  exact Nat.card_le_card_of_injective (Submodule.inclusion hm) (Submodule.inclusion_injective hm)

/-- The original five-space is in the central omega layer of the literal
Baumann product, including the covered row. -/
theorem firstFlagCore_module_le_centralOmega
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D) :
    let B := ChapterB.baumann (firstFlagCore h structural D m)
    V.subgroupOf (L ⊔ B) ≤ centralOmega L B := by
  let X := L ⊔ (T : Subgroup G)
  let R := firstFlagCore h structural D m
  let B := ChapterB.baumann R
  let J := L ⊔ B
  have hRT : R ≤ T := map_subtype_le _
  have hJX : J ≤ X := sup_le le_sup_left
    ((inf_le_left : B ≤ R).trans (hRT.trans le_sup_right))
  have hVJ : V ≤ J := D.le_component.trans le_sup_left
  have hTNB : (T : Subgroup G) ≤ normalizer (B : Set G) :=
    (sylow_normalizes_firstFlagCore h structural D m).trans (normalizer_le_normalizer_baumann R)
  have hXNJ : X ≤ normalizer (J : Set G) :=
    sup_le (le_sup_left.trans J.le_normalizer)
      ((le_inf D.sylow_normalizes_component hTNB).trans
        (normalizer_inf_normalizer_le_normalizer_sup L B))
  let U := V.subgroupOf J
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (hJX.trans (sup_le D.normalizes ((structural G T L h).2.2 V D).1))
  let := D.elementary
  have hUQ : U ≤ pCore 2 J := le_sSup ⟨inferInstance,(IsElementaryAbelian.isPGroup 2 V).comap_subtype⟩
  have hQQ : J.pCoreIn 2 ≤ X.pCoreIn 2 := pCoreIn_mono_of_normalizes hJX hXNJ
  change U ≤ centralOmega L B
  intro v hv
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨hUQ hv,?_,?_⟩
  · intro x hx
    apply Subtype.ext
    exact (D.core_centralizes (hQQ (mem_map_of_mem J.subtype hx)) v.val hv).symm
  · apply Subtype.ext
    change v.val ^ 2 = 1
    exact elemPow_eq_one_of_isElementaryAbelian (A := V) v.val hv

/-- The entire moved subgroup of the central omega layer is the original
chosen V, through the literal inclusion into L Baum(R₁). -/
theorem covered_firstFlagCore_initial_moved_of_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hescape : ¬ normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G)) :
    let B := ChapterB.baumann (firstFlagCore h structural D m)
    ⁅centralOmega L B,L.subgroupOf (L ⊔ B)⁆ = V.subgroupOf (L ⊔ B) := by
  let B := ChapterB.baumann (firstFlagCore h structural D m)
  let J := L ⊔ B
  let U := V.subgroupOf J
  let K := L.subgroupOf J
  let X := centralOmega L B
  let hms : SmallMSPair KnownSimple.IsKnownSimple L B := covered_firstFlagCore_smallMSPair_of_escape h structural D m hc z hzT hzL hescape
  let e : CentralMarking L := m.quotient.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)).symm
  have hRT : firstFlagCore h structural D m ≤ T := map_subtype_le _
  have hJX : J ≤ L ⊔ (T : Subgroup G) := sup_le le_sup_left
    ((inf_le_left : B ≤ firstFlagCore h structural D m).trans (hRT.trans le_sup_right))
  have hVJ : V ≤ J := D.le_component.trans le_sup_left
  let : U.Normal := normal_subgroupOf_of_le_normalizer
    (hJX.trans (sup_le D.normalizes ((structural G T L h).2.2 V D).1))
  let : Group.IsPerfect K := hms.component.perfect
  have hn : ¬ U ≤ centralizer (K : Set J) := by
    intro hcent
    apply hzL
    intro l hl
    exact congrArg (fun x : J => (x : G))
      (hcent (show (⟨z.val,hVJ z.property⟩ : J) ∈ U from z.property)
        ⟨l,mem_sup_left hl⟩ hl)
  have hUX : U ≤ X := firstFlagCore_module_le_centralOmega h structural D m
  have hm := moved_le_noncentral_subgroup U X hUX
    (QuotientGroup.mk' (layerKernel L B)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _) K hn (layer_moved_irrPlus hms e hc.2.1)
  have hcomm : ⁅U,K⁆ = U := by
    apply map_injective J.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVJ,
      map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left),D.eq_commutator.symm]
  change ⁅X,K⁆ = U
  apply le_antisymm ?_ (hcomm ▸ commutator_mono hUX le_rfl)
  intro x hx
  apply hm (show Additive.ofMul (⟨x,(commutator_le_left X K) hx⟩ : X) ∈
    moved (layerAction L B) (layerComponent L B) from ?_)
  change _ ∈ subspaceCommutator (NormalElementaryQuotient.representation X
    (QuotientGroup.mk' (layerKernel L B)) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _)) ⊤ (K.map (QuotientGroup.mk' (layerKernel L B)))
  rw [←NormalElementaryQuotient.commutatorSpace_eq]
  exact hx

/-- The constructed covered MS pair cannot have a faithful six-dimensional
initial moved layer: its original noncentral five-space lies in central omega.
Consequently its exact initial kernel is the retained cubic extension. -/
theorem covered_firstFlagCore_initial_kernel_of_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hc : Section08.SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (z : V) (hzT : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hescape : ¬ normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G)) :
    let B := ChapterB.baumann (firstFlagCore h structural D m)
    let hms : SmallMSPair KnownSimple.IsKnownSimple L B := covered_firstFlagCore_smallMSPair_of_escape h structural D m hc z hzT hzL hescape
    layerKernel L B = extensionKernel hms := by
  let B := ChapterB.baumann (firstFlagCore h structural D m)
  let J := L ⊔ B
  let hms : SmallMSPair KnownSimple.IsKnownSimple L B := covered_firstFlagCore_smallMSPair_of_escape h structural D m hc z hzT hzL hescape
  let e : CentralMarking L := m.quotient.trans
    (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)).symm
  change layerKernel L B = extensionKernel hms
  rcases centralOmega_centralizer_cases hms e hc.2.1 with hfaith | hkernel
  · obtain ⟨hi,hd,_⟩ := layer_moved_hexEven hms e hc.2.1 hfaith
    let U := V.subgroupOf J
    let K := L.subgroupOf J
    have hRT : firstFlagCore h structural D m ≤ T := map_subtype_le _
    have hJX : J ≤ L ⊔ (T : Subgroup G) := sup_le le_sup_left
      ((inf_le_left : B ≤ firstFlagCore h structural D m).trans (hRT.trans le_sup_right))
    have hVJ : V ≤ J := D.le_component.trans le_sup_left
    let : U.Normal := normal_subgroupOf_of_le_normalizer
      (hJX.trans (sup_le D.normalizes ((structural G T L h).2.2 V D).1))
    let : Group.IsPerfect K := hms.component.perfect
    have hn : ¬ U ≤ centralizer (K : Set J) := by
      intro hcent
      apply hzL
      intro l hl
      exact congrArg (fun x : J => (x : G))
        (hcent (show (⟨z.val,hVJ z.property⟩ : J) ∈ U from z.property)
          ⟨l,mem_sup_left hl⟩ hl)
    have hb := moved_card_le_noncentral_subgroup U (centralOmega L B)
      (firstFlagCore_module_le_centralOmega h structural D m)
      (QuotientGroup.mk' (layerKernel L B)) (QuotientGroup.mk'_surjective _)
      (QuotientGroup.ker_mk' _) K hn hi
    change 2 ^ Module.finrank (ZMod 2)
      (moved (layerAction L B) (layerComponent L B)) ≤ Nat.card U at hb
    have hu : Nat.card U = 32 :=
      (Nat.card_congr (subgroupOfEquivOfLe hVJ).toEquiv).trans m.card_module
    rw [hd,hu] at hb
    norm_num at hb
  · exact hkernel

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
