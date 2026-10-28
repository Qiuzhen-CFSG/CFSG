module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeZeroCoreTriality
public import Theory.SpecificGroups.Triality.ArmsSylowCenter
public import Theory.GroupTheory.CenterWeakClosureByDerivedLines

/-!
# The original omega-center in the marked zero-core triality row

Characteristic two places the original Sylow center inside the overlap
S. The marked right parabolic then identifies Z(S) with the nontrivial
original omega-center, of order two. The right factor and T centralize
this center, hence so does their actual join H. The original seven-actor
therefore fixes the whole L-span, by the checked fixed-lift theorem.

No equality S=T or comparison of the two field degrees is assumed.
Recognition of the parabolic marking and exclusion of its remaining
configuration stay with qt-d-1222-rankone-cartan-local-to-global.
Source: Aschbacher–Smith 5.2.2, printed pp.647–648 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The original Sylow center lies in the overlap two-core, before any model marking. -/
theorem Input.center_sylow_le_sourceS {κ : GroupClass}
    {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}
    (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    (center T).map (T : Subgroup G).subtype ≤ Global.sourceS L H := by
  have hQ : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow H (T.subtype hH.1.1.2)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hc := Chapter1.lemma_1_1_4_6 T (h.qtke.evenCharacteristic T) hH.1.1
  have hQS : H.pCoreIn 2 ≤ Global.sourceS L H :=
    Chapter3.twoCore_le_of_sylow_le T (le_inf h.sylow_normalizes hH.1.1.2)
      (show Global.intersection L H ≤ H from inf_le_right)
  rintro z ⟨t,ht,rfl⟩
  apply hQS
  apply hc
  refine ⟨hH.1.1.2 t.property,?_⟩
  intro q hq
  exact congrArg Subtype.val (mem_center_iff.mp ht ⟨q,hQ hq⟩)

namespace Prime
open Triality.Standard Triality.Standard.Parabolics

/-- The marked right endpoint centralizes the original omega-center. In particular
H centralizes it, although the equality S=T has not been used. -/
theorem LocalData.zeroCore_binaryTriality_omega_center
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (e : RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      binaryTrialityPrimeAmalgam) :
    (center (Global.sourceS L H)).map (Global.sourceS L H).subtype =
        Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ∧
      Nat.card (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2 ∧
      H ≤ omegaCentralizer T := by
  let S := Global.sourceS L H
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let C := (center S).map S.subtype
  obtain ⟨_,hSR,_,_⟩ := d.zeroCore_binaryTriality_configuration h hH c hd hz e
  have heq : R = R ⊔ S := (sup_eq_left.mpr hSR).symm
  let a : R ≃* parabolic (binaryParameters 1 Nat.zero_lt_one) .arms :=
    (MulEquiv.subgroupCongr heq).trans e.right
  obtain ⟨P,hP⟩ := d.right_sylow
  have hPS : (P : Subgroup R).map R.subtype = S := hP.trans (inf_eq_left.mpr hSR)
  obtain ⟨hcard,hcentral⟩ := binary_arms_sylow_center a P
  have hC : C = (center P).map (R.subtype.comp (P : Subgroup R).subtype) := by
    dsimp only [C]
    rw [←hPS,map_center_image_of_injective _ _ R.subtype_injective]
  have hCcard : Nat.card C = 2 := by
    rw [hC,card_map_of_injective (f := R.subtype.comp (P : Subgroup R).subtype)
      (R.subtype_injective.comp (P : Subgroup R).subtype_injective)]
    exact hcard
  have hCR : C ≤ centralizer (R : Set G) := by
    rw [hC]
    rintro _ ⟨z,hz,rfl⟩ r hr
    exact congrArg Subtype.val (mem_center_iff.mp
      (hcentral (mem_map_of_mem _ hz)) ⟨r,hr⟩)
  have hST := Global.sourceS_le_sylow h.sylow_normalizes hH.1.1.2
  have hZC : Z ≤ C := by
    intro z hz
    have ht := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
    have hZS : z ∈ S := h.center_sylow_le_sourceS hH
      ⟨⟨z,ht.1⟩,mem_center_iff.mpr (fun t => Subtype.ext (ht.2.2 t t.property)),rfl⟩
    exact ⟨⟨z,hZS⟩,mem_center_iff.mpr
      (fun s => Subtype.ext (ht.2.2 s (hST s.property))),rfl⟩
  have hT : (T : Subgroup G) ≠ ⊥ := by
    intro ht
    have hQT := pCoreIn_le_sylow H (T.subtype hH.1.1.2)
    change H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf H).map H.subtype at hQT
    rw [map_subgroupOf_eq_of_le hH.1.1.2,ht] at hQT
    exact hH.1.1.1 (bot_unique hQT)
  let : Nontrivial T := (nontrivial_iff_ne_bot _).mpr hT
  have hZ : Z ≠ ⊥ := by
    intro he
    exact omega_center_ne_bot T.isPGroup'
      ((map_eq_bot_iff_of_injective _ (f := (T : Subgroup G).subtype)
        (T : Subgroup G).subtype_injective).mp he)
  have hZeq : Z = C := eq_of_le_of_card_ge hZC (by
    rw [hCcard]
    exact Nat.succ_le_iff.mpr ((one_lt_card_iff_ne_bot Z).mpr hZ))
  refine ⟨hZeq.symm,?_,?_⟩
  · change Nat.card Z = 2
    rw [hZeq]
    exact hCcard
  · rw [←d.right_generate]
    apply sup_le _ sylow_le_omegaCentralizer
    apply le_centralizer_iff.mp
    change Z ≤ centralizer (R : Set G)
    rw [hZeq]
    exact hCR

/-- The actual order-seven Hall intersection fixes the entire original L-span;
its omega-fixing premise is now discharged by the marked geometry. -/
theorem LocalData.zeroCore_binaryTriality_fixes_omega_span
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hn : n = 2 ∨ n = 4 ∨ n = 8)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    (e : RankTwoAmalgam.ParabolicEquiv (zeroCoreAmalgam L H B D R)
      binaryTrialityPrimeAmalgam) :
    (B ⊓ R : Subgroup G) ≤ centralizer
      (conjugateSpanBy (Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) L : Set G) := by
  obtain ⟨_,_,_,hcard⟩ := d.zeroCore_binaryTriality_configuration h hH c hd hz e
  have hHC := (d.zeroCore_binaryTriality_omega_center h hH c hd hz e).2.2
  exact (c.seven_centralizes_omega_span_iff h hn inf_le_left hcard).mpr
    (inf_le_right.trans ((d.right_le_residual.trans (map_subtype_le _)).trans hHC))
end Prime
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
