module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralResidualImage
public import Theory.GroupAction.FiveSixteenCentralizer
public import Theory.Representation.BinaryOffender.ConjugationImage
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# The original order-five residual and its uniqueness normalizer

The marked five-kernel acts faithfully on the sixteen-element chosen module.
Its invariant subgroups are trivial or full, so the nontrivial original
central seed generates V under the literal residual Y. The source ordering
criterion therefore proves M = !M(YT) without classifying the whole actor.
The exact image also gives [V,Y] = V. Since V lies in the original
intersection core, it normalizes Y and hence lies in O₂(Y). Uniqueness
then puts N_G(O₂(Y)) and N_G(Y) inside M.

These are the residual prerequisites used in the order-five wreath argument;
the mixed rank-one amalgam and subsequent proper-local contradiction remain
separate source steps. No normality of Y in M is assumed or asserted.

Source: Aschbacher--Smith15.2.3(3) and15.2.4, printed pp.1105--1107.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

private theorem seed_span_of_five_image
    {M V X Z : Subgroup G} (hn : M ≤ normalizer (V : Set G))
    (hXM : X ≤ M) (hZV : Z ≤ V) (hZ : Z ≠ ⊥) (hV : Nat.card V = 16)
    (hc : Nat.card ((X.subgroupOf M).map (actionHom M V hn).rangeRestrict) = 5) :
    conjugateSpanBy Z X = V := by
  let D := internalActionImage M V hn
  let f : M →* D := (actionHom M V hn).rangeRestrict
  let P := (X.subgroupOf M).map f
  change Nat.card P = 5 at hc
  let K := conjugateSpanBy Z X
  have hKV : K ≤ V := conjugateSpanBy_le hZV (hXM.trans hn)
  have hKn : X ≤ normalizer (K : Set G) := le_normalizer_conjugateSpanBy Z X
  have hnot : FixedPoints.subgroup P V ≠ ⊤ := by
    intro he
    have hbot : P = ⊥ := by
      apply bot_unique
      intro p hp
      apply Subtype.ext
      apply MulEquiv.ext
      intro v
      have hh : v ∈ FixedPoints.subgroup P V := he ▸ mem_top v
      exact hh ⟨p,hp⟩
    rw [hbot,card_bot] at hc
    norm_num at hc
  have hfixed := Theory.GroupAction.fixed_eq_bot_of_five_action_card_sixteen hc hV hnot
  let : IsInvariant P V (K.subgroupOf V) := ⟨by
    intro p v
    obtain ⟨x,hx,he⟩ := p.property
    change (x:G) ∈ X at hx
    have hpval : ((f x : D) : MulAut V) = ((p:D) : MulAut V) := congrArg Subtype.val he
    change (v:G) ∈ K ↔ (((p:D) : MulAut V) v : G) ∈ K
    rw [←hpval]
    exact mem_normalizer_iff.mp (hKn hx) (v:G)⟩
  rcases invariant_eq_bot_or_top_of_five_actor hc hV hfixed (K.subgroupOf V) with hb | ht
  · apply (hZ ?_).elim
    apply bot_unique
    intro z hz
    have hzk : (⟨z,hZV hz⟩ : V) ∈ K.subgroupOf V := le_conjugateSpanBy Z X hz
    exact congrArg Subtype.val (mem_bot.mp (show (⟨z,hZV hz⟩ : V) ∈ (⊥ : Subgroup V) from hb ▸ hzk))
  · apply le_antisymm hKV
    intro v hv
    exact show (⟨v,hv⟩ : V) ∈ K.subgroupOf V from ht ▸ mem_top _

private theorem residual_notation (K : Subgroup G) :
    twoResidualAmbient K = (pResidual 2 K).map K.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN,n,hn⟩
    exact ⟨hN,IsPGroup.of_card hn⟩
  · rintro ⟨hN,hn⟩
    exact ⟨hN,IsPGroup.iff_card.mp hn⟩

section ChosenFive
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype)) {m : ℕ}
    (hp : PrimeDimensionOptions 5 m) (hd : DihedralMarking l 5 m)
include hG hempty hM hJ hu hmany hp hd

private theorem five_cards :
    Nat.card V = 16 ∧ Nat.card
      (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
        (actionHom M V hV.normalized).rangeRestrict) = 5 := by
  have hm : m = 2 := by
    rcases (primeDimensionOptions_iff 5 m).mp hp with h | h
    · norm_num at h
    · exact h.2
  have hdim : Module.finrank (ZMod 2) (Additive V) = 4 := by simpa [hm] using hd.dimension
  have hc : Nat.card V = 16 := by
    have hh := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod,hdim] at hh
    exact (Nat.card_congr Additive.toMul).symm.trans hh
  refine ⟨hc,?_⟩
  have he := source_dihedral_caseIIResidual_image hG T hempty hM hJ hu hmany hV l hp hd
  exact (congrArg (fun K : Subgroup (internalActionImage M V hV.normalized) => Nat.card K) he).trans
    ((card_map_of_injective (Jhat (imageRepresentation M V hV.normalized)).subtype_injective).trans
      hd.card_kernel)

/-- The original central seed generates under the marked five residual itself. -/
theorem source_dihedral_five_residual_seed_span :
    V = conjugateSpanBy (centralInvolutions T ⊓ V)
      (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc) := by
  obtain ⟨hcV,hcY⟩ := five_cards hG T hempty hM hJ hu hmany hV l hp hd
  have hZ : centralInvolutions T ⊓ V ≠ ⊥ := by
    intro hz
    apply hV.nontrivial
    rw [hV.seed_span]
    exact bot_unique (conjugateSpanBy_le hz.le le_normalizer_of_normal)
  exact (seed_span_of_five_image hV.normalized
    (source_caseIIResidual_le T hM.1.2 (map_subtype_le _)) inf_le_right hZ hcV hcY).symm

/-- Original15.2.3(3) for the marked order-five row, with all image premises discharged. -/
theorem source_dihedral_five_residual_sylow_unique :
    maximalTwoLocalOvergroups
      (caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc ⊔
        (T : Subgroup G)) = {M} := by
  apply source_unique_overgroup_of_seed_span hG T hempty hM hJ le_sup_right
    (sup_le (source_caseIIResidual_le T hM.1.2 (map_subtype_le _)) hM.1.2)
    hV.nontrivial hV.normalized
  apply le_antisymm ?_ (conjugateSpanBy_le inf_le_right
    ((sup_le (source_caseIIResidual_le T hM.1.2 (map_subtype_le _)) hM.1.2).trans hV.normalized))
  exact (source_dihedral_five_residual_seed_span hG T hempty hM hJ hu hmany hV l hp hd).le.trans
    (conjugateSpanBy_mono le_rfl le_sup_left)

/-- The literal order-five residual moves the entire original chosen module. -/
theorem source_dihedral_five_residual_movement :
    ⁅V,caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc⁆ = V := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let ρ := imageRepresentation M V hV.normalized
  let f : M →* internalActionImage M V hV.normalized := (actionHom M V hV.normalized).rangeRestrict
  have hYM : Y ≤ M := source_caseIIResidual_le T hM.1.2 (map_subtype_le _)
  let a := f.comp (inclusion hYM)
  have ha : a.range = (Y.subgroupOf M).map f := by
    ext d
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨⟨y,hYM y.property⟩,y.property,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
  have hh := commutator_image_eq ρ V V Y (hYM.trans hV.normalized) le_rfl
    a (MonoidHom.id V) (fun _ _ => rfl) ⊤ (by ext x; simp [binarySubgroup])
  rw [map_id,ha] at hh
  have he := source_dihedral_caseIIResidual_image hG T hempty hM hJ hu hmany hV l hp hd
  have hm : subspaceCommutator ρ ⊤ (l.kernel.map (Jhat ρ).subtype) = ⊤ := by
    rw [←subspaceCommutator_comp_map]
    exact l.moved
  change (Y.subgroupOf M).map f = l.kernel.map (Jhat ρ).subtype at he
  rw [he,hm] at hh
  have hcommV : ⁅V,Y⁆ ≤ V := le_normalizer_iff_commutator_le_left.mp (hYM.trans hV.normalized)
  have hfull : ⁅V,Y⁆.subgroupOf V = ⊤ := hh
  have h := congrArg (map V.subtype) hfull
  rw [map_subgroupOf_eq_of_le hcommV,←MonoidHom.range_eq_map,range_subtype] at h
  exact h


/-- The exact core and normalizer controls used in the order-five branch of15.2.4. -/
theorem source_dihedral_five_residual_core_normalizer :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    V ≤ Y.pCoreIn 2 ∧ normalizer (Y.pCoreIn 2 : Set G) ≤ M ∧
      normalizer (Y : Set G) ≤ M := by
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  let R := (M ⊓ Mc).pCoreIn 2
  let A := twoResidualAmbient (chosenStarredPreimage M V hV.normalized) ⊔ (T : Subgroup G)
  let K := conjugateSpanBy R A
  have hYR : Y = (pResidual 2 K).map K.subtype := residual_notation K
  have hn : normalizer (K : Set G) ≤ normalizer (Y : Set G) := by
    rw [hYR]
    exact normalizer_le_normalizer_characteristic_image K (pResidual 2 K)
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    (show (T : Subgroup G) ≤ A from le_sup_right).trans
      ((le_normalizer_conjugateSpanBy R A).trans hn)
  have hVR : V ≤ R := le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
    (le_inf hV.le_selected (V.le_centralizer.trans (hV.centralizer_le_partner T hu)))
    (inf_le_left.trans hV.normalized)
  have hVY : V ≤ normalizer (Y : Set G) :=
    hVR.trans ((le_conjugateSpanBy R A).trans (K.le_normalizer.trans hn))
  have hYM : Y ≤ M := source_caseIIResidual_le T hM.1.2 (map_subtype_le _)
  have hVinside : V ≤ Y := by
    exact (source_dihedral_five_residual_movement hG T hempty hM hJ hu hmany hV l hp hd).symm.le.trans
      (le_normalizer_iff_commutator_le_right.mp hVY)
  have hVcore : V ≤ Y.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 V) hVinside (hYM.trans hV.normalized)
  have hcore : Y.pCoreIn 2 ≠ ⊥ := fun he => hV.nontrivial (bot_unique (hVcore.trans he.le))
  have hc : normalizer (Y : Set G) ≤ normalizer (Y.pCoreIn 2 : Set G) :=
    normalizer_le_normalizer_characteristic_image Y (pCore 2 Y)
  have huY := source_dihedral_five_residual_sylow_unique hG T hempty hM hJ hu hmany hV l hp hd
  have hcontrol : normalizer (Y.pCoreIn 2 : Set G) ≤ M := by
    apply normalizer_le_of_unique_maximalTwoLocal (J := Y ⊔ (T : Subgroup G))
      (fun N hN hYN => ?_) (isPGroup_pCoreIn 2 Y) hcore
      ((sup_le Y.le_normalizer hTY).trans hc)
    have hmem : N ∈ maximalTwoLocalOvergroups (Y ⊔ (T : Subgroup G)) := ⟨hN,hYN⟩
    rw [huY] at hmem
    exact hmem
  exact ⟨hVcore,hcontrol,hc.trans hcontrol⟩
end ChosenFive
end CFSG.Quasithin.Chapter15.Section02
