module
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.NoThreeSupport
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.Seed

/-!
# Proper seed spans on a factor orbit

For an invariant proper orbit support, its central Sylow-fixed seed span cannot
fill the support. If it did, the actor's nonzero fixed space forces its full
preimage into the unique partner maximal local subgroup. The resulting
conjugate span is then M-invariant, contradicting the actual ordering source
obstruction. This is the basic case division in 15.1.2, before the proper
support case-6 analysis.

Source: Aschbacher--Smith 15.1.2, printed p.1085, and A.5.6/14.1.4,
with the literal selected-action seed and partner centralizer.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

theorem source_localAction_normal_actor_le_partner
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc}) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    ∀ (A : Subgroup (internalActionImage M V (le_normalizer_conjugateSpanBy _ _)))
      [A.Normal], fixedSpace ρ A ≠ ⊥ → (A.comap f).map M.subtype ≤ Mc := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let Vm := V.subgroupOf M
  have hVM : V ≤ M := localModule_le T hM.1.2
  let : Vm.Normal := normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  let : IsElementaryAbelian 2 Vm := IsElementaryAbelian.subgroupOf hVM
  dsimp only
  intro A hAN hfix
  let X := A.comap f
  let : A.Normal := hAN
  let : X.Normal := hAN.comap f
  by_contra hescape
  have hbot := fixed_eq_bot_of_image_normalized T hM.1.2 hu Vm X
    (le_normalizer_of_normal) hescape
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfix
  have hvm : (⟨v.toMul,hVM v.toMul.property⟩ : M) ∈ Vm ⊓ centralizer (X : Set M) := by
    refine ⟨v.toMul.property,?_⟩
    intro x hx
    have he := congrArg (fun w : Additive V => (w.toMul : G)) (hv ⟨f x,hx⟩)
    change (x:G) * (v.toMul:G) * (x:G)⁻¹ = v.toMul at he
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mp he
  rw [hbot] at hvm
  apply hv0
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg M.subtype (Subgroup.mem_bot.mp hvm)

theorem source_localAction_proper_seed_span
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc) :
    letI := localModule_elementary_from_source hG T
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
    let V := localModule T M
    let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
    let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
    let Z := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
    ∀ (A : Subgroup D) [A.Normal] (W : Submodule (ZMod 2) (Additive V)),
      (⊤ : Subgroup D) ≤ subspaceStabilizer ρ W → W ≠ ⊥ → W ≠ ⊤ →
      W ⊔ fixedSpace ρ A = ⊤ → Homogeneous.orbitSpan ρ A (Z ⊓ W) < W := by
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  let V := localModule T M
  let D := internalActionImage M V (le_normalizer_conjugateSpanBy _ _)
  let f := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict
  let ρ := imageRepresentation M V (le_normalizer_conjugateSpanBy _ _)
  let Z := AddSubgroup.toZModSubmodule 2 ((centralInvolutions T).subgroupOf V).toAddSubgroup
  dsimp only
  intro A hAN W hs hW hWt hsup
  change W ⊔ fixedSpace ρ A = ⊤ at hsup
  have hle : Homogeneous.orbitSpan ρ A (Z ⊓ W) ≤ W :=
    Homogeneous.orbitSpan_le ρ inf_le_right (le_top.trans hs)
  apply lt_of_le_of_ne hle
  intro he
  have hfix : fixedSpace ρ A ≠ ⊥ := by
    intro hb
    apply hWt
    simpa only [hb,sup_bot_eq] using hsup
  have hAMc := source_localAction_normal_actor_le_partner hG T hM hu A hfix
  let B : Subgroup V := Subgroup.toAddSubgroup.symm W.toAddSubgroup
  let X := B.map V.subtype
  let Y := X ⊓ centralInvolutions T
  let L := conjugateSpanBy Y (Mc ⊓ M)
  have hnX : M ≤ normalizer (X : Set G) := by
    apply le_normalizer_iff.mpr
    intro m hm v hv
    obtain ⟨v,hv,rfl⟩ := hv
    have hmem : ρ (f ⟨m,hm⟩) (Additive.ofMul v) ∈ W :=
      (hs (Subgroup.mem_top _) _).mpr hv
    exact ⟨(ρ (f ⟨m,hm⟩) (Additive.ofMul v)).toMul,hmem,rfl⟩
  have hLY : L ≤ X := conjugateSpanBy_le inf_le_left (inf_le_right.trans hnX)
  let C := AddSubgroup.toZModSubmodule 2 (L.subgroupOf V).toAddSubgroup
  have hseed : Z ⊓ W ≤ C := by
    intro v hv
    exact le_conjugateSpanBy Y (Mc ⊓ M) ⟨mem_map_of_mem V.subtype hv.2,hv.1⟩
  have hstable : A ≤ subspaceStabilizer ρ C := by
    apply le_subspaceStabilizer
    intro a ha v hv
    obtain ⟨m,hm⟩ := (actionHom M V (le_normalizer_conjugateSpanBy _ _)).rangeRestrict_surjective a
    have hmA : m ∈ A.comap f := by change f m ∈ A; rwa [hm]
    have hmMc : (m:G) ∈ Mc := hAMc (mem_map_of_mem M.subtype hmA)
    rw [←hm]
    exact le_normalizer_iff.mp (le_normalizer_conjugateSpanBy Y (Mc ⊓ M))
      (m:G) ⟨hmMc,m.property⟩ (v.toMul:G) hv
  have hWC : W ≤ C := he ▸ Homogeneous.orbitSpan_le ρ hseed hstable
  have hXL : X = L := by
    apply le_antisymm _ hLY
    rintro x ⟨v,hv,rfl⟩
    exact hWC hv
  have hXne : X ≠ ⊥ := by
    intro hb
    apply hW
    apply le_bot_iff.mp
    intro v hv
    have hx : (v.toMul:G) ∈ X :=
      mem_map_of_mem V.subtype (show v.toMul ∈ B from hv)
    rw [hb] at hx
    have hv0 : v = 0 := Additive.toMul.injective (Subtype.ext (Subgroup.mem_bot.mp hx))
    simpa only [hv0] using (show (0 : Additive V) ∈ (⊥ : Submodule (ZMod 2) (Additive V)) from zero_mem _)
  have hYne : Y ≠ ⊥ := by
    intro hy
    apply hXne
    rw [hXL]
    change conjugateSpanBy Y (Mc ⊓ M) = ⊥
    exact le_bot_iff.mp (conjugateSpanBy_le (by rw [hy]) (by rw [normalizer_eq_top]; exact le_top))
  have hMc : Mc ∈ maximalLocals T := by
    refine ⟨(show Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) from hu ▸ Set.mem_singleton Mc).1,?_⟩
    apply le_trans _ (centralizer_le_partner T hu)
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ z).mp hz).2.2 t ht).symm
  have hnL : M ≤ normalizer (conjugateSpanBy Y (Mc ⊓ M) : Set G) := by
    change M ≤ normalizer (L : Set G)
    rw [←hXL]
    exact hnX
  exact source_no_invariant_span_of_centralizing_orderingMaximal hG T hempty hM hJ
    hMc hne.symm Y hYne inf_le_right hnL

end CFSG.Quasithin.Chapter15.Section01
