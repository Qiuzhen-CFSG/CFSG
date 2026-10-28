module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.OmegaChosenComplete
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.ChosenCyclicExtension
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.DihedralMovement
public import Theory.GroupTheory.PResidual.PrimeConjugateSpan

/-!
# The original dihedral residual image

The action image of M0 is the literal Jhat, and its two-residual maps onto
the marked odd prime kernel P. The image of the specified O²(M0)T orbit
is therefore P S. Source core noncentrality makes Rc's two-image nontrivial;
the exact dihedral Jhat and prepared ratio force it to move P. The residual
of that relative orbit is P. The existing cyclic star transfer supplies
the faithful action/star isomorphism, retaining the original l,p,m marking.

Source: Aschbacher--Smith15.2.3(1)(i), printed pp.1104--1105.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
open ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

private theorem residual_notation {D : Type*} [Group D] [Finite D] (H : Subgroup D) :
    twoResidualAmbient H = (pResidual 2 H).map H.subtype := by
  unfold twoResidualAmbient twoResidualSubgroup pResidual
  congr 1
  apply congrArg sInf
  ext N
  constructor
  · rintro ⟨hN, n, hn⟩
    exact ⟨hN, IsPGroup.of_card hn⟩
  · rintro ⟨hN, hp⟩
    exact ⟨hN, IsPGroup.iff_card.mp hp⟩

/-- The original dihedral residual has precisely the marked prime action image. -/
theorem source_dihedral_caseIIResidual_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype)) {p m : ℕ}
    (hp : PrimeDimensionOptions p m) (hd : DihedralMarking l p m) :
    ((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
        (actionHom M V hV.normalized).rangeRestrict =
      l.kernel.map (Jhat (imageRepresentation M V hV.normalized)).subtype := by
  let ρ := imageRepresentation M V hV.normalized
  let f : M →* internalActionImage M V hV.normalized := (actionHom M V hV.normalized).rangeRestrict
  let M₀ := chosenStarredPreimage M V hV.normalized
  let P := l.kernel.map (Jhat ρ).subtype
  let R := (((M ⊓ Mc).pCoreIn 2).subgroupOf M).map f
  let S := ((T : Subgroup G).subgroupOf M).map f
  let : (Jhat ρ).Normal := Jhat_normal ρ
  obtain ⟨_,_,hPc,hPn,_,_,_,_,_,_⟩ := hd.ambient_marks (Jhat ρ) hp
  let : P.Normal := hPn
  have hRc := source_chosen_core_noncentral hG T hempty hM hJ hu hmany hV
  have hRne : R ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    apply hRc
    intro x hx
    let a : M := ⟨x,((pCoreIn_le 2 _).trans inf_le_left) hx⟩
    have hh : actionHom M V hV.normalized a = 1 :=
      congrArg Subtype.val (hk (show a ∈ ((M ⊓ Mc).pCoreIn 2).subgroupOf M from hx))
    have hc : a ∈ (actionHom M V hV.normalized).ker := hh
    rwa [actionHom_ker] at hc
  have hRtwo : IsPGroup 2 R := ((isPGroup_pCoreIn 2 (M ⊓ Mc)).comap_subtype).map f
  have hStwo : IsPGroup 2 S := T.isPGroup'.comap_subtype.map f
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    apply hMc.2
    intro z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  have hRT : (M ⊓ Mc).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow (M ⊓ Mc) (T.subtype (le_inf hM.1.2 hTMc))
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le (le_inf hM.1.2 hTMc)] using hh
  have hRS : R ≤ S := map_mono (comap_mono hRT)
  have hmove : ¬ R ≤ centralizer (P : Set (internalActionImage M V hV.normalized)) :=
    dihedral_prime_moves_twoGroup ρ (imageRepresentation_injective _ _ _)
      hV.quadratic_ratio l hp hd R hRtwo hRne
  have hM₀M : M₀ ≤ M := map_subtype_le _
  have hM₀image : (M₀.subgroupOf M).map f = Jhat ρ := by
    change ((((Jhat ρ).comap f).map M.subtype).subgroupOf M).map f = Jhat ρ
    rw [←comap_subtype,comap_map_eq_self_of_injective M.subtype_injective]
    exact map_comap_eq_self_of_surjective (show Function.Surjective f from
      (actionHom M V hV.normalized).rangeRestrict_surjective) (Jhat ρ)
  have hY₀image : ((twoResidualAmbient M₀).subgroupOf M).map f = P := by
    rw [←map_twoResidualAmbient_of_subgroup_image (M₀.subgroupOf M) M.subtype M₀
      (map_subgroupOf_eq_of_le hM₀M),←comap_subtype,
      comap_map_eq_self_of_injective M.subtype_injective,
      map_twoResidualAmbient_of_subgroup_image _ f _ hM₀image,residual_notation,
      ←l.kernel_eq_twoResidual]
  have hY₀M : twoResidualAmbient M₀ ≤ M :=
    (show twoResidualAmbient M₀ ≤ M₀ from map_subtype_le _).trans hM₀M
  have hOrbit : ((twoResidualAmbient M₀ ⊔ (T : Subgroup G)).subgroupOf M).map f = P ⊔ S := by
    rw [subgroupOf_sup hY₀M hM.1.2,Subgroup.map_sup,hY₀image]
  change ((caseIIResidual T M M₀ Mc).subgroupOf M).map f = P
  rw [source_caseIIResidual_image T hM.1.2 hM₀M f,hOrbit,residual_notation]
  apply prime_conjugateSpan_residual P S R _ _ hStwo hRS hmove
  · rw [hPc]
    rcases (primeDimensionOptions_iff p m).mp hp with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide
  · rw [hPc]
    rcases (primeDimensionOptions_iff p m).mp hp with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide

/-- Original15.2.3(1)(i) in the dihedral row, with the exact prime marking retained.
The source noncentrality, image and faithful-star premises are all discharged. -/
theorem source_dihedral_residual_prime_image
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (hD : SourceCases.Dihedral (imageRepresentation M V hV.normalized)) :
    let ρ := imageRepresentation M V hV.normalized
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    let Ybar := (Y.subgroupOf M).map (actionHom M V hV.normalized).rangeRestrict
    let Ystar := (Y.subgroupOf M).map (QuotientGroup.mk' (pCore 2 M))
    ∃ (l : LocalGeneration (ρ.comp (Jhat ρ).subtype)) (p m : ℕ),
      PrimeDimensionOptions p m ∧ DihedralMarking l p m ∧
      Ybar = (pResidual 2 (Jhat ρ)).map (Jhat ρ).subtype ∧
      Nat.card Ybar = p ∧ Nat.card Ystar = p ∧ Nonempty (Ybar ≃* Ystar) := by
  obtain ⟨l,p,m,hp,hd⟩ := hD
  have hprime : Nat.Prime p := by
    rcases (primeDimensionOptions_iff p m).mp hp with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide
  let : Fact p.Prime := ⟨hprime⟩
  have he := source_dihedral_caseIIResidual_image hG T hempty hM hJ hu hmany hV l hp hd
  have hc : Nat.card (((caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc).subgroupOf M).map
      (actionHom M V hV.normalized).rangeRestrict) = p := by
    exact (congrArg (fun K : Subgroup (internalActionImage M V hV.normalized) => Nat.card K) he).trans
      ((card_map_of_injective (Jhat (imageRepresentation M V hV.normalized)).subtype_injective).trans
        hd.card_kernel)
  have hs := (source_chosen_cyclic_star_card T hM.1.2 hu hV (isCyclic_of_prime_card hc)).trans hc
  refine ⟨l,p,m,hp,hd,?_,hc,hs,⟨mulEquivOfPrimeCardEq hc hs⟩⟩
  simpa only [l.kernel_eq_twoResidual] using he

end CFSG.Quasithin.Chapter15.Section02
