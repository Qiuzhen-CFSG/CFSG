module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.Placement
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.PreliminaryActions.LocalContracts

/-!
# Assembling the preliminary component alternatives

The image-rank equality on U gives a trivial offender kernel, the supplement
V=U+C_V(A), and U=W. Equality of the literal local subrepresentations then
transports every action and marking to the specified moved section. Faithful
restriction identifies A with its actual quotient image; the Sylow and Klein
four conclusions are transported through that identification. The projection
argument proves A≤L in each required branch, using genuine B.7.2 invariance.
Case (IV) retains U with only its justified LA-action.

`preliminary_of_local_alternative` is the final assembly from `Prepared` and
`LocalAlternative`. These are still proof outputs to construct, not allowed
earlier-source assumptions and not a completed proof of B.5.9. Their construction
remains with the local preparation and representation-comparison producers.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.5.9, printed pp.107–108, before the final natural-module enlargement.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
open QuasisimpleSource
universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Faithful restriction identifies an original subgroup with its literal
image in LA/C_LA(U), retaining the quotient map on elements. -/
noncomputable def seedSubgroupEquiv {A L : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (X : Subgroup G) (hX : X ≤ L ⊔ A)
    (hf : Function.Injective ((seedSubrepresentation ρ hLA).toRepresentation.comp
      (Subgroup.inclusion hX))) :
    X ≃* (X.subgroupOf (L ⊔ A)).map (seedQuotientMap ρ hLA) := by
  let f := (seedQuotientMap ρ hLA).comp (Subgroup.inclusion hX)
  have hi : Function.Injective f := by
    intro x y he
    apply hf
    apply LinearMap.ext
    intro w
    exact congrArg (fun q => seedQuotientAction ρ hLA q w) he
  have hr : f.range = (X.subgroupOf (L ⊔ A)).map (seedQuotientMap ρ hLA) := by
    ext q
    constructor
    · rintro ⟨x,rfl⟩
      exact ⟨Subgroup.inclusion hX x,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx⟩,rfl⟩
  exact (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hr)

@[simp] theorem seedSubgroupEquiv_apply {A L : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (X : Subgroup G) (hX : X ≤ L ⊔ A)
    (hf : Function.Injective ((seedSubrepresentation ρ hLA).toRepresentation.comp
      (Subgroup.inclusion hX))) (x : X) :
    (seedSubgroupEquiv ρ hLA X hX hf x : SeedQuotient ρ hLA) =
      seedQuotientMap ρ hLA (Subgroup.inclusion hX x) := rfl

private theorem seedOffender_faithful {A L : Subgroup G} (hLA : ⁅L,A⁆ = L)
    (hk : subspaceKernel ρ (naturalSeedSpace ρ L A) A = ⊥) :
    Function.Injective ((seedSubrepresentation ρ hLA).toRepresentation.comp
      (Subgroup.inclusion (show A ≤ L ⊔ A from le_sup_right))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro a ha
  apply Subtype.ext
  apply hk.le
  refine ⟨a.property,fun v hv => ?_⟩
  exact congrArg Subtype.val (LinearMap.congr_fun (MonoidHom.mem_ker.mp ha) ⟨v,hv⟩)

variable [Finite G]

/-- On the doubled branch, image-rank equality gives U=W and the supplement;
the genuine Irr⁺ invariance and centralizer projections then give A≤L. -/
theorem preliminary_doubleThree_of_local {K : GroupClass.{u}} (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A) (hL : IsComponent G L)
    (hLA : ⁅L,A⁆ = L) (s : MovedSection ρ L) (p : Prepared ρ K hLA)
    (F : BinaryField) (ho : Odd F.degree)
    (hn : IsRepeatedLinearNatural (seedComponentAction ρ hLA) F 3 2)
    (hspan : naturalSeedSpace ρ L A ≤ sSup {I | IsIrrPlus ρ L I})
    (hi : InducesInner A L) (hd : Disjoint L (centralizer (L : Set G)))
    (he : SeedRankEquality ρ A L) : PreliminaryConclusion ρ A L s := by
  let := hyp.finite_module
  obtain ⟨_,hU,hs⟩ := seed_equality_of_image_rank ρ hyp.faithful hA hLA p.noncentral he
  let W : Subrepresentation (ρ.comp (L ⊔ A).subtype) :=
    ⟨s.space.toSubmodule, fun g _ hv => s.space.apply_mem_toSubmodule g hv⟩
  have hW : seedSubrepresentation ρ hLA = W := by
    apply Subrepresentation.ext
    exact hU.trans s.space_eq.symm
  have hnW : IsRepeatedLinearNatural (s.space.toRepresentation.comp L.subtype) F 3 2 := by
    unfold seedComponentAction at hn
    rw [hW] at hn
    exact hn
  have hsW : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤ := s.space_eq.symm ▸ hs
  have hspanW : s.space.toSubmodule ≤ sSup {I | IsIrrPlus ρ L I} := by
    rw [s.space_eq, ← hU]
    exact hspan
  exact .classified L (doubleThree_case_of_span ρ hyp.faithful hyp.twoCore hA hL hLA s
    F ho hnW hi hd hsW hspanW)

/-- The four-dimensional branch transports the actual quotient offender,
proves U=W, and applies the non-IV projection argument. -/
theorem preliminary_fourCover_of_local {K : GroupClass.{u}} (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A) (hL : IsComponent G L)
    (hLA : ⁅L,A⁆ = L) (s : MovedSection ρ L) (p : Prepared ρ K hLA)
    (hc : FourDimensionalCoverSource (seedComponentAction ρ hLA))
    (hk : Nonempty (seedOffenderImage ρ hLA ≃* Multiplicative (Fin 2 → ZMod 2)))
    (hI : IsIrrPlus ρ L (naturalSeedSpace ρ L A))
    (hi : InducesInner A L) (hd : Disjoint L (centralizer (L : Set G)))
    (he : SeedRankEquality ρ A L) : PreliminaryConclusion ρ A L s := by
  let := hyp.finite_module
  obtain ⟨hkU,hU,hs⟩ := seed_equality_of_image_rank ρ hyp.faithful hA hLA p.noncentral he
  let W : Subrepresentation (ρ.comp (L ⊔ A).subtype) :=
    ⟨s.space.toSubmodule, fun g _ hv => s.space.apply_mem_toSubmodule g hv⟩
  have hW : seedSubrepresentation ρ hLA = W := by
    apply Subrepresentation.ext
    exact hU.trans s.space_eq.symm
  have hcW : FourDimensionalCoverSource (s.space.toRepresentation.comp L.subtype) := by
    unfold seedComponentAction at hc
    rw [hW] at hc
    exact hc
  obtain ⟨ek⟩ := hk
  have hkA : Nonempty (A ≃* Multiplicative (Fin 2 → ZMod 2)) :=
    ⟨(seedSubgroupEquiv ρ hLA A le_sup_right (seedOffender_faithful ρ hLA hkU)).trans ek⟩
  have hsW : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤ := s.space_eq.symm ▸ hs
  have hIW : IsIrrPlus ρ L s.space.toSubmodule := by
    rw [s.space_eq, ← hU]
    exact hI
  exact .classified L (fourCover_case_of_irrPlus ρ hyp.faithful hyp.twoCore hA hL hLA s
    hcW hkA hi hd hsW hIW)

/-- The S₅ branch retains the marking of L and the original LA action. -/
theorem preliminary_symmetricFive_of_local {K : GroupClass.{u}} (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hLA : ⁅L,A⁆ = L) (s : MovedSection ρ L) (p : Prepared ρ K hLA)
    (action : MarkedActionEquiv (seedSubrepresentation ρ hLA).toRepresentation
      ⊤ (L.subgroupOf (L ⊔ A))
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))
    (hc : Nat.card (seedOffenderImage ρ hLA) = 2)
    (he : SeedRankEquality ρ A L) : PreliminaryConclusion ρ A L s := by
  let := hyp.finite_module
  obtain ⟨hkU,hU,hs⟩ := seed_equality_of_image_rank ρ hyp.faithful hA hLA p.noncentral he
  let W : Subrepresentation (ρ.comp (L ⊔ A).subtype) :=
    ⟨s.space.toSubmodule, fun g _ hv => s.space.apply_mem_toSubmodule g hv⟩
  have hW : seedSubrepresentation ρ hLA = W := by
    apply Subrepresentation.ext
    exact hU.trans s.space_eq.symm
  rw [hW] at action
  let eL := (Subgroup.subgroupOfEquivOfLe (show L ≤ L ⊔ A from le_sup_left)).symm
  let eH := (Subgroup.topEquiv : (⊤ : Subgroup (L ⊔ A : Subgroup G)) ≃* (L ⊔ A : Subgroup G)).symm
  let mark : MarkedActionEquiv s.space.toRepresentation (L ⊔ A) L
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)) := {
    action := {
      groupEquiv := eH.trans action.action.groupEquiv
      linearEquiv := action.action.linearEquiv
      intertwines := fun g v => action.action.intertwines (eH g) v }
    contained := le_sup_left
    subgroupEquiv := eL.trans action.subgroupEquiv
    compatible := fun l => action.compatible (eL l) }
  have hcard : Nat.card A = 2 :=
    (Nat.card_congr (seedSubgroupEquiv ρ hLA A le_sup_right
      (seedOffender_faithful ρ hLA hkU)).toEquiv).trans hc
  exact .classified (L ⊔ A) (.symmetricFive mark hcard (s.space_eq.symm ▸ hs))

/-- The L₂ branch transfers the actual Sylow image back to A≤L and uses
the literal central quotient of the supplied moved section. -/
theorem preliminary_linearTwo_of_local {K : GroupClass.{u}} (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A) (hL : IsComponent G L)
    (hLA : ⁅L,A⁆ = L) (s : MovedSection ρ L) (p : Prepared ρ K hLA)
    (F : BinaryField)
    (hn : IsLinearNatural (reducedAction (seedComponentAction ρ hLA)) F 2)
    (hI : IsIrrPlus ρ L (naturalSeedSpace ρ L A))
    (hT : ∃ T : Sylow 2 (seedComponentImage ρ hLA),
      seedOffenderImage ρ hLA = (T : Subgroup (seedComponentImage ρ hLA)).map
        (seedComponentImage ρ hLA).subtype)
    (hi : InducesInner A L) (hd : Disjoint L (centralizer (L : Set G)))
    (he : SeedRankEquality ρ A L) : PreliminaryConclusion ρ A L s := by
  let := hyp.finite_module
  obtain ⟨_,hU,hs⟩ := seed_equality_of_image_rank ρ hyp.faithful hA hLA p.noncentral he
  let W : Subrepresentation (ρ.comp (L ⊔ A).subtype) :=
    ⟨s.space.toSubmodule, fun g _ hv => s.space.apply_mem_toSubmodule g hv⟩
  have hW : seedSubrepresentation ρ hLA = W := by
    apply Subrepresentation.ext
    exact hU.trans s.space_eq.symm
  have hsW : s.space.toSubmodule ⊔ fixedSpace ρ A = ⊤ := s.space_eq.symm ▸ hs
  have hIW : IsIrrPlus ρ L s.space.toSubmodule := by
    rw [s.space_eq, ← hU]
    exact hI
  have hAL := minimalOffender_le_component_of_irrPlus ρ hyp.faithful hyp.twoCore
    hA hL hLA s hi hd hsW hIW
  have hnW : IsLinearNatural (s.action.comp L.subtype) F 2 := by
    unfold seedComponentAction at hn
    rw [hW] at hn
    let Z : Subrepresentation (s.space.toRepresentation.comp L.subtype) :=
      ⟨s.central.toSubmodule, fun l _ hv => s.central.apply_mem_toSubmodule l hv⟩
    have hZ : fixed (s.space.toRepresentation.comp L.subtype) = Z := by
      apply Subrepresentation.ext
      exact s.central_eq.symm
    change IsLinearNatural ((fixed (s.space.toRepresentation.comp L.subtype)).quotientRepresentation) F 2 at hn
    rw [hZ] at hn
    exact hn
  let eL : L ≃* seedComponentImage ρ hLA :=
    seedSubgroupEquiv ρ hLA L le_sup_left p.component_faithful
  obtain ⟨T,hT⟩ := hT
  have hAT : (A.subgroupOf L).map eL.toMonoidHom = (T : Subgroup _) := by
    apply Subgroup.map_injective (seedComponentImage ρ hLA).subtype_injective
    rw [← hT]
    ext q
    constructor
    · rintro ⟨_,⟨l,hl,rfl⟩,rfl⟩
      exact ⟨Subgroup.inclusion (show A ≤ L ⊔ A from le_sup_right) ⟨l,hl⟩,hl,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      let l : L := ⟨a,hAL ha⟩
      exact ⟨eL l,⟨l,ha,rfl⟩,rfl⟩
  let S : Sylow 2 L := T.mapSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  have hAS : A.subgroupOf L = (S : Subgroup L) := by
    change A.subgroupOf L = (T : Subgroup _).map eL.symm.toMonoidHom
    rw [← hAT, map_map]
    have hid : eL.symm.toMonoidHom.comp eL.toMonoidHom = MonoidHom.id L := by
      ext l
      exact congrArg Subtype.val (eL.symm_apply_apply l)
    rw [hid,map_id]
  have hSylow : ∃ S : Sylow 2 L, A = (S : Subgroup L).map L.subtype := by
    refine ⟨S, ?_⟩
    rw [← hAS, map_subgroupOf_eq_of_le hAL]
  exact .classified L (.linearTwo F hnW hSylow hsW)

/-- Final assembly of the preliminary conclusion from the two separately
specified outputs. Neither output is an earlier-source input; their producers
must construct them from B.5.3 and the permitted earlier implications. -/
theorem preliminary_of_local_alternative {K : GroupClass.{u}} (hyp : FFHypothesis K ρ)
    {A L : Subgroup G} (hA : IsMinimalBestOffender ρ A) (hL : IsComponent G L)
    (hLA : ⁅L,A⁆ = L) (s : MovedSection ρ L) (p : Prepared ρ K hLA)
    (cases : LocalAlternative ρ hLA) : PreliminaryConclusion ρ A L s := by
  cases cases with
  | linearTwo F hn hI hT hi hd he =>
    exact preliminary_linearTwo_of_local ρ hyp hA hL hLA s p F hn hI hT hi hd he
  | symmetricFive action hc he =>
    exact preliminary_symmetricFive_of_local ρ hyp hA hLA s p action hc he
  | doubleThree F ho hn hspan hi hd he =>
    exact preliminary_doubleThree_of_local ρ hyp hA hL hLA s p F ho hn hspan hi hd he
  | naturalThree F ho hn hi =>
    exact naturalSeed_of_localNatural ρ hLA F ho hn hi s
  | fourCover hc hk hI hi hd he =>
    exact preliminary_fourCover_of_local ρ hyp hA hL hLA s p hc hk hI hi hd he
end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.PreliminaryActions
