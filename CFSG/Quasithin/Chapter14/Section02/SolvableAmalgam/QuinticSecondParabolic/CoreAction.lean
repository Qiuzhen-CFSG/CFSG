module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic.Reduction
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreAction

/-!
# The original cubic vertex acts on the identified Tits core

The marked core equality gives an equivalence with the actual normal two-core
of the original subgroup X. Transporting its conjugation agrees on every
element of the original Sylow with the concrete Sylow action. Even
characteristic makes its kernel exactly the center of that core, so the
transported image is an overgroup of the concrete Sylow image with the exact
required order. No endpoint isomorphism or action-image classification is
assumed here.

Source: Aschbacher--Smith F.1.11--12, pp.262--264, and14.2.20--21,
pp.988--989. The finite action census and lifting from the action image
remain separate reconstruction obligations.
-/

@[expose] public section
noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Tits.ExceptionalParabolics
variable {G : Type*} [Group G]

/-- Identify the actual two-core, with its original Sylow inclusion retained. -/
def markedCoreEquiv (T : Sylow 2 G) (X : Subgroup G)
    (hTX : (T : Subgroup G) ≤ X) (σ : S ≃* (T : Subgroup G))
    (hcore : coreInMarkedSylow T X hTX σ = SecondRecognition.coreInSylow) :
    SecondCoreAction.Core ≃* pCore 2 X :=
  SecondCoreAction.sylowCoreEquiv.symm.trans
    ((MulEquiv.subgroupCongr hcore.symm).trans (coreEquiv T X hTX σ))

theorem markedCoreEquiv_val (T : Sylow 2 G) (X : Subgroup G)
    (hTX : (T : Subgroup G) ≤ X) (σ : S ≃* (T : Subgroup G))
    (hcore : coreInMarkedSylow T X hTX σ = SecondRecognition.coreInSylow)
    (q : SecondCoreAction.Core) :
    (markedCoreEquiv T X hTX σ hcore q : X) =
      sylowMap T X hTX σ (SecondCoreAction.sylowCoreEquiv.symm q).val := rfl

/-- Conjugation by X expressed on the concrete core, not a replacement action. -/
def markedCoreAction (T : Sylow 2 G) (X : Subgroup G)
    (hTX : (T : Subgroup G) ≤ X) (σ : S ≃* (T : Subgroup G))
    (hcore : coreInMarkedSylow T X hTX σ = SecondRecognition.coreInSylow) :
    X →* MulAut SecondCoreAction.Core :=
  SecondCoreAction.through (pCore 2 X) (markedCoreEquiv T X hTX σ hcore)

/-- Every original Sylow element has precisely the marked core action. -/
theorem markedCoreAction_sylow (T : Sylow 2 G) (X : Subgroup G)
    (hTX : (T : Subgroup G) ≤ X) (σ : S ≃* (T : Subgroup G))
    (hcore : coreInMarkedSylow T X hTX σ = SecondRecognition.coreInSylow)
    (s : S) :
    markedCoreAction T X hTX σ hcore (sylowMap T X hTX σ s) =
      SecondCoreAction.sylow s := by
  apply MulEquiv.ext
  intro q
  apply (markedCoreEquiv T X hTX σ hcore).injective
  apply Subtype.ext
  rw [markedCoreAction, SecondCoreAction.through_apply]
  rw [MulAut.conjNormal_apply, markedCoreEquiv_val, markedCoreEquiv_val,
    SecondCoreAction.sylow_apply, map_mul, map_mul, map_inv]

theorem sylowAction_le_markedCoreAction (T : Sylow 2 G) (X : Subgroup G)
    (hTX : (T : Subgroup G) ≤ X) (σ : S ≃* (T : Subgroup G))
    (hcore : coreInMarkedSylow T X hTX σ = SecondRecognition.coreInSylow) :
    SecondCoreAction.sylow.range ≤ (markedCoreAction T X hTX σ hcore).range := by
  rintro _ ⟨s,rfl⟩
  exact ⟨sylowMap T X hTX σ s,markedCoreAction_sylow T X hTX σ hcore s⟩

/-- The source supplies the genuine core action and its exact central kernel.
This is the source input to the finite action-overgroup census. -/
theorem source_core_action_input
    [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hfirst : Nonempty (Tits.ExceptionalParabolics.first ≃* H))
    (σ : S ≃* (T : Subgroup G))
    (hcore : coreInMarkedSylow T (sourceResidual M Mc ⊔ (T : Subgroup G))
      le_sup_right σ = SecondRecognition.coreInSylow) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let a := markedCoreAction T X le_sup_right σ hcore
    centralizer (pCore 2 X : Set X) ≤ pCore 2 X ∧
      a.ker = (center (pCore 2 X)).map (pCore 2 X).subtype ∧
      SecondCoreAction.sylow.range ≤ a.range ∧
      Nat.card (center SecondCoreAction.Core) * Nat.card a.range = 6144 := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  have hXM : X ≤ M := sup_le (sourceResidual_le _ _) hM.1.2
  have hXH : X ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T le_sup_right hXM
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  have hc : centralizer (pCore 2 X : Set X) ≤ pCore 2 X :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hXH)
  obtain ⟨_,_,_,_,hX,_,_⟩ :=
    source_tits_first_second_data hG T hempty hM hu hmany hcard e H hH hi hfirst
  exact ⟨hc,SecondCoreAction.through_ker_of_selfCentralizing _ _ hc,
    sylowAction_le_markedCoreAction T X le_sup_right σ hcore,
    (SecondCoreAction.through_card _ _ hc).trans hX⟩

/-- A finite census of action overgroups aligns the original action on the
original core. It does not identify X from its numerical data. The remaining
lifting theorem must retain the central kernel recorded here. -/
theorem source_core_action_alignment_of_census
    [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hfirst : Nonempty (Tits.ExceptionalParabolics.first ≃* H))
    (σ : S ≃* (T : Subgroup G))
    (hcore : coreInMarkedSylow T (sourceResidual M Mc ⊔ (T : Subgroup G))
      le_sup_right σ = SecondRecognition.coreInSylow)
    (hcensus : ∀ A : Subgroup (MulAut SecondCoreAction.Core),
      SecondCoreAction.sylow.range ≤ A →
      Nat.card (center SecondCoreAction.Core) * Nat.card A = 6144 →
      ∃ α : MulAut SecondCoreAction.Core,
        A.map (MulAut.congr α).toMonoidHom = SecondCoreAction.model.range) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    ∃ d : SecondCoreAction.Core ≃* pCore 2 X,
      (SecondCoreAction.through (pCore 2 X) d).range = SecondCoreAction.model.range ∧
      (SecondCoreAction.through (pCore 2 X) d).ker =
        (center (pCore 2 X)).map (pCore 2 X).subtype := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let d := markedCoreEquiv T X le_sup_right σ hcore
  obtain ⟨hc,_,hS,hcount⟩ := source_core_action_input hG T hempty hM hu hmany
    hcard e H hH hi hfirst σ hcore
  obtain ⟨α,hα⟩ := hcensus _ hS hcount
  refine ⟨α.symm.trans d,?_,SecondCoreAction.through_ker_of_selfCentralizing _ _ hc⟩
  rw [SecondCoreAction.through_range_recoordinate]
  exact hα

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic
