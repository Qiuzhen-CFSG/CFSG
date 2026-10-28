module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic.CoreAction
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondCoreActionLifting

/-!
# The original cubic reflection from the identified core action

Apply the central-kernel lifting theorem to the literal subgroup
`X = sourceResidual M Mc ⊔ T` and its original Sylow `T.subtype le_sup_right`.
The original even-characteristic hypothesis gives self-centralization of
`O₂(X)`. The resulting injective Sylow map is an equivalence with the same
original `T`, and its reflection satisfies the exact checked three-coset
table. The existing collection recognizer then identifies the original X.

The two concrete center facts and the identified core/action image remain
explicit inputs; the action census owner supplies them. No complement,
endpoint equivalence, or marked reflection is assumed.

Source: Aschbacher--Smith F.1.11--12, pp.262--264, and 14.2.20--21,
pp.988--989. The generator conventions are Parrott (1972), §5, p.683.
-/

@[expose] public section
noncomputable section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Tits.ExceptionalParabolics
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem marking_of_range (T : Sylow 2 G) (X : Subgroup G)
    (hTX : (T : Subgroup G) ≤ X) (j : S →* X) (hj : Function.Injective j)
    (hrange : j.range = (T : Subgroup G).subgroupOf X) :
    ∃ τ : S ≃* (T : Subgroup G), sylowMap T X hTX τ = j := by
  let τ := (MonoidHom.ofInjective hj).trans
    ((MulEquiv.subgroupCongr hrange).trans (subgroupOfEquivOfLe hTX))
  refine ⟨τ,?_⟩
  ext s
  rfl

/-- Reconstruct a reflection in the original cubic vertex from its actual
identified core action, keeping the original common Sylow. -/
theorem source_reflection_of_core_action
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
    (hZcard : Nat.card (center SecondCoreAction.Core) = 4)
    (hZcentralizer : centralizer ((center SecondCoreAction.Core).map
      (pCore 2 second).subtype : Set second) = pCore 2 second)
    (d : SecondCoreAction.Core ≃*
      pCore 2 (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G))
    (himage : (SecondCoreAction.through
      (pCore 2 (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G)) d).range =
      SecondCoreAction.model.range) :
    ∃ (τ : S ≃* (T : Subgroup G))
      (r : (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G)),
      (r : G) ∉ (T : Subgroup G) ∧
      Tits.AmalgamRigidity.SecondExtension.CosetRelations
        (SecondRecognition.generators
          (sylowMap T (sourceResidual M Mc ⊔ (T : Subgroup G)) le_sup_right τ) r) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  obtain ⟨_,hMX,_,_,_,_,_⟩ :=
    source_tits_first_second_data hG T hempty hM hu hmany hcard e H hH hi hfirst
  have hXM : X ≤ M := hMX.ge
  have hXH : X ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T le_sup_right hXM
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  have hc : centralizer (pCore 2 X : Set X) ≤ pCore 2 X :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hXH)
  obtain ⟨j,hj,hrange,r,hr,htable⟩ := SecondCoreActionLifting.exists_reflection
    hZcard hZcentralizer hc d himage (T.subtype le_sup_right)
  obtain ⟨τ,hτ⟩ := marking_of_range T X le_sup_right j hj hrange
  refine ⟨τ,r,hr,?_⟩
  rw [hτ]
  exact htable

/-- Apply the existing source recognizer to the reconstructed table on the
literal original subgroup. The only extra inputs are the concrete center
facts and the original core/action identification. -/
theorem source_second_of_core_action
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
    (hZcard : Nat.card (center SecondCoreAction.Core) = 4)
    (hZcentralizer : centralizer ((center SecondCoreAction.Core).map
      (pCore 2 second).subtype : Set second) = pCore 2 second)
    (d : SecondCoreAction.Core ≃*
      pCore 2 (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G))
    (himage : (SecondCoreAction.through
      (pCore 2 (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G)) d).range =
      SecondCoreAction.model.range) :
    Nonempty (second ≃* (sourceResidual M Mc ⊔ (T : Subgroup G) : Subgroup G)) := by
  obtain ⟨τ,r,hr,htable⟩ := source_reflection_of_core_action hG T hempty hM hu hmany
    hcard e H hH hi hfirst hZcard hZcentralizer d himage
  exact source_second_of_collection hG T hempty hM hu hmany hcard e H hH hi hfirst
    τ r hr htable

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticSecondParabolic
