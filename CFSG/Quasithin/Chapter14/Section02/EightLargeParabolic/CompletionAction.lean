module
public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.CompletionStructure

/-!
# Faithful automorphisms of the actual triality completion

Conjugation embeds Mc join M, the full ambient normalizer, in the automorphism
group of H join P₂. The base maps exactly to the inner automorphisms, and its
preimage is exactly the base. Thus the already proved quotient of order dividing
three is the actual outer action, with no central kernel.

The common cubic supplement acts on the whole completion and restricts to the
previously constructed marked action on each endpoint. Both compatibility
equations use the original faithful completion maps. This extends the action to
the actual ambient completion; identification with the standard finite triality
completion remains to be proved by qt-e-14315-eight-borel-exclusion. The explicit
marked-realization input remains owned by qt-e-1427-eight-amalgam-recognition.

Source: Aschbacher--Smith 14.2.18--19, p.987; Definition F.4.3, p.274.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H : Subgroup G}
variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
include hG hempty hM hu hmany hcard e hH


/-- Conjugation on the actual original completion, defined on its full ambient normalizer. -/
def sourceCompletionAction (r : MarkedTriality T M Mc H) :
    (Mc ⊔ M : Subgroup G) →* MulAut (H ⊔ secondParabolic T M Mc H : Subgroup G) :=
  (H ⊔ secondParabolic T M Mc H).normalizerMonoidHom.comp
    (inclusion (source_generated_normalizer_eq hG hempty hM hu hmany hcard e hH r).ge)

theorem sourceCompletionAction_apply (r : MarkedTriality T M Mc H)
    (x : (Mc ⊔ M : Subgroup G)) (b : (H ⊔ secondParabolic T M Mc H : Subgroup G)) :
    (sourceCompletionAction hG hempty hM hu hmany hcard e hH r x b : G) =
      (x : G) * (b : G) * (x : G)⁻¹ := rfl

theorem sourceCompletionAction_injective (r : MarkedTriality T M Mc H) :
    Function.Injective (sourceCompletionAction hG hempty hM hu hmany hcard e hH r) := by
  have hi : Function.Injective (H ⊔ secondParabolic T M Mc H).normalizerMonoidHom := by
    rw [←MonoidHom.ker_eq_bot_iff,normalizerMonoidHom_ker,
      source_generated_centralizer_eq_bot hG hempty hM hu hmany hcard e hH r,bot_subgroupOf]
  exact hi.comp (inclusion_injective _)

theorem sourceCompletionAction_inner_image (r : MarkedTriality T M Mc H) :
    ((H ⊔ secondParabolic T M Mc H).subgroupOf (Mc ⊔ M)).map
      (sourceCompletionAction hG hempty hM hu hmany hcard e hH r) =
      MulAut.innerSubgroup (H ⊔ secondParabolic T M Mc H : Subgroup G) := by
  have hBJ : H ⊔ secondParabolic T M Mc H ≤ Mc ⊔ M := sup_le_sup
    (source_first_le_partner hG hempty hM hu hmany hcard e hH)
    (source_parabolics hG T hempty hM hu hmany hcard e H hH
      (firstResidualQuotientEquiv r)).2.2.2.2
  ext a
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,by ext b; rfl⟩
  · rintro ⟨b,rfl⟩
    exact ⟨inclusion hBJ b,b.property,by ext c; rfl⟩

theorem sourceCompletionAction_inner_preimage (r : MarkedTriality T M Mc H) :
    (MulAut.innerSubgroup (H ⊔ secondParabolic T M Mc H : Subgroup G)).comap
      (sourceCompletionAction hG hempty hM hu hmany hcard e hH r) =
      (H ⊔ secondParabolic T M Mc H).subgroupOf (Mc ⊔ M) := by
  rw [←sourceCompletionAction_inner_image hG hempty hM hu hmany hcard e hH r]
  exact comap_map_eq_self_of_injective
    (sourceCompletionAction_injective hG hempty hM hu hmany hcard e hH r) _

/-- The cubic action extends to the actual completion with its original left endpoint map. -/
theorem sourceCompletionAction_left (r : MarkedTriality T M Mc H)
    (A : Subgroup G) (hAJ : A ≤ Mc ⊔ M)
    (hAH : A ≤ normalizer (H : Set G))
    (hAP : A ≤ normalizer (secondParabolic T M Mc H : Set G))
    (a : A) (x : _root_.Triality.Standard.Parabolics.parabolic
      (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one) .arms) :
    sourceCompletionAction hG hempty hM hu hmany hcard e hH r (inclusion hAJ a)
      ((markedCompletion r).left x) =
        (markedCompletion r).left ((markedCubicAction r A hAH hAP a).left x) := by
  apply Subtype.ext
  have hx := congrArg r.left.symm (markedCubicAction_left r A hAH hAP a (r.left.symm x))
  simp only [MulEquiv.apply_symm_apply,MulEquiv.symm_apply_apply] at hx
  exact congrArg (fun y : H => (y : G)) hx.symm

/-- The same extension preserves the original right endpoint map. -/
theorem sourceCompletionAction_right (r : MarkedTriality T M Mc H)
    (A : Subgroup G) (hAJ : A ≤ Mc ⊔ M)
    (hAH : A ≤ normalizer (H : Set G))
    (hAP : A ≤ normalizer (secondParabolic T M Mc H : Set G))
    (a : A) (x : _root_.Triality.Standard.Parabolics.parabolic
      (_root_.Triality.Standard.binaryParameters 1 Nat.zero_lt_one) .central) :
    sourceCompletionAction hG hempty hM hu hmany hcard e hH r (inclusion hAJ a)
      ((markedCompletion r).right x) =
        (markedCompletion r).right ((markedCubicAction r A hAH hAP a).right x) := by
  apply Subtype.ext
  have hx := congrArg r.right.symm (markedCubicAction_right r A hAH hAP a (r.right.symm x))
  simp only [MulEquiv.apply_symm_apply,MulEquiv.symm_apply_apply] at hx
  exact congrArg (fun y : secondParabolic T M Mc H => (y : G)) hx.symm

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic
