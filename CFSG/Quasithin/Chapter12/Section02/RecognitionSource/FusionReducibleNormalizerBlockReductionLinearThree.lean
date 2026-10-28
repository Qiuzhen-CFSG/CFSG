module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerModelBounds

/-!
# The reducible SL₃ block branch

Transport the marked extension's actual action on V to the chosen vector
space, then descend its given natural projection to V/C_V(L). The binary
natural cohomology and Sylow fixed-space bounds prove normalizer containment.
Thus the escaping hypothesis of the retained block-construction contract is
impossible. This discharges that contract without an MS classification or
an identification of V with the source omega-generated module.

Source: Aschbacher–Smith B.4.8(2), 3.3.23–24 and 12.2.16,
printed pp.91,598–599,800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource Section04.SmallFusion
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The extension marking is compatible with the literal chosen action. -/
def slThree_chosen_action_equiv (D : ChosenModule T L V) (E : SLThreeExtension D) :
    letI := D.elementary
    ActionEquiv D.quotientAction E.action := by
  let := D.elementary
  let a₀ : D.space ≃+ Additive V := {
    toFun := fun v => Additive.ofMul (D.spaceEquiv (Multiplicative.ofAdd v))
    invFun := fun v => (D.spaceEquiv.symm v.toMul).toAdd
    left_inv := fun v => congrArg Multiplicative.toAdd (D.spaceEquiv.symm_apply_apply _)
    right_inv := fun v => congrArg Additive.ofMul (D.spaceEquiv.apply_symm_apply v.toMul)
    map_add' := fun v w => congrArg Additive.ofMul (map_mul D.spaceEquiv
      (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)) }
  let a : D.space ≃ₗ[ZMod 2] Additive V := { a₀ with map_smul' := ZMod.map_smul a₀ }
  refine ⟨E.quotientEquiv,a,?_⟩
  intro q v
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [E.conjugation]
  change (D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l v)) : G) =
    (l : G) * D.spaceEquiv (Multiplicative.ofAdd v) * (l : G)⁻¹
  rw [D.spaceEquiv_apply,D.spaceEquiv_apply]
  rfl

/-- The marked SL₃ extension rules out an escaping Sylow normalizer. -/
theorem sylow_normalizer_le_of_slThree_extension
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple) (hnone : NoEscape L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) (E : SLThreeExtension D) :
    normalizer (T : Set G) ≤ normalizer (L : Set G) := by
  let := D.elementary
  let e := chosenCentralEquiv_of_cover D (slThree_chosen_action_equiv D E)
    E.projection E.surjective E.kernel
  exact sylow_normalizer_le_of_chosen_central_model h D structural hnone hne e
    BinaryLinearThree.natural_dual_H1_finrank.le
    BinaryLinearThree.card_sylow_natural_fixed_le_two

/-- The complete retained linear-three block-construction contract. -/
theorem linearThreeBlockConstruction : LinearThreeBlockConstruction T L V := by
  intro h D structural hnone hne hescape E
  exact (hescape (sylow_normalizer_le_of_slThree_extension h D structural hnone hne E)).elim

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
