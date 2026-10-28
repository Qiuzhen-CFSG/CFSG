module

public import CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound.Cases

/-!
# The marked action of the original LT

The normalizer-action hypothesis supplies an L-element with the same action
as every element of LT. Faithfulness of the marked SL₃(2) action makes its
image unique, hence gives a surjective homomorphism retaining the literal
conjugation equation on V. This transports the hyperplane stabilizer without
replacing either the original hyperplane or its Sylow subgroup.

Source: Aschbacher--Smith, 12.4.8, printed p.815.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G}

/-- The full LT action has exactly the original marked SL₃(2) image. -/
theorem Configuration.exists_marked_join_action (c : Configuration T L V U) :
    letI := c.chosen.elementary
    ∃ q : ↥(L ⊔ (T : Subgroup G)) →* BinaryLinearThree.Group,
      Function.Surjective q ∧ ∀ (n : ↥(L ⊔ (T : Subgroup G))) (v : Additive V),
        ((c.extension.action (q n) v).toMul : G) =
          (n : G) * (v.toMul : G) * (n : G)⁻¹ := by
  classical
  let _ := c.chosen.elementary
  let E := c.extension
  let A := L ⊔ (T : Subgroup G)
  have hTV := ((c.structural G T L c.hypothesis).2.2 V c.chosen).1
  have hAV : A ≤ normalizer (V : Set G) := sup_le c.chosen.normalizes hTV
  have hex (n : A) : ∃ b : BinaryLinearThree.Group, ∀ v : Additive V,
      ((E.action b v).toMul : G) = (n : G) * (v.toMul : G) * (n : G)⁻¹ := by
    obtain ⟨l,hl,he⟩ := c.normalizer_action n (hAV n.property)
    refine ⟨E.quotientEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩), ?_⟩
    intro v
    exact (E.conjugation ⟨l,hl⟩ v).trans (he v.toMul v.toMul.property).symm
  choose f hf using hex
  let q : A →* BinaryLinearThree.Group := {
    toFun := f
    map_one' := by
      apply action_injective E
      apply LinearMap.ext
      intro v
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [map_one]
      change ((E.action (f 1) v).toMul : G) = (v.toMul : G)
      rw [hf]
      simp
    map_mul' := by
      intro a b
      apply action_injective E
      apply LinearMap.ext
      intro v
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [map_mul,Module.End.mul_apply,hf,hf,hf]
      simp only [Subgroup.coe_mul]
      group }
  refine ⟨q, ?_, hf⟩
  intro b
  obtain ⟨l,hl⟩ := E.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) b
  refine ⟨⟨l,(le_sup_left : L ≤ A) l.property⟩, ?_⟩
  apply action_injective E
  apply LinearMap.ext
  intro v
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((E.action (f ⟨l,(le_sup_left : L ≤ A) l.property⟩) v).toMul : G) = ((E.action b v).toMul : G)
  rw [hf,←hl]
  exact (E.conjugation l v).symm
end CFSG.Quasithin.Chapter12.Section04.SLThreeCommutatorSource.CentralizerBound
