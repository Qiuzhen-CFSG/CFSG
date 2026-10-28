module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.NormalizerAction.Definitions
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.NormalizerAction.PointwiseFixer

/-!
# Core center and residual centralizer in the full Hall--Janko automorphism group

A self-centralizing inner radical bounds the center of the full normalizer's
two-core by the already computed radical center. The entire radical lies
in the two-residual, whose cubic element has no nonidentity fixed point on
that center. Thus the residual has trivial full automorphism centralizer.

The checked full automorphism radical fixer discharges the containment, giving
both conclusions for the literal normalizer of the fixed inner radical.
No simplicity assumption or ambient local placement is needed.
Source: GLS3 Table 5.3g; Aschbacher--Smith 15.3.42, printed p.1138.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.NormalizerAction
open Theory.GroupTheory Subgroup GeneratorPair Seed PairNormalizer

/-- Self-centralization of the radical controls the whole local core center;
no equality between the full core and the inner radical is needed. -/
theorem core_center_card_le_of_radical_centralizer
    (hc : centralizer (innerRadical : Set (MulAut Carrier)) ≤ innerRadical) :
    Nat.card (center (fullNormalizer.pCoreIn 2)) ≤ 4 := by
  let R := fullNormalizer.pCoreIn 2
  have hz (z : center R) : (z.val : MulAut Carrier) ∈ centralizer (innerRadical : Set _) := by
    intro x hx
    exact congrArg Subtype.val
      (mem_center_iff.mp z.property ⟨x, innerRadical_le_core hx⟩)
  let f : center R → center innerRadical := fun z =>
    ⟨⟨z.val, hc (hz z)⟩, mem_center_iff.mpr (fun x =>
      Subtype.ext (hz z x x.property))⟩
  have hf : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : center innerRadical => (z.val : MulAut Carrier)) h
  exact (Nat.card_le_card_of_injective f hf).trans card_center_innerRadical_le

/-- The full residual's centralizer vanishes once the radical fixer is controlled. -/
theorem residual_centralizer_eq_bot_of_radical_centralizer
    (hc : centralizer (innerRadical : Set (MulAut Carrier)) ≤ innerRadical) :
    centralizer (fullResidual : Set (MulAut Carrier)) = ⊥ := by
  apply eq_bot_iff.mpr
  intro f hf
  have hq : f ∈ centralizer (innerRadical : Set (MulAut Carrier)) :=
    centralizer_le innerRadical_le_fullResidual hf
  obtain ⟨x, hx, rfl⟩ := hc hq
  have hz : (⟨x, hx⟩ : q₂) ∈ center q₂ := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply inner_conj_injective
    exact (map_mul MulAut.conj _ _).trans
      ((hq (MulAut.conj (y : Carrier)) (mem_map_of_mem MulAut.conj y.property)).trans
        (map_mul MulAut.conj _ _).symm)
  have ho : oddGenerator 0 * x = x * oddGenerator 0 := by
    apply inner_conj_injective
    exact (map_mul MulAut.conj _ _).trans
      ((hf (MulAut.conj (oddGenerator 0)) (odd_inner_mem_fullResidual 0)).trans
        (map_mul MulAut.conj _ _).symm)
  have hx1 : x = 1 := congrArg Subtype.val (center_fixed_eq_one ⟨x, hx⟩ hz ho)
  change MulAut.conj x = 1
  rw [hx1, map_one]

/-- The center of the actual full normalizer's two-core has at most four elements. -/
theorem core_center_card_le : Nat.card (center (fullNormalizer.pCoreIn 2)) ≤ 4 :=
  core_center_card_le_of_radical_centralizer radical_centralizer_le

/-- The actual full normalizer's two-residual has trivial automorphism centralizer. -/
theorem residual_centralizer_eq_bot :
    centralizer (fullResidual : Set (MulAut Carrier)) = ⊥ :=
  residual_centralizer_eq_bot_of_radical_centralizer radical_centralizer_le

end Sporadic.LeechRelated.J2.ExceptionalParabolics.NormalizerAction
